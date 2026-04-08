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
lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Util_ParamMinimizer_Status_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Util_ParamMinimizer_Status_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Util_ParamMinimizer_Status_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg(lean_object* v_missing_28_){
_start:
{
lean_inc(v_missing_28_);
return v_missing_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg___boxed(lean_object* v_missing_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg(v_missing_29_);
lean_dec(v_missing_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_missing_34_){
_start:
{
lean_inc(v_missing_34_);
return v_missing_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_missing_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Util_ParamMinimizer_Status_missing_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_missing_38_);
lean_dec(v_missing_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg(lean_object* v_approx_41_){
_start:
{
lean_inc(v_approx_41_);
return v_approx_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg___boxed(lean_object* v_approx_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg(v_approx_42_);
lean_dec(v_approx_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_approx_47_){
_start:
{
lean_inc(v_approx_47_);
return v_approx_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_approx_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Util_ParamMinimizer_Status_approx_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_approx_51_);
lean_dec(v_approx_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg(lean_object* v_precise_54_){
_start:
{
lean_inc(v_precise_54_);
return v_precise_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg___boxed(lean_object* v_precise_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg(v_precise_55_);
lean_dec(v_precise_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_precise_60_){
_start:
{
lean_inc(v_precise_60_);
return v_precise_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_precise_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Util_ParamMinimizer_Status_precise_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_precise_64_);
lean_dec(v_precise_64_);
return v_res_66_;
}
}
static uint8_t _init_l_Lean_Util_ParamMinimizer_instInhabitedStatus_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_Lean_Util_ParamMinimizer_instInhabitedStatus(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
static lean_object* _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(2u);
v___x_79_ = lean_nat_to_int(v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr(uint8_t v_x_82_, lean_object* v_prec_83_){
_start:
{
lean_object* v___y_85_; lean_object* v___y_92_; lean_object* v___y_99_; 
switch(v_x_82_)
{
case 0:
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1024u);
v___x_106_ = lean_nat_dec_le(v___x_105_, v_prec_83_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6);
v___y_85_ = v___x_107_;
goto v___jp_84_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7);
v___y_85_ = v___x_108_;
goto v___jp_84_;
}
}
case 1:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(1024u);
v___x_110_ = lean_nat_dec_le(v___x_109_, v_prec_83_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6);
v___y_92_ = v___x_111_;
goto v___jp_91_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7);
v___y_92_ = v___x_112_;
goto v___jp_91_;
}
}
default: 
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(1024u);
v___x_114_ = lean_nat_dec_le(v___x_113_, v_prec_83_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6);
v___y_99_ = v___x_115_;
goto v___jp_98_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7);
v___y_99_ = v___x_116_;
goto v___jp_98_;
}
}
}
v___jp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__1));
lean_inc(v___y_85_);
v___x_87_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_87_, 0, v___y_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = 0;
v___x_89_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_88_);
v___x_90_ = l_Repr_addAppParen(v___x_89_, v_prec_83_);
return v___x_90_;
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_93_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__3));
lean_inc(v___y_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___y_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = 0;
v___x_96_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_95_);
v___x_97_ = l_Repr_addAppParen(v___x_96_, v_prec_83_);
return v___x_97_;
}
v___jp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_100_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__5));
lean_inc(v___y_99_);
v___x_101_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_101_, 0, v___y_99_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = 0;
v___x_103_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*1, v___x_102_);
v___x_104_ = l_Repr_addAppParen(v___x_103_, v_prec_83_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr___boxed(lean_object* v_x_117_, lean_object* v_prec_118_){
_start:
{
uint8_t v_x_177__boxed_119_; lean_object* v_res_120_; 
v_x_177__boxed_119_ = lean_unbox(v_x_117_);
v_res_120_ = l_Lean_Util_ParamMinimizer_instReprStatus_repr(v_x_177__boxed_119_, v_prec_118_);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0(lean_object* v_toPure_350_, uint8_t v___x_351_, lean_object* v_____x_352_){
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
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0___boxed(lean_object* v_toPure_391_, lean_object* v___x_392_, lean_object* v_____x_393_){
_start:
{
uint8_t v___x_7305__boxed_394_; lean_object* v_res_395_; 
v___x_7305__boxed_394_ = lean_unbox(v___x_392_);
v_res_395_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0(v_toPure_391_, v___x_7305__boxed_394_, v_____x_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__1(lean_object* v_toPure_396_, lean_object* v_inst_397_, lean_object* v_toBind_398_, lean_object* v___f_399_, lean_object* v_____x_400_){
_start:
{
lean_object* v_fst_401_; 
v_fst_401_ = lean_ctor_get(v_____x_400_, 0);
if (lean_obj_tag(v_fst_401_) == 0)
{
lean_object* v___x_402_; 
lean_dec(v___f_399_);
lean_dec(v_toBind_398_);
lean_dec_ref(v_inst_397_);
v___x_402_ = lean_apply_2(v_toPure_396_, lean_box(0), v_____x_400_);
return v___x_402_;
}
else
{
lean_object* v_a_403_; uint8_t v___x_404_; 
v_a_403_ = lean_ctor_get(v_fst_401_, 0);
v___x_404_ = lean_unbox(v_a_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_dec(v___f_399_);
lean_dec(v_toBind_398_);
lean_dec_ref(v_inst_397_);
v___x_405_ = lean_apply_2(v_toPure_396_, lean_box(0), v_____x_400_);
return v___x_405_;
}
else
{
lean_object* v_snd_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec(v_toPure_396_);
v_snd_406_ = lean_ctor_get(v_____x_400_, 1);
lean_inc(v_snd_406_);
lean_dec_ref(v_____x_400_);
v___x_407_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(v_inst_397_, v_snd_406_);
v___x_408_ = lean_apply_4(v_toBind_398_, lean_box(0), lean_box(0), v___x_407_, v___f_399_);
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__2(lean_object* v_toPure_409_, lean_object* v_____x_410_){
_start:
{
lean_object* v_fst_411_; lean_object* v_snd_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_421_; 
v_fst_411_ = lean_ctor_get(v_____x_410_, 0);
v_snd_412_ = lean_ctor_get(v_____x_410_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v_____x_410_);
if (v_isSharedCheck_421_ == 0)
{
v___x_414_ = v_____x_410_;
v_isShared_415_ = v_isSharedCheck_421_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_snd_412_);
lean_inc(v_fst_411_);
lean_dec(v_____x_410_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_421_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v_fst_411_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_416_);
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_snd_412_);
v___x_418_ = v_reuseFailAlloc_420_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; 
v___x_419_ = lean_apply_2(v_toPure_409_, lean_box(0), v___x_418_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3(lean_object* v_snd_422_, lean_object* v_toPure_423_, uint8_t v_a_424_){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_box(v_a_424_);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v_snd_422_);
v___x_427_ = lean_apply_2(v_toPure_423_, lean_box(0), v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3___boxed(lean_object* v_snd_428_, lean_object* v_toPure_429_, lean_object* v_a_430_){
_start:
{
uint8_t v_a_boxed_431_; lean_object* v_res_432_; 
v_a_boxed_431_ = lean_unbox(v_a_430_);
v_res_432_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3(v_snd_428_, v_toPure_429_, v_a_boxed_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__4(lean_object* v_toPure_433_, lean_object* v_a_434_, lean_object* v_toBind_435_, lean_object* v___f_436_, lean_object* v_____x_437_){
_start:
{
lean_object* v_fst_438_; 
v_fst_438_ = lean_ctor_get(v_____x_437_, 0);
lean_inc(v_fst_438_);
if (lean_obj_tag(v_fst_438_) == 0)
{
lean_object* v_snd_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_455_; 
lean_dec(v___f_436_);
lean_dec(v_toBind_435_);
lean_dec_ref(v_a_434_);
v_snd_439_ = lean_ctor_get(v_____x_437_, 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v_____x_437_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; 
v_unused_456_ = lean_ctor_get(v_____x_437_, 0);
lean_dec(v_unused_456_);
v___x_441_ = v_____x_437_;
v_isShared_442_ = v_isSharedCheck_455_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_snd_439_);
lean_dec(v_____x_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_455_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_454_; 
v_a_443_ = lean_ctor_get(v_fst_438_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v_fst_438_);
if (v_isSharedCheck_454_ == 0)
{
v___x_445_ = v_fst_438_;
v_isShared_446_ = v_isSharedCheck_454_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v_fst_438_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_454_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_453_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_450_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_448_);
v___x_450_ = v___x_441_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_snd_439_);
v___x_450_ = v_reuseFailAlloc_452_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; 
v___x_451_ = lean_apply_2(v_toPure_433_, lean_box(0), v___x_450_);
return v___x_451_;
}
}
}
}
}
else
{
lean_object* v_a_457_; lean_object* v_snd_458_; lean_object* v_test_459_; lean_object* v_cur_460_; lean_object* v___x_461_; lean_object* v___f_462_; lean_object* v___f_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_a_457_ = lean_ctor_get(v_fst_438_, 0);
lean_inc(v_a_457_);
lean_dec_ref(v_fst_438_);
v_snd_458_ = lean_ctor_get(v_____x_437_, 1);
lean_inc(v_snd_458_);
lean_dec_ref(v_____x_437_);
v_test_459_ = lean_ctor_get(v_a_434_, 1);
lean_inc(v_test_459_);
lean_dec_ref(v_a_434_);
v_cur_460_ = lean_ctor_get(v_a_457_, 0);
lean_inc_ref(v_cur_460_);
lean_dec(v_a_457_);
v___x_461_ = lean_apply_1(v_test_459_, v_cur_460_);
lean_inc(v_toPure_433_);
v___f_462_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__2), 2, 1);
lean_closure_set(v___f_462_, 0, v_toPure_433_);
v___f_463_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_463_, 0, v_snd_458_);
lean_closure_set(v___f_463_, 1, v_toPure_433_);
lean_inc_n(v_toBind_435_, 2);
v___x_464_ = lean_apply_4(v_toBind_435_, lean_box(0), lean_box(0), v___x_461_, v___f_463_);
v___x_465_ = lean_apply_4(v_toBind_435_, lean_box(0), lean_box(0), v___x_464_, v___f_462_);
v___x_466_ = lean_apply_4(v_toBind_435_, lean_box(0), lean_box(0), v___x_465_, v___f_436_);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5(lean_object* v_toPure_467_, lean_object* v_____x_468_){
_start:
{
lean_object* v_fst_469_; lean_object* v_snd_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_479_; 
v_fst_469_ = lean_ctor_get(v_____x_468_, 0);
v_snd_470_ = lean_ctor_get(v_____x_468_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_____x_468_);
if (v_isSharedCheck_479_ == 0)
{
v___x_472_ = v_____x_468_;
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_snd_470_);
lean_inc(v_fst_469_);
lean_dec(v_____x_468_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_474_, 0, v_fst_469_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_474_);
v___x_476_ = v___x_472_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_snd_470_);
v___x_476_ = v_reuseFailAlloc_478_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_477_; 
v___x_477_ = lean_apply_2(v_toPure_467_, lean_box(0), v___x_476_);
return v___x_477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__6(lean_object* v_toPure_480_, lean_object* v_toBind_481_, lean_object* v___f_482_, lean_object* v_____x_483_){
_start:
{
lean_object* v_fst_484_; 
v_fst_484_ = lean_ctor_get(v_____x_483_, 0);
lean_inc(v_fst_484_);
if (lean_obj_tag(v_fst_484_) == 0)
{
lean_object* v_snd_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_501_; 
lean_dec(v___f_482_);
lean_dec(v_toBind_481_);
v_snd_485_ = lean_ctor_get(v_____x_483_, 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v_____x_483_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; 
v_unused_502_ = lean_ctor_get(v_____x_483_, 0);
lean_dec(v_unused_502_);
v___x_487_ = v_____x_483_;
v_isShared_488_ = v_isSharedCheck_501_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_snd_485_);
lean_dec(v_____x_483_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_501_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_500_; 
v_a_489_ = lean_ctor_get(v_fst_484_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v_fst_484_);
if (v_isSharedCheck_500_ == 0)
{
v___x_491_ = v_fst_484_;
v_isShared_492_ = v_isSharedCheck_500_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v_fst_484_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_500_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_499_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_496_; 
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_494_);
v___x_496_ = v___x_487_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_snd_485_);
v___x_496_ = v_reuseFailAlloc_498_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_497_; 
v___x_497_ = lean_apply_2(v_toPure_480_, lean_box(0), v___x_496_);
return v___x_497_;
}
}
}
}
}
else
{
lean_object* v_snd_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_516_; 
v_snd_503_ = lean_ctor_get(v_____x_483_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_____x_483_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v_____x_483_, 0);
lean_dec(v_unused_517_);
v___x_505_ = v_____x_483_;
v_isShared_506_ = v_isSharedCheck_516_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_snd_503_);
lean_dec(v_____x_483_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_516_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v_a_507_; lean_object* v___f_508_; lean_object* v___f_509_; lean_object* v___x_511_; 
v_a_507_ = lean_ctor_get(v_fst_484_, 0);
lean_inc(v_a_507_);
lean_dec_ref(v_fst_484_);
lean_inc(v_toBind_481_);
lean_inc_n(v_toPure_480_, 2);
v___f_508_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__4), 5, 4);
lean_closure_set(v___f_508_, 0, v_toPure_480_);
lean_closure_set(v___f_508_, 1, v_a_507_);
lean_closure_set(v___f_508_, 2, v_toBind_481_);
lean_closure_set(v___f_508_, 3, v___f_482_);
v___f_509_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_509_, 0, v_toPure_480_);
lean_inc(v_snd_503_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v_snd_503_);
v___x_511_ = v___x_505_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_snd_503_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_snd_503_);
v___x_511_ = v_reuseFailAlloc_515_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_apply_2(v_toPure_480_, lean_box(0), v___x_511_);
lean_inc(v_toBind_481_);
v___x_513_ = lean_apply_4(v_toBind_481_, lean_box(0), lean_box(0), v___x_512_, v___f_509_);
v___x_514_ = lean_apply_4(v_toBind_481_, lean_box(0), lean_box(0), v___x_513_, v___f_508_);
return v___x_514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7(lean_object* v_toPure_518_, lean_object* v_a_519_, lean_object* v_toBind_520_, lean_object* v___f_521_, lean_object* v_____x_522_){
_start:
{
lean_object* v_fst_523_; 
v_fst_523_ = lean_ctor_get(v_____x_522_, 0);
lean_inc(v_fst_523_);
if (lean_obj_tag(v_fst_523_) == 0)
{
lean_object* v_snd_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_540_; 
lean_dec(v___f_521_);
lean_dec(v_toBind_520_);
v_snd_524_ = lean_ctor_get(v_____x_522_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_____x_522_);
if (v_isSharedCheck_540_ == 0)
{
lean_object* v_unused_541_; 
v_unused_541_ = lean_ctor_get(v_____x_522_, 0);
lean_dec(v_unused_541_);
v___x_526_ = v_____x_522_;
v_isShared_527_ = v_isSharedCheck_540_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_snd_524_);
lean_dec(v_____x_522_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_540_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_539_; 
v_a_528_ = lean_ctor_get(v_fst_523_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v_fst_523_);
if (v_isSharedCheck_539_ == 0)
{
v___x_530_ = v_fst_523_;
v_isShared_531_ = v_isSharedCheck_539_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v_fst_523_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_539_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_538_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_535_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_533_);
v___x_535_ = v___x_526_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_snd_524_);
v___x_535_ = v_reuseFailAlloc_537_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; 
v___x_536_ = lean_apply_2(v_toPure_518_, lean_box(0), v___x_535_);
return v___x_536_;
}
}
}
}
}
else
{
lean_object* v_snd_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_559_; 
v_snd_542_ = lean_ctor_get(v_____x_522_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_____x_522_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v_____x_522_, 0);
lean_dec(v_unused_560_);
v___x_544_ = v_____x_522_;
v_isShared_545_ = v_isSharedCheck_559_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_snd_542_);
lean_dec(v_____x_522_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_559_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_557_; 
v_isSharedCheck_557_ = !lean_is_exclusive(v_fst_523_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; 
v_unused_558_ = lean_ctor_get(v_fst_523_, 0);
lean_dec(v_unused_558_);
v___x_547_ = v_fst_523_;
v_isShared_548_ = v_isSharedCheck_557_;
goto v_resetjp_546_;
}
else
{
lean_dec(v_fst_523_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_557_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
lean_inc_ref(v_a_519_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v_a_519_);
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_519_);
v___x_550_ = v_reuseFailAlloc_556_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_552_; 
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_550_);
v___x_552_ = v___x_544_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_snd_542_);
v___x_552_ = v_reuseFailAlloc_555_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_apply_2(v_toPure_518_, lean_box(0), v___x_552_);
v___x_554_ = lean_apply_4(v_toBind_520_, lean_box(0), lean_box(0), v___x_553_, v___f_521_);
return v___x_554_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7___boxed(lean_object* v_toPure_561_, lean_object* v_a_562_, lean_object* v_toBind_563_, lean_object* v___f_564_, lean_object* v_____x_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7(v_toPure_561_, v_a_562_, v_toBind_563_, v___f_564_, v_____x_565_);
lean_dec_ref(v_a_562_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(lean_object* v_toPure_569_, lean_object* v_inst_570_, lean_object* v_toBind_571_, lean_object* v_a_572_, lean_object* v_maxCalls_573_, lean_object* v_____x_574_){
_start:
{
lean_object* v_fst_575_; lean_object* v_snd_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_629_; 
v_fst_575_ = lean_ctor_get(v_____x_574_, 0);
v_snd_576_ = lean_ctor_get(v_____x_574_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_____x_574_);
if (v_isSharedCheck_629_ == 0)
{
v___x_578_ = v_____x_574_;
v_isShared_579_ = v_isSharedCheck_629_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_snd_576_);
lean_inc(v_fst_575_);
lean_dec(v_____x_574_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_629_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
uint8_t v___y_581_; 
if (lean_obj_tag(v_fst_575_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_623_; 
lean_del_object(v___x_578_);
lean_dec(v_toBind_571_);
lean_dec_ref(v_inst_570_);
v_a_614_ = lean_ctor_get(v_fst_575_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v_fst_575_);
if (v_isSharedCheck_623_ == 0)
{
v___x_616_ = v_fst_575_;
v_isShared_617_ = v_isSharedCheck_623_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v_fst_575_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_623_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_622_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v_snd_576_);
v___x_621_ = lean_apply_2(v_toPure_569_, lean_box(0), v___x_620_);
return v___x_621_;
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_a_624_ = lean_ctor_get(v_fst_575_, 0);
lean_inc(v_a_624_);
lean_dec_ref(v_fst_575_);
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = lean_nat_dec_lt(v___x_625_, v_maxCalls_573_);
if (v___x_626_ == 0)
{
lean_dec(v_a_624_);
v___y_581_ = v___x_626_;
goto v___jp_580_;
}
else
{
lean_object* v_numCalls_627_; uint8_t v___x_628_; 
v_numCalls_627_ = lean_ctor_get(v_a_624_, 2);
lean_inc(v_numCalls_627_);
lean_dec(v_a_624_);
v___x_628_ = lean_nat_dec_le(v_maxCalls_573_, v_numCalls_627_);
lean_dec(v_numCalls_627_);
v___y_581_ = v___x_628_;
goto v___jp_580_;
}
}
v___jp_580_:
{
if (v___y_581_ == 0)
{
lean_object* v_cur_582_; lean_object* v_added_583_; lean_object* v_numCalls_584_; uint8_t v_found_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_608_; 
v_cur_582_ = lean_ctor_get(v_snd_576_, 0);
v_added_583_ = lean_ctor_get(v_snd_576_, 1);
v_numCalls_584_ = lean_ctor_get(v_snd_576_, 2);
v_found_585_ = lean_ctor_get_uint8(v_snd_576_, sizeof(void*)*3);
v_isSharedCheck_608_ = !lean_is_exclusive(v_snd_576_);
if (v_isSharedCheck_608_ == 0)
{
v___x_587_ = v_snd_576_;
v_isShared_588_ = v_isSharedCheck_608_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_numCalls_584_);
lean_inc(v_added_583_);
lean_inc(v_cur_582_);
lean_dec(v_snd_576_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_608_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___f_591_; lean_object* v___f_592_; lean_object* v___f_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_589_ = 1;
v___x_590_ = lean_box(v___x_589_);
lean_inc_n(v_toPure_569_, 5);
v___f_591_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_591_, 0, v_toPure_569_);
lean_closure_set(v___f_591_, 1, v___x_590_);
lean_inc_n(v_toBind_571_, 3);
v___f_592_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__1), 5, 4);
lean_closure_set(v___f_592_, 0, v_toPure_569_);
lean_closure_set(v___f_592_, 1, v_inst_570_);
lean_closure_set(v___f_592_, 2, v_toBind_571_);
lean_closure_set(v___f_592_, 3, v___f_591_);
v___f_593_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__6), 4, 3);
lean_closure_set(v___f_593_, 0, v_toPure_569_);
lean_closure_set(v___f_593_, 1, v_toBind_571_);
lean_closure_set(v___f_593_, 2, v___f_592_);
lean_inc_ref(v_a_572_);
v___f_594_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7___boxed), 5, 4);
lean_closure_set(v___f_594_, 0, v_toPure_569_);
lean_closure_set(v___f_594_, 1, v_a_572_);
lean_closure_set(v___f_594_, 2, v_toBind_571_);
lean_closure_set(v___f_594_, 3, v___f_593_);
v___f_595_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_595_, 0, v_toPure_569_);
v___x_596_ = lean_box(0);
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = lean_nat_add(v_numCalls_584_, v___x_597_);
lean_dec(v_numCalls_584_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 2, v___x_598_);
v___x_600_ = v___x_587_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_cur_582_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_added_583_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v___x_598_);
lean_ctor_set_uint8(v_reuseFailAlloc_607_, sizeof(void*)*3, v_found_585_);
v___x_600_ = v_reuseFailAlloc_607_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_602_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 1, v___x_600_);
lean_ctor_set(v___x_578_, 0, v___x_596_);
v___x_602_ = v___x_578_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v___x_600_);
v___x_602_ = v_reuseFailAlloc_606_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_apply_2(v_toPure_569_, lean_box(0), v___x_602_);
lean_inc(v_toBind_571_);
v___x_604_ = lean_apply_4(v_toBind_571_, lean_box(0), lean_box(0), v___x_603_, v___f_595_);
v___x_605_ = lean_apply_4(v_toBind_571_, lean_box(0), lean_box(0), v___x_604_, v___f_594_);
return v___x_605_;
}
}
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_611_; 
lean_dec(v_toBind_571_);
lean_dec_ref(v_inst_570_);
v___x_609_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0));
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_609_);
v___x_611_ = v___x_578_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_snd_576_);
v___x_611_ = v_reuseFailAlloc_613_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; 
v___x_612_ = lean_apply_2(v_toPure_569_, lean_box(0), v___x_611_);
return v___x_612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed(lean_object* v_toPure_630_, lean_object* v_inst_631_, lean_object* v_toBind_632_, lean_object* v_a_633_, lean_object* v_maxCalls_634_, lean_object* v_____x_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(v_toPure_630_, v_inst_631_, v_toBind_632_, v_a_633_, v_maxCalls_634_, v_____x_635_);
lean_dec(v_maxCalls_634_);
lean_dec_ref(v_a_633_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(lean_object* v_toPure_637_, lean_object* v_inst_638_, lean_object* v_toBind_639_, lean_object* v_a_640_, lean_object* v_____x_641_){
_start:
{
lean_object* v_fst_642_; 
v_fst_642_ = lean_ctor_get(v_____x_641_, 0);
lean_inc(v_fst_642_);
if (lean_obj_tag(v_fst_642_) == 0)
{
lean_object* v_snd_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_toBind_639_);
lean_dec_ref(v_inst_638_);
v_snd_643_ = lean_ctor_get(v_____x_641_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v_____x_641_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v_____x_641_, 0);
lean_dec(v_unused_660_);
v___x_645_ = v_____x_641_;
v_isShared_646_ = v_isSharedCheck_659_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_snd_643_);
lean_dec(v_____x_641_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_659_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_658_; 
v_a_647_ = lean_ctor_get(v_fst_642_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v_fst_642_);
if (v_isSharedCheck_658_ == 0)
{
v___x_649_ = v_fst_642_;
v_isShared_650_ = v_isSharedCheck_658_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v_fst_642_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_658_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_657_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_654_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_652_);
v___x_654_ = v___x_645_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_snd_643_);
v___x_654_ = v_reuseFailAlloc_656_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; 
v___x_655_ = lean_apply_2(v_toPure_637_, lean_box(0), v___x_654_);
return v___x_655_;
}
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v_snd_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_675_; 
v_a_661_ = lean_ctor_get(v_fst_642_, 0);
lean_inc(v_a_661_);
lean_dec_ref(v_fst_642_);
v_snd_662_ = lean_ctor_get(v_____x_641_, 1);
v_isSharedCheck_675_ = !lean_is_exclusive(v_____x_641_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; 
v_unused_676_ = lean_ctor_get(v_____x_641_, 0);
lean_dec(v_unused_676_);
v___x_664_ = v_____x_641_;
v_isShared_665_ = v_isSharedCheck_675_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_snd_662_);
lean_dec(v_____x_641_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_675_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v_maxCalls_666_; lean_object* v___f_667_; lean_object* v___f_668_; lean_object* v___x_670_; 
v_maxCalls_666_ = lean_ctor_get(v_a_661_, 2);
lean_inc(v_maxCalls_666_);
lean_dec(v_a_661_);
lean_inc_ref(v_a_640_);
lean_inc(v_toBind_639_);
lean_inc_n(v_toPure_637_, 2);
v___f_667_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_667_, 0, v_toPure_637_);
lean_closure_set(v___f_667_, 1, v_inst_638_);
lean_closure_set(v___f_667_, 2, v_toBind_639_);
lean_closure_set(v___f_667_, 3, v_a_640_);
lean_closure_set(v___f_667_, 4, v_maxCalls_666_);
v___f_668_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_668_, 0, v_toPure_637_);
lean_inc(v_snd_662_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v_snd_662_);
v___x_670_ = v___x_664_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_snd_662_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_snd_662_);
v___x_670_ = v_reuseFailAlloc_674_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = lean_apply_2(v_toPure_637_, lean_box(0), v___x_670_);
lean_inc(v_toBind_639_);
v___x_672_ = lean_apply_4(v_toBind_639_, lean_box(0), lean_box(0), v___x_671_, v___f_668_);
v___x_673_ = lean_apply_4(v_toBind_639_, lean_box(0), lean_box(0), v___x_672_, v___f_667_);
return v___x_673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10___boxed(lean_object* v_toPure_677_, lean_object* v_inst_678_, lean_object* v_toBind_679_, lean_object* v_a_680_, lean_object* v_____x_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(v_toPure_677_, v_inst_678_, v_toBind_679_, v_a_680_, v_____x_681_);
lean_dec_ref(v_a_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(lean_object* v_inst_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v_toApplicative_686_; lean_object* v_toBind_687_; lean_object* v_toPure_688_; lean_object* v___f_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_toApplicative_686_ = lean_ctor_get(v_inst_683_, 0);
v_toBind_687_ = lean_ctor_get(v_inst_683_, 1);
lean_inc_n(v_toBind_687_, 2);
v_toPure_688_ = lean_ctor_get(v_toApplicative_686_, 1);
lean_inc_n(v_toPure_688_, 2);
lean_inc_ref_n(v_a_684_, 2);
v___f_689_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10___boxed), 5, 4);
lean_closure_set(v___f_689_, 0, v_toPure_688_);
lean_closure_set(v___f_689_, 1, v_inst_683_);
lean_closure_set(v___f_689_, 2, v_toBind_687_);
lean_closure_set(v___f_689_, 3, v_a_684_);
v___x_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_690_, 0, v_a_684_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v_a_685_);
v___x_692_ = lean_apply_2(v_toPure_688_, lean_box(0), v___x_691_);
v___x_693_ = lean_apply_4(v_toBind_687_, lean_box(0), lean_box(0), v___x_692_, v___f_689_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___boxed(lean_object* v_inst_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_694_, v_a_695_, v_a_696_);
lean_dec_ref(v_a_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(lean_object* v_m_698_, lean_object* v_inst_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_699_, v_a_700_, v_a_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___boxed(lean_object* v_m_703_, lean_object* v_inst_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(v_m_703_, v_inst_704_, v_a_705_, v_a_706_);
lean_dec_ref(v_a_705_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0(lean_object* v_toPure_708_, lean_object* v_____x_709_){
_start:
{
lean_object* v_fst_710_; 
v_fst_710_ = lean_ctor_get(v_____x_709_, 0);
lean_inc(v_fst_710_);
if (lean_obj_tag(v_fst_710_) == 0)
{
lean_object* v_snd_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_727_; 
v_snd_711_ = lean_ctor_get(v_____x_709_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v_____x_709_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; 
v_unused_728_ = lean_ctor_get(v_____x_709_, 0);
lean_dec(v_unused_728_);
v___x_713_ = v_____x_709_;
v_isShared_714_ = v_isSharedCheck_727_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_snd_711_);
lean_dec(v_____x_709_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_727_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_726_; 
v_a_715_ = lean_ctor_get(v_fst_710_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v_fst_710_);
if (v_isSharedCheck_726_ == 0)
{
v___x_717_ = v_fst_710_;
v_isShared_718_ = v_isSharedCheck_726_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v_fst_710_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_726_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_725_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_720_);
v___x_722_ = v___x_713_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_snd_711_);
v___x_722_ = v_reuseFailAlloc_724_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; 
v___x_723_ = lean_apply_2(v_toPure_708_, lean_box(0), v___x_722_);
return v___x_723_;
}
}
}
}
}
else
{
lean_object* v_snd_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_745_; 
v_snd_729_ = lean_ctor_get(v_____x_709_, 1);
v_isSharedCheck_745_ = !lean_is_exclusive(v_____x_709_);
if (v_isSharedCheck_745_ == 0)
{
lean_object* v_unused_746_; 
v_unused_746_ = lean_ctor_get(v_____x_709_, 0);
lean_dec(v_unused_746_);
v___x_731_ = v_____x_709_;
v_isShared_732_ = v_isSharedCheck_745_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_snd_729_);
lean_dec(v_____x_709_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_745_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_744_; 
v_a_733_ = lean_ctor_get(v_fst_710_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_fst_710_);
if (v_isSharedCheck_744_ == 0)
{
v___x_735_ = v_fst_710_;
v_isShared_736_ = v_isSharedCheck_744_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v_fst_710_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_744_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_743_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_740_; 
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_738_);
v___x_740_ = v___x_731_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_snd_729_);
v___x_740_ = v_reuseFailAlloc_742_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; 
v___x_741_ = lean_apply_2(v_toPure_708_, lean_box(0), v___x_740_);
return v___x_741_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1(lean_object* v_toPure_747_, lean_object* v___x_748_, lean_object* v_____x_749_){
_start:
{
lean_object* v_fst_750_; 
v_fst_750_ = lean_ctor_get(v_____x_749_, 0);
lean_inc(v_fst_750_);
if (lean_obj_tag(v_fst_750_) == 0)
{
lean_object* v_snd_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_767_; 
v_snd_751_ = lean_ctor_get(v_____x_749_, 1);
v_isSharedCheck_767_ = !lean_is_exclusive(v_____x_749_);
if (v_isSharedCheck_767_ == 0)
{
lean_object* v_unused_768_; 
v_unused_768_ = lean_ctor_get(v_____x_749_, 0);
lean_dec(v_unused_768_);
v___x_753_ = v_____x_749_;
v_isShared_754_ = v_isSharedCheck_767_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_snd_751_);
lean_dec(v_____x_749_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_767_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_766_; 
v_a_755_ = lean_ctor_get(v_fst_750_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v_fst_750_);
if (v_isSharedCheck_766_ == 0)
{
v___x_757_ = v_fst_750_;
v_isShared_758_ = v_isSharedCheck_766_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v_fst_750_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_766_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_765_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_762_; 
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_760_);
v___x_762_ = v___x_753_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_snd_751_);
v___x_762_ = v_reuseFailAlloc_764_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_763_; 
v___x_763_ = lean_apply_2(v_toPure_747_, lean_box(0), v___x_762_);
return v___x_763_;
}
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_796_; 
v_a_769_ = lean_ctor_get(v_fst_750_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_fst_750_);
if (v_isSharedCheck_796_ == 0)
{
v___x_771_ = v_fst_750_;
v_isShared_772_ = v_isSharedCheck_796_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v_fst_750_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_796_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v_fst_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_794_; 
v_fst_773_ = lean_ctor_get(v_a_769_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v_a_769_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v_a_769_, 1);
lean_dec(v_unused_795_);
v___x_775_ = v_a_769_;
v_isShared_776_ = v_isSharedCheck_794_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_fst_773_);
lean_dec(v_a_769_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_794_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
if (lean_obj_tag(v_fst_773_) == 0)
{
lean_object* v_snd_777_; lean_object* v___x_779_; 
v_snd_777_ = lean_ctor_get(v_____x_749_, 1);
lean_inc(v_snd_777_);
lean_dec_ref(v_____x_749_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_748_);
v___x_779_ = v___x_771_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_748_);
v___x_779_ = v_reuseFailAlloc_784_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_781_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v_snd_777_);
lean_ctor_set(v___x_775_, 0, v___x_779_);
v___x_781_ = v___x_775_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_snd_777_);
v___x_781_ = v_reuseFailAlloc_783_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; 
v___x_782_ = lean_apply_2(v_toPure_747_, lean_box(0), v___x_781_);
return v___x_782_;
}
}
}
else
{
lean_object* v_snd_785_; lean_object* v_val_786_; lean_object* v___x_788_; 
v_snd_785_ = lean_ctor_get(v_____x_749_, 1);
lean_inc(v_snd_785_);
lean_dec_ref(v_____x_749_);
v_val_786_ = lean_ctor_get(v_fst_773_, 0);
lean_inc(v_val_786_);
lean_dec_ref(v_fst_773_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v_val_786_);
v___x_788_ = v___x_771_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_val_786_);
v___x_788_ = v_reuseFailAlloc_793_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_790_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v_snd_785_);
lean_ctor_set(v___x_775_, 0, v___x_788_);
v___x_790_ = v___x_775_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_snd_785_);
v___x_790_ = v_reuseFailAlloc_792_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; 
v___x_791_ = lean_apply_2(v_toPure_747_, lean_box(0), v___x_790_);
return v___x_791_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2(lean_object* v_toPure_797_, lean_object* v___x_798_, lean_object* v___x_799_, lean_object* v_____x_800_){
_start:
{
lean_object* v_fst_801_; 
v_fst_801_ = lean_ctor_get(v_____x_800_, 0);
lean_inc(v_fst_801_);
if (lean_obj_tag(v_fst_801_) == 0)
{
lean_object* v_snd_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_818_; 
lean_dec_ref(v___x_798_);
v_snd_802_ = lean_ctor_get(v_____x_800_, 1);
v_isSharedCheck_818_ = !lean_is_exclusive(v_____x_800_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v_____x_800_, 0);
lean_dec(v_unused_819_);
v___x_804_ = v_____x_800_;
v_isShared_805_ = v_isSharedCheck_818_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_snd_802_);
lean_dec(v_____x_800_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_818_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_817_; 
v_a_806_ = lean_ctor_get(v_fst_801_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v_fst_801_);
if (v_isSharedCheck_817_ == 0)
{
v___x_808_ = v_fst_801_;
v_isShared_809_ = v_isSharedCheck_817_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v_fst_801_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_817_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_816_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_813_; 
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_811_);
v___x_813_ = v___x_804_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_snd_802_);
v___x_813_ = v_reuseFailAlloc_815_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; 
v___x_814_ = lean_apply_2(v_toPure_797_, lean_box(0), v___x_813_);
return v___x_814_;
}
}
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_855_; 
v_a_820_ = lean_ctor_get(v_fst_801_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v_fst_801_);
if (v_isSharedCheck_855_ == 0)
{
v___x_822_ = v_fst_801_;
v_isShared_823_ = v_isSharedCheck_855_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v_fst_801_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_855_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
uint8_t v___x_824_; 
v___x_824_ = lean_unbox(v_a_820_);
lean_dec(v_a_820_);
if (v___x_824_ == 0)
{
lean_object* v_snd_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_837_; 
v_snd_825_ = lean_ctor_get(v_____x_800_, 1);
v_isSharedCheck_837_ = !lean_is_exclusive(v_____x_800_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; 
v_unused_838_ = lean_ctor_get(v_____x_800_, 0);
lean_dec(v_unused_838_);
v___x_827_ = v_____x_800_;
v_isShared_828_ = v_isSharedCheck_837_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_snd_825_);
lean_dec(v_____x_800_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_837_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_798_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_829_);
v___x_831_ = v___x_822_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_836_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_833_; 
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_831_);
v___x_833_ = v___x_827_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_snd_825_);
v___x_833_ = v_reuseFailAlloc_835_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_834_; 
v___x_834_ = lean_apply_2(v_toPure_797_, lean_box(0), v___x_833_);
return v___x_834_;
}
}
}
}
else
{
lean_object* v_snd_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_853_; 
lean_dec_ref(v___x_798_);
v_snd_839_ = lean_ctor_get(v_____x_800_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v_____x_800_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v_____x_800_, 0);
lean_dec(v_unused_854_);
v___x_841_ = v_____x_800_;
v_isShared_842_ = v_isSharedCheck_853_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_snd_839_);
lean_dec(v_____x_800_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_853_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_799_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v___x_799_);
lean_ctor_set(v___x_841_, 0, v___x_843_);
v___x_845_ = v___x_841_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v___x_799_);
v___x_845_ = v_reuseFailAlloc_852_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_846_);
v___x_848_ = v___x_822_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_851_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v_snd_839_);
v___x_850_ = lean_apply_2(v_toPure_797_, lean_box(0), v___x_849_);
return v___x_850_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(lean_object* v_inst_856_, lean_object* v_toBind_857_, lean_object* v___f_858_, lean_object* v_____r_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_856_, v___y_860_, v___y_861_);
v___x_863_ = lean_apply_4(v_toBind_857_, lean_box(0), lean_box(0), v___x_862_, v___f_858_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3___boxed(lean_object* v_inst_864_, lean_object* v_toBind_865_, lean_object* v___f_866_, lean_object* v_____r_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(v_inst_864_, v_toBind_865_, v___f_866_, v_____r_867_, v___y_868_, v___y_869_);
lean_dec_ref(v___y_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(lean_object* v_toPure_871_, lean_object* v_next_872_, lean_object* v_G_873_, lean_object* v___y_874_, lean_object* v_____x_875_){
_start:
{
lean_object* v_fst_876_; 
v_fst_876_ = lean_ctor_get(v_____x_875_, 0);
lean_inc(v_fst_876_);
if (lean_obj_tag(v_fst_876_) == 0)
{
lean_object* v_snd_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_G_873_);
v_snd_877_ = lean_ctor_get(v_____x_875_, 1);
v_isSharedCheck_893_ = !lean_is_exclusive(v_____x_875_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; 
v_unused_894_ = lean_ctor_get(v_____x_875_, 0);
lean_dec(v_unused_894_);
v___x_879_ = v_____x_875_;
v_isShared_880_ = v_isSharedCheck_893_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_snd_877_);
lean_dec(v_____x_875_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_893_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_892_; 
v_a_881_ = lean_ctor_get(v_fst_876_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v_fst_876_);
if (v_isSharedCheck_892_ == 0)
{
v___x_883_ = v_fst_876_;
v_isShared_884_ = v_isSharedCheck_892_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v_fst_876_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_892_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_891_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_886_);
v___x_888_ = v___x_879_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_snd_877_);
v___x_888_ = v_reuseFailAlloc_890_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; 
v___x_889_ = lean_apply_2(v_toPure_871_, lean_box(0), v___x_888_);
return v___x_889_;
}
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_918_; 
v_a_895_ = lean_ctor_get(v_fst_876_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v_fst_876_);
if (v_isSharedCheck_918_ == 0)
{
v___x_897_ = v_fst_876_;
v_isShared_898_ = v_isSharedCheck_918_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v_fst_876_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_918_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
if (lean_obj_tag(v_a_895_) == 0)
{
lean_object* v_snd_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_911_; 
lean_dec(v_G_873_);
v_snd_899_ = lean_ctor_get(v_____x_875_, 1);
v_isSharedCheck_911_ = !lean_is_exclusive(v_____x_875_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; 
v_unused_912_ = lean_ctor_get(v_____x_875_, 0);
lean_dec(v_unused_912_);
v___x_901_ = v_____x_875_;
v_isShared_902_ = v_isSharedCheck_911_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_snd_899_);
lean_dec(v_____x_875_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_911_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v_a_903_; lean_object* v___x_905_; 
v_a_903_ = lean_ctor_get(v_a_895_, 0);
lean_inc(v_a_903_);
lean_dec_ref(v_a_895_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v_a_903_);
v___x_905_ = v___x_897_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_903_);
v___x_905_ = v_reuseFailAlloc_910_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_907_; 
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_905_);
v___x_907_ = v___x_901_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_snd_899_);
v___x_907_ = v_reuseFailAlloc_909_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; 
v___x_908_ = lean_apply_2(v_toPure_871_, lean_box(0), v___x_907_);
return v___x_908_;
}
}
}
}
else
{
lean_object* v_snd_913_; lean_object* v_a_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
lean_del_object(v___x_897_);
lean_dec(v_toPure_871_);
v_snd_913_ = lean_ctor_get(v_____x_875_, 1);
lean_inc(v_snd_913_);
lean_dec_ref(v_____x_875_);
v_a_914_ = lean_ctor_get(v_a_895_, 0);
lean_inc(v_a_914_);
lean_dec_ref(v_a_895_);
v___x_915_ = lean_unsigned_to_nat(1u);
v___x_916_ = lean_nat_add(v_next_872_, v___x_915_);
lean_inc_ref(v___y_874_);
v___x_917_ = lean_apply_6(v_G_873_, v___x_916_, v_a_914_, lean_box(0), lean_box(0), v___y_874_, v_snd_913_);
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed(lean_object* v_toPure_919_, lean_object* v_next_920_, lean_object* v_G_921_, lean_object* v___y_922_, lean_object* v_____x_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(v_toPure_919_, v_next_920_, v_G_921_, v___y_922_, v_____x_923_);
lean_dec_ref(v___y_922_);
lean_dec(v_next_920_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(lean_object* v_toPure_925_, lean_object* v___f_926_, lean_object* v___y_927_, lean_object* v_____x_928_){
_start:
{
lean_object* v_fst_929_; 
v_fst_929_ = lean_ctor_get(v_____x_928_, 0);
lean_inc(v_fst_929_);
if (lean_obj_tag(v_fst_929_) == 0)
{
lean_object* v_snd_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_946_; 
lean_dec(v___f_926_);
v_snd_930_ = lean_ctor_get(v_____x_928_, 1);
v_isSharedCheck_946_ = !lean_is_exclusive(v_____x_928_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v_____x_928_, 0);
lean_dec(v_unused_947_);
v___x_932_ = v_____x_928_;
v_isShared_933_ = v_isSharedCheck_946_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_snd_930_);
lean_dec(v_____x_928_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_946_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_945_; 
v_a_934_ = lean_ctor_get(v_fst_929_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v_fst_929_);
if (v_isSharedCheck_945_ == 0)
{
v___x_936_ = v_fst_929_;
v_isShared_937_ = v_isSharedCheck_945_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v_fst_929_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_945_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_944_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_941_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_939_);
v___x_941_ = v___x_932_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_snd_930_);
v___x_941_ = v_reuseFailAlloc_943_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_942_; 
v___x_942_ = lean_apply_2(v_toPure_925_, lean_box(0), v___x_941_);
return v___x_942_;
}
}
}
}
}
else
{
lean_object* v_snd_948_; lean_object* v_a_949_; lean_object* v___x_950_; 
lean_dec(v_toPure_925_);
v_snd_948_ = lean_ctor_get(v_____x_928_, 1);
lean_inc(v_snd_948_);
lean_dec_ref(v_____x_928_);
v_a_949_ = lean_ctor_get(v_fst_929_, 0);
lean_inc(v_a_949_);
lean_dec_ref(v_fst_929_);
lean_inc_ref(v___y_927_);
v___x_950_ = lean_apply_3(v___f_926_, v_a_949_, v___y_927_, v_snd_948_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5___boxed(lean_object* v_toPure_951_, lean_object* v___f_952_, lean_object* v___y_953_, lean_object* v_____x_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(v_toPure_951_, v___f_952_, v___y_953_, v_____x_954_);
lean_dec_ref(v___y_953_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(lean_object* v___x_956_, lean_object* v_toPure_957_, lean_object* v_toBind_958_, lean_object* v___f_959_, lean_object* v_initialMask_960_, lean_object* v___f_961_, lean_object* v_inst_962_, lean_object* v___x_963_, lean_object* v_next_964_, lean_object* v_acc_965_, lean_object* v_h_966_, lean_object* v_G_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
uint8_t v___x_970_; 
v___x_970_ = lean_nat_dec_lt(v_next_964_, v___x_956_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
lean_dec(v_G_967_);
lean_dec(v_next_964_);
lean_dec_ref(v_inst_962_);
lean_dec(v___f_961_);
lean_dec(v___f_959_);
lean_dec(v_toBind_958_);
v___x_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_971_, 0, v_acc_965_);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v___y_969_);
v___x_973_ = lean_apply_2(v_toPure_957_, lean_box(0), v___x_972_);
return v___x_973_;
}
else
{
lean_object* v___f_974_; lean_object* v___y_976_; lean_object* v___x_979_; uint8_t v___x_980_; 
lean_dec_ref(v_acc_965_);
lean_inc_ref(v___y_968_);
lean_inc(v_next_964_);
lean_inc(v_toPure_957_);
v___f_974_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_974_, 0, v_toPure_957_);
lean_closure_set(v___f_974_, 1, v_next_964_);
lean_closure_set(v___f_974_, 2, v_G_967_);
lean_closure_set(v___f_974_, 3, v___y_968_);
v___x_979_ = lean_array_fget_borrowed(v_initialMask_960_, v_next_964_);
v___x_980_ = lean_unbox(v___x_979_);
if (v___x_980_ == 0)
{
lean_object* v___f_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
lean_inc_ref(v___y_968_);
v___f_981_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_981_, 0, v_toPure_957_);
lean_closure_set(v___f_981_, 1, v___f_961_);
lean_closure_set(v___f_981_, 2, v___y_968_);
v___x_982_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(v_next_964_, v_inst_962_, v___y_969_);
lean_inc(v_toBind_958_);
v___x_983_ = lean_apply_4(v_toBind_958_, lean_box(0), lean_box(0), v___x_982_, v___f_981_);
v___y_976_ = v___x_983_;
goto v___jp_975_;
}
else
{
lean_object* v___x_984_; 
lean_dec(v_next_964_);
lean_dec_ref(v_inst_962_);
lean_dec(v_toPure_957_);
lean_inc_ref(v___y_968_);
v___x_984_ = lean_apply_3(v___f_961_, v___x_963_, v___y_968_, v___y_969_);
v___y_976_ = v___x_984_;
goto v___jp_975_;
}
v___jp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
lean_inc(v_toBind_958_);
v___x_977_ = lean_apply_4(v_toBind_958_, lean_box(0), lean_box(0), v___y_976_, v___f_959_);
v___x_978_ = lean_apply_4(v_toBind_958_, lean_box(0), lean_box(0), v___x_977_, v___f_974_);
return v___x_978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed(lean_object* v___x_985_, lean_object* v_toPure_986_, lean_object* v_toBind_987_, lean_object* v___f_988_, lean_object* v_initialMask_989_, lean_object* v___f_990_, lean_object* v_inst_991_, lean_object* v___x_992_, lean_object* v_next_993_, lean_object* v_acc_994_, lean_object* v_h_995_, lean_object* v_G_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(v___x_985_, v_toPure_986_, v_toBind_987_, v___f_988_, v_initialMask_989_, v___f_990_, v_inst_991_, v___x_992_, v_next_993_, v_acc_994_, v_h_995_, v_G_996_, v___y_997_, v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec_ref(v_initialMask_989_);
lean_dec(v___x_985_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(lean_object* v_toPure_1003_, lean_object* v_inst_1004_, lean_object* v_toBind_1005_, lean_object* v___f_1006_, lean_object* v_a_1007_, lean_object* v_____x_1008_){
_start:
{
lean_object* v_fst_1009_; 
v_fst_1009_ = lean_ctor_get(v_____x_1008_, 0);
lean_inc(v_fst_1009_);
if (lean_obj_tag(v_fst_1009_) == 0)
{
lean_object* v_snd_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v___f_1006_);
lean_dec(v_toBind_1005_);
lean_dec_ref(v_inst_1004_);
v_snd_1010_ = lean_ctor_get(v_____x_1008_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_____x_1008_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v_____x_1008_, 0);
lean_dec(v_unused_1027_);
v___x_1012_ = v_____x_1008_;
v_isShared_1013_ = v_isSharedCheck_1026_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_snd_1010_);
lean_dec(v_____x_1008_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1026_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1025_; 
v_a_1014_ = lean_ctor_get(v_fst_1009_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_fst_1009_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1016_ = v_fst_1009_;
v_isShared_1017_ = v_isSharedCheck_1025_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v_fst_1009_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1025_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1019_);
v___x_1021_ = v___x_1012_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_snd_1010_);
v___x_1021_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_apply_2(v_toPure_1003_, lean_box(0), v___x_1021_);
return v___x_1022_;
}
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v_snd_1029_; lean_object* v_initialMask_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___f_1034_; lean_object* v___x_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___x_6347__overap_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v_a_1028_ = lean_ctor_get(v_fst_1009_, 0);
lean_inc(v_a_1028_);
lean_dec_ref(v_fst_1009_);
v_snd_1029_ = lean_ctor_get(v_____x_1008_, 1);
lean_inc(v_snd_1029_);
lean_dec_ref(v_____x_1008_);
v_initialMask_1030_ = lean_ctor_get(v_a_1028_, 0);
lean_inc_ref(v_initialMask_1030_);
lean_dec(v_a_1028_);
v___x_1031_ = lean_array_get_size(v_initialMask_1030_);
v___x_1032_ = lean_unsigned_to_nat(0u);
v___x_1033_ = lean_box(0);
lean_inc_n(v_toPure_1003_, 2);
v___f_1034_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1034_, 0, v_toPure_1003_);
lean_closure_set(v___f_1034_, 1, v___x_1033_);
v___x_1035_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0));
v___f_1036_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1036_, 0, v_toPure_1003_);
lean_closure_set(v___f_1036_, 1, v___x_1035_);
lean_closure_set(v___f_1036_, 2, v___x_1033_);
lean_inc_n(v_toBind_1005_, 2);
lean_inc_ref(v_inst_1004_);
v___f_1037_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1037_, 0, v_inst_1004_);
lean_closure_set(v___f_1037_, 1, v_toBind_1005_);
lean_closure_set(v___f_1037_, 2, v___f_1036_);
v___f_1038_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed), 14, 8);
lean_closure_set(v___f_1038_, 0, v___x_1031_);
lean_closure_set(v___f_1038_, 1, v_toPure_1003_);
lean_closure_set(v___f_1038_, 2, v_toBind_1005_);
lean_closure_set(v___f_1038_, 3, v___f_1006_);
lean_closure_set(v___f_1038_, 4, v_initialMask_1030_);
lean_closure_set(v___f_1038_, 5, v___f_1037_);
lean_closure_set(v___f_1038_, 6, v_inst_1004_);
lean_closure_set(v___f_1038_, 7, v___x_1033_);
v___x_6347__overap_1039_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1038_, v___x_1032_, v___x_1035_, lean_box(0));
lean_inc_ref(v_a_1007_);
v___x_1040_ = lean_apply_2(v___x_6347__overap_1039_, v_a_1007_, v_snd_1029_);
v___x_1041_ = lean_apply_4(v_toBind_1005_, lean_box(0), lean_box(0), v___x_1040_, v___f_1034_);
return v___x_1041_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___boxed(lean_object* v_toPure_1042_, lean_object* v_inst_1043_, lean_object* v_toBind_1044_, lean_object* v___f_1045_, lean_object* v_a_1046_, lean_object* v_____x_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(v_toPure_1042_, v_inst_1043_, v_toBind_1044_, v___f_1045_, v_a_1046_, v_____x_1047_);
lean_dec_ref(v_a_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(lean_object* v_inst_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_toApplicative_1052_; lean_object* v_toBind_1053_; lean_object* v_toPure_1054_; lean_object* v___f_1055_; lean_object* v___f_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_toApplicative_1052_ = lean_ctor_get(v_inst_1049_, 0);
v_toBind_1053_ = lean_ctor_get(v_inst_1049_, 1);
lean_inc_n(v_toBind_1053_, 2);
v_toPure_1054_ = lean_ctor_get(v_toApplicative_1052_, 1);
lean_inc_n(v_toPure_1054_, 3);
v___f_1055_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1055_, 0, v_toPure_1054_);
lean_inc_ref_n(v_a_1050_, 2);
v___f_1056_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_1056_, 0, v_toPure_1054_);
lean_closure_set(v___f_1056_, 1, v_inst_1049_);
lean_closure_set(v___f_1056_, 2, v_toBind_1053_);
lean_closure_set(v___f_1056_, 3, v___f_1055_);
lean_closure_set(v___f_1056_, 4, v_a_1050_);
v___x_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1057_, 0, v_a_1050_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v_a_1051_);
v___x_1059_ = lean_apply_2(v_toPure_1054_, lean_box(0), v___x_1058_);
v___x_1060_ = lean_apply_4(v_toBind_1053_, lean_box(0), lean_box(0), v___x_1059_, v___f_1056_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___boxed(lean_object* v_inst_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1061_, v_a_1062_, v_a_1063_);
lean_dec_ref(v_a_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(lean_object* v_m_1065_, lean_object* v_inst_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1066_, v_a_1067_, v_a_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___boxed(lean_object* v_m_1070_, lean_object* v_inst_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(v_m_1070_, v_inst_1071_, v_a_1072_, v_a_1073_);
lean_dec_ref(v_a_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0(lean_object* v_toPure_1077_, lean_object* v_____x_1078_){
_start:
{
lean_object* v_fst_1079_; 
v_fst_1079_ = lean_ctor_get(v_____x_1078_, 0);
lean_inc(v_fst_1079_);
if (lean_obj_tag(v_fst_1079_) == 0)
{
lean_object* v_snd_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1096_; 
v_snd_1080_ = lean_ctor_get(v_____x_1078_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_____x_1078_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v_____x_1078_, 0);
lean_dec(v_unused_1097_);
v___x_1082_ = v_____x_1078_;
v_isShared_1083_ = v_isSharedCheck_1096_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_snd_1080_);
lean_dec(v_____x_1078_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1096_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1095_; 
v_a_1084_ = lean_ctor_get(v_fst_1079_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_fst_1079_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1086_ = v_fst_1079_;
v_isShared_1087_ = v_isSharedCheck_1095_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v_fst_1079_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1095_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1091_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1089_);
v___x_1091_ = v___x_1082_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_snd_1080_);
v___x_1091_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_apply_2(v_toPure_1077_, lean_box(0), v___x_1091_);
return v___x_1092_;
}
}
}
}
}
else
{
lean_object* v_snd_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1107_; 
lean_dec_ref(v_fst_1079_);
v_snd_1098_ = lean_ctor_get(v_____x_1078_, 1);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_____x_1078_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; 
v_unused_1108_ = lean_ctor_get(v_____x_1078_, 0);
lean_dec(v_unused_1108_);
v___x_1100_ = v_____x_1078_;
v_isShared_1101_ = v_isSharedCheck_1107_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_snd_1098_);
lean_dec(v_____x_1078_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1107_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1102_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0));
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1102_);
v___x_1104_ = v___x_1100_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_snd_1098_);
v___x_1104_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_apply_2(v_toPure_1077_, lean_box(0), v___x_1104_);
return v___x_1105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1(lean_object* v_toPure_1109_, lean_object* v___x_1110_, lean_object* v_____x_1111_){
_start:
{
lean_object* v_fst_1112_; 
v_fst_1112_ = lean_ctor_get(v_____x_1111_, 0);
lean_inc(v_fst_1112_);
if (lean_obj_tag(v_fst_1112_) == 0)
{
lean_object* v_snd_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1129_; 
lean_dec(v___x_1110_);
v_snd_1113_ = lean_ctor_get(v_____x_1111_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_____x_1111_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; 
v_unused_1130_ = lean_ctor_get(v_____x_1111_, 0);
lean_dec(v_unused_1130_);
v___x_1115_ = v_____x_1111_;
v_isShared_1116_ = v_isSharedCheck_1129_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_snd_1113_);
lean_dec(v_____x_1111_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1129_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1128_; 
v_a_1117_ = lean_ctor_get(v_fst_1112_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_fst_1112_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1119_ = v_fst_1112_;
v_isShared_1120_ = v_isSharedCheck_1128_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v_fst_1112_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1128_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1124_; 
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1122_);
v___x_1124_ = v___x_1115_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_snd_1113_);
v___x_1124_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_apply_2(v_toPure_1109_, lean_box(0), v___x_1124_);
return v___x_1125_;
}
}
}
}
}
else
{
lean_object* v_snd_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1148_; 
v_snd_1131_ = lean_ctor_get(v_____x_1111_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_____x_1111_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v_____x_1111_, 0);
lean_dec(v_unused_1149_);
v___x_1133_ = v_____x_1111_;
v_isShared_1134_ = v_isSharedCheck_1148_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_snd_1131_);
lean_dec(v_____x_1111_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1148_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1146_; 
v_isSharedCheck_1146_ = !lean_is_exclusive(v_fst_1112_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; 
v_unused_1147_ = lean_ctor_get(v_fst_1112_, 0);
lean_dec(v_unused_1147_);
v___x_1136_ = v_fst_1112_;
v_isShared_1137_ = v_isSharedCheck_1146_;
goto v_resetjp_1135_;
}
else
{
lean_dec(v_fst_1112_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1146_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1110_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1138_);
v___x_1140_ = v___x_1136_;
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
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1140_);
v___x_1142_ = v___x_1133_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_snd_1131_);
v___x_1142_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_apply_2(v_toPure_1109_, lean_box(0), v___x_1142_);
return v___x_1143_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2(lean_object* v_toPure_1150_, lean_object* v___x_1151_, lean_object* v_inst_1152_, lean_object* v_toBind_1153_, lean_object* v___f_1154_, lean_object* v___x_1155_, lean_object* v_____x_1156_){
_start:
{
lean_object* v_fst_1157_; 
v_fst_1157_ = lean_ctor_get(v_____x_1156_, 0);
lean_inc(v_fst_1157_);
if (lean_obj_tag(v_fst_1157_) == 0)
{
lean_object* v_snd_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v___x_1155_);
lean_dec(v___f_1154_);
lean_dec(v_toBind_1153_);
lean_dec_ref(v_inst_1152_);
v_snd_1158_ = lean_ctor_get(v_____x_1156_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_____x_1156_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; 
v_unused_1175_ = lean_ctor_get(v_____x_1156_, 0);
lean_dec(v_unused_1175_);
v___x_1160_ = v_____x_1156_;
v_isShared_1161_ = v_isSharedCheck_1174_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_snd_1158_);
lean_dec(v_____x_1156_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1174_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1173_; 
v_a_1162_ = lean_ctor_get(v_fst_1157_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_fst_1157_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1164_ = v_fst_1157_;
v_isShared_1165_ = v_isSharedCheck_1173_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v_fst_1157_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1173_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1169_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1167_);
v___x_1169_ = v___x_1160_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_snd_1158_);
v___x_1169_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_apply_2(v_toPure_1150_, lean_box(0), v___x_1169_);
return v___x_1170_;
}
}
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1198_; 
v_a_1176_ = lean_ctor_get(v_fst_1157_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_fst_1157_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1178_ = v_fst_1157_;
v_isShared_1179_ = v_isSharedCheck_1198_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v_fst_1157_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1198_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
uint8_t v___x_1180_; 
v___x_1180_ = lean_unbox(v_a_1176_);
lean_dec(v_a_1176_);
if (v___x_1180_ == 0)
{
lean_object* v_snd_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_del_object(v___x_1178_);
lean_dec(v___x_1155_);
lean_dec(v_toPure_1150_);
v_snd_1181_ = lean_ctor_get(v_____x_1156_, 1);
lean_inc(v_snd_1181_);
lean_dec_ref(v_____x_1156_);
v___x_1182_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(v___x_1151_, v_inst_1152_, v_snd_1181_);
v___x_1183_ = lean_apply_4(v_toBind_1153_, lean_box(0), lean_box(0), v___x_1182_, v___f_1154_);
return v___x_1183_;
}
else
{
lean_object* v_snd_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1196_; 
lean_dec(v___f_1154_);
lean_dec(v_toBind_1153_);
lean_dec_ref(v_inst_1152_);
v_snd_1184_ = lean_ctor_get(v_____x_1156_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_____x_1156_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; 
v_unused_1197_ = lean_ctor_get(v_____x_1156_, 0);
lean_dec(v_unused_1197_);
v___x_1186_ = v_____x_1156_;
v_isShared_1187_ = v_isSharedCheck_1196_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_snd_1184_);
lean_dec(v_____x_1156_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1196_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1155_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1188_);
v___x_1190_ = v___x_1178_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1192_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1190_);
v___x_1192_ = v___x_1186_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_snd_1184_);
v___x_1192_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_apply_2(v_toPure_1150_, lean_box(0), v___x_1192_);
return v___x_1193_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2___boxed(lean_object* v_toPure_1199_, lean_object* v___x_1200_, lean_object* v_inst_1201_, lean_object* v_toBind_1202_, lean_object* v___f_1203_, lean_object* v___x_1204_, lean_object* v_____x_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2(v_toPure_1199_, v___x_1200_, v_inst_1201_, v_toBind_1202_, v___f_1203_, v___x_1204_, v_____x_1205_);
lean_dec(v___x_1200_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(lean_object* v_toPure_1207_, lean_object* v_inst_1208_, lean_object* v___y_1209_, lean_object* v_toBind_1210_, lean_object* v___f_1211_, lean_object* v_____x_1212_){
_start:
{
lean_object* v_fst_1213_; 
v_fst_1213_ = lean_ctor_get(v_____x_1212_, 0);
lean_inc(v_fst_1213_);
if (lean_obj_tag(v_fst_1213_) == 0)
{
lean_object* v_snd_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v___f_1211_);
lean_dec(v_toBind_1210_);
lean_dec_ref(v_inst_1208_);
v_snd_1214_ = lean_ctor_get(v_____x_1212_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_____x_1212_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v_____x_1212_, 0);
lean_dec(v_unused_1231_);
v___x_1216_ = v_____x_1212_;
v_isShared_1217_ = v_isSharedCheck_1230_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_snd_1214_);
lean_dec(v_____x_1212_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1230_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1229_; 
v_a_1218_ = lean_ctor_get(v_fst_1213_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_fst_1213_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1220_ = v_fst_1213_;
v_isShared_1221_ = v_isSharedCheck_1229_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v_fst_1213_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1229_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1225_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1223_);
v___x_1225_ = v___x_1216_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_snd_1214_);
v___x_1225_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_apply_2(v_toPure_1207_, lean_box(0), v___x_1225_);
return v___x_1226_;
}
}
}
}
}
else
{
lean_object* v_snd_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec_ref(v_fst_1213_);
lean_dec(v_toPure_1207_);
v_snd_1232_ = lean_ctor_get(v_____x_1212_, 1);
lean_inc(v_snd_1232_);
lean_dec_ref(v_____x_1212_);
v___x_1233_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_1208_, v___y_1209_, v_snd_1232_);
v___x_1234_ = lean_apply_4(v_toBind_1210_, lean_box(0), lean_box(0), v___x_1233_, v___f_1211_);
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3___boxed(lean_object* v_toPure_1235_, lean_object* v_inst_1236_, lean_object* v___y_1237_, lean_object* v_toBind_1238_, lean_object* v___f_1239_, lean_object* v_____x_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(v_toPure_1235_, v_inst_1236_, v___y_1237_, v_toBind_1238_, v___f_1239_, v_____x_1240_);
lean_dec_ref(v___y_1237_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(lean_object* v_toPure_1242_, lean_object* v___x_1243_, lean_object* v_inst_1244_, lean_object* v_toBind_1245_, lean_object* v___f_1246_, lean_object* v___y_1247_, lean_object* v_____x_1248_){
_start:
{
lean_object* v_fst_1249_; 
v_fst_1249_ = lean_ctor_get(v_____x_1248_, 0);
lean_inc(v_fst_1249_);
if (lean_obj_tag(v_fst_1249_) == 0)
{
lean_object* v_snd_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v___f_1246_);
lean_dec(v_toBind_1245_);
lean_dec_ref(v_inst_1244_);
lean_dec(v___x_1243_);
v_snd_1250_ = lean_ctor_get(v_____x_1248_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_____x_1248_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v_____x_1248_, 0);
lean_dec(v_unused_1267_);
v___x_1252_ = v_____x_1248_;
v_isShared_1253_ = v_isSharedCheck_1266_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_snd_1250_);
lean_dec(v_____x_1248_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1266_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1265_; 
v_a_1254_ = lean_ctor_get(v_fst_1249_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_fst_1249_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1256_ = v_fst_1249_;
v_isShared_1257_ = v_isSharedCheck_1265_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v_fst_1249_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1265_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1261_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___x_1259_);
v___x_1261_ = v___x_1252_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_snd_1250_);
v___x_1261_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_apply_2(v_toPure_1242_, lean_box(0), v___x_1261_);
return v___x_1262_;
}
}
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v_snd_1269_; lean_object* v_added_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___f_1273_; lean_object* v___f_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_a_1268_ = lean_ctor_get(v_fst_1249_, 0);
lean_inc(v_a_1268_);
lean_dec_ref(v_fst_1249_);
v_snd_1269_ = lean_ctor_get(v_____x_1248_, 1);
lean_inc(v_snd_1269_);
lean_dec_ref(v_____x_1248_);
v_added_1270_ = lean_ctor_get(v_a_1268_, 1);
lean_inc_ref(v_added_1270_);
lean_dec(v_a_1268_);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = lean_array_get(v___x_1271_, v_added_1270_, v___x_1243_);
lean_dec_ref(v_added_1270_);
lean_inc_n(v_toBind_1245_, 2);
lean_inc_ref_n(v_inst_1244_, 2);
lean_inc(v___x_1272_);
lean_inc(v_toPure_1242_);
v___f_1273_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2___boxed), 7, 6);
lean_closure_set(v___f_1273_, 0, v_toPure_1242_);
lean_closure_set(v___f_1273_, 1, v___x_1272_);
lean_closure_set(v___f_1273_, 2, v_inst_1244_);
lean_closure_set(v___f_1273_, 3, v_toBind_1245_);
lean_closure_set(v___f_1273_, 4, v___f_1246_);
lean_closure_set(v___f_1273_, 5, v___x_1243_);
lean_inc_ref(v___y_1247_);
v___f_1274_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_1274_, 0, v_toPure_1242_);
lean_closure_set(v___f_1274_, 1, v_inst_1244_);
lean_closure_set(v___f_1274_, 2, v___y_1247_);
lean_closure_set(v___f_1274_, 3, v_toBind_1245_);
lean_closure_set(v___f_1274_, 4, v___f_1273_);
v___x_1275_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(v___x_1272_, v_inst_1244_, v_snd_1269_);
lean_dec(v___x_1272_);
v___x_1276_ = lean_apply_4(v_toBind_1245_, lean_box(0), lean_box(0), v___x_1275_, v___f_1274_);
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4___boxed(lean_object* v_toPure_1277_, lean_object* v___x_1278_, lean_object* v_inst_1279_, lean_object* v_toBind_1280_, lean_object* v___f_1281_, lean_object* v___y_1282_, lean_object* v_____x_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(v_toPure_1277_, v___x_1278_, v_inst_1279_, v_toBind_1280_, v___f_1281_, v___y_1282_, v_____x_1283_);
lean_dec_ref(v___y_1282_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(lean_object* v_toPure_1285_, lean_object* v___x_1286_, lean_object* v_inst_1287_, lean_object* v_toBind_1288_, lean_object* v_x_1289_, lean_object* v_____s_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = lean_nat_dec_lt(v___x_1293_, v_____s_1290_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_dec(v_toBind_1288_);
lean_dec_ref(v_inst_1287_);
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v_____s_1290_);
v___x_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
v___x_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
lean_ctor_set(v___x_1297_, 1, v___y_1292_);
v___x_1298_ = lean_apply_2(v_toPure_1285_, lean_box(0), v___x_1297_);
return v___x_1298_;
}
else
{
lean_object* v___x_1299_; lean_object* v___f_1300_; lean_object* v___f_1301_; lean_object* v___f_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1299_ = lean_nat_sub(v_____s_1290_, v___x_1286_);
lean_dec(v_____s_1290_);
lean_inc(v___x_1299_);
lean_inc_n(v_toPure_1285_, 3);
v___f_1300_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1300_, 0, v_toPure_1285_);
lean_closure_set(v___f_1300_, 1, v___x_1299_);
lean_inc_ref(v___y_1291_);
lean_inc_n(v_toBind_1288_, 2);
v___f_1301_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4___boxed), 7, 6);
lean_closure_set(v___f_1301_, 0, v_toPure_1285_);
lean_closure_set(v___f_1301_, 1, v___x_1299_);
lean_closure_set(v___f_1301_, 2, v_inst_1287_);
lean_closure_set(v___f_1301_, 3, v_toBind_1288_);
lean_closure_set(v___f_1301_, 4, v___f_1300_);
lean_closure_set(v___f_1301_, 5, v___y_1291_);
v___f_1302_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1302_, 0, v_toPure_1285_);
lean_inc_ref(v___y_1292_);
v___x_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___y_1292_);
lean_ctor_set(v___x_1303_, 1, v___y_1292_);
v___x_1304_ = lean_apply_2(v_toPure_1285_, lean_box(0), v___x_1303_);
v___x_1305_ = lean_apply_4(v_toBind_1288_, lean_box(0), lean_box(0), v___x_1304_, v___f_1302_);
v___x_1306_ = lean_apply_4(v_toBind_1288_, lean_box(0), lean_box(0), v___x_1305_, v___f_1301_);
return v___x_1306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed(lean_object* v_toPure_1307_, lean_object* v___x_1308_, lean_object* v_inst_1309_, lean_object* v_toBind_1310_, lean_object* v_x_1311_, lean_object* v_____s_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(v_toPure_1307_, v___x_1308_, v_inst_1309_, v_toBind_1310_, v_x_1311_, v_____s_1312_, v___y_1313_, v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___x_1308_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(lean_object* v_toPure_1316_, lean_object* v_inst_1317_, lean_object* v_toBind_1318_, lean_object* v___x_1319_, lean_object* v_a_1320_, lean_object* v___f_1321_, lean_object* v_____x_1322_){
_start:
{
lean_object* v_fst_1323_; 
v_fst_1323_ = lean_ctor_get(v_____x_1322_, 0);
lean_inc(v_fst_1323_);
if (lean_obj_tag(v_fst_1323_) == 0)
{
lean_object* v_snd_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v___f_1321_);
lean_dec_ref(v___x_1319_);
lean_dec(v_toBind_1318_);
lean_dec_ref(v_inst_1317_);
v_snd_1324_ = lean_ctor_get(v_____x_1322_, 1);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_____x_1322_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v_____x_1322_, 0);
lean_dec(v_unused_1341_);
v___x_1326_ = v_____x_1322_;
v_isShared_1327_ = v_isSharedCheck_1340_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_snd_1324_);
lean_dec(v_____x_1322_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1340_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1339_; 
v_a_1328_ = lean_ctor_get(v_fst_1323_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_fst_1323_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1330_ = v_fst_1323_;
v_isShared_1331_ = v_isSharedCheck_1339_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v_fst_1323_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1339_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1335_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1333_);
v___x_1335_ = v___x_1326_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_snd_1324_);
v___x_1335_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_apply_2(v_toPure_1316_, lean_box(0), v___x_1335_);
return v___x_1336_;
}
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v_snd_1343_; lean_object* v_added_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___f_1347_; lean_object* v___x_1348_; lean_object* v___x_4696__overap_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_a_1342_ = lean_ctor_get(v_fst_1323_, 0);
lean_inc(v_a_1342_);
lean_dec_ref(v_fst_1323_);
v_snd_1343_ = lean_ctor_get(v_____x_1322_, 1);
lean_inc(v_snd_1343_);
lean_dec_ref(v_____x_1322_);
v_added_1344_ = lean_ctor_get(v_a_1342_, 1);
lean_inc_ref(v_added_1344_);
lean_dec(v_a_1342_);
v___x_1345_ = lean_array_get_size(v_added_1344_);
lean_dec_ref(v_added_1344_);
v___x_1346_ = lean_unsigned_to_nat(1u);
lean_inc(v_toBind_1318_);
v___f_1347_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed), 8, 4);
lean_closure_set(v___f_1347_, 0, v_toPure_1316_);
lean_closure_set(v___f_1347_, 1, v___x_1346_);
lean_closure_set(v___f_1347_, 2, v_inst_1317_);
lean_closure_set(v___f_1347_, 3, v_toBind_1318_);
v___x_1348_ = lean_nat_sub(v___x_1345_, v___x_1346_);
v___x_4696__overap_1349_ = l___private_Init_While_0__Lean_Loop_forIn_loop(lean_box(0), lean_box(0), v___x_1319_, v___f_1347_, v___x_1348_);
lean_inc_ref(v_a_1320_);
v___x_1350_ = lean_apply_2(v___x_4696__overap_1349_, v_a_1320_, v_snd_1343_);
v___x_1351_ = lean_apply_4(v_toBind_1318_, lean_box(0), lean_box(0), v___x_1350_, v___f_1321_);
return v___x_1351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed(lean_object* v_toPure_1352_, lean_object* v_inst_1353_, lean_object* v_toBind_1354_, lean_object* v___x_1355_, lean_object* v_a_1356_, lean_object* v___f_1357_, lean_object* v_____x_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(v_toPure_1352_, v_inst_1353_, v_toBind_1354_, v___x_1355_, v_a_1356_, v___f_1357_, v_____x_1358_);
lean_dec_ref(v_a_1356_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(lean_object* v_inst_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v___f_1363_; lean_object* v___f_1364_; lean_object* v___f_1365_; lean_object* v___f_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___f_1373_; lean_object* v___f_1374_; lean_object* v___f_1375_; lean_object* v___f_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v_toApplicative_1384_; lean_object* v_toBind_1385_; lean_object* v_toPure_1386_; lean_object* v___f_1387_; lean_object* v___f_1388_; lean_object* v___f_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_inc_ref_n(v_inst_1360_, 7);
v___f_1363_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1363_, 0, v_inst_1360_);
v___f_1364_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1364_, 0, v_inst_1360_);
v___f_1365_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1365_, 0, v_inst_1360_);
v___f_1366_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1366_, 0, v_inst_1360_);
v___x_1367_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1367_, 0, lean_box(0));
lean_closure_set(v___x_1367_, 1, lean_box(0));
lean_closure_set(v___x_1367_, 2, v_inst_1360_);
v___x_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
lean_ctor_set(v___x_1368_, 1, v___f_1363_);
v___x_1369_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1369_, 0, lean_box(0));
lean_closure_set(v___x_1369_, 1, lean_box(0));
lean_closure_set(v___x_1369_, 2, v_inst_1360_);
v___x_1370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1368_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
lean_ctor_set(v___x_1370_, 2, v___f_1364_);
lean_ctor_set(v___x_1370_, 3, v___f_1365_);
lean_ctor_set(v___x_1370_, 4, v___f_1366_);
v___x_1371_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1371_, 0, lean_box(0));
lean_closure_set(v___x_1371_, 1, lean_box(0));
lean_closure_set(v___x_1371_, 2, v_inst_1360_);
v___x_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1370_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
lean_inc_ref_n(v___x_1372_, 6);
v___f_1373_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1373_, 0, v___x_1372_);
v___f_1374_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1374_, 0, v___x_1372_);
v___f_1375_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1375_, 0, v___x_1372_);
v___f_1376_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1376_, 0, v___x_1372_);
v___x_1377_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1377_, 0, lean_box(0));
lean_closure_set(v___x_1377_, 1, lean_box(0));
lean_closure_set(v___x_1377_, 2, v___x_1372_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
lean_ctor_set(v___x_1378_, 1, v___f_1373_);
v___x_1379_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1379_, 0, lean_box(0));
lean_closure_set(v___x_1379_, 1, lean_box(0));
lean_closure_set(v___x_1379_, 2, v___x_1372_);
v___x_1380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1378_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
lean_ctor_set(v___x_1380_, 2, v___f_1374_);
lean_ctor_set(v___x_1380_, 3, v___f_1375_);
lean_ctor_set(v___x_1380_, 4, v___f_1376_);
v___x_1381_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1381_, 0, lean_box(0));
lean_closure_set(v___x_1381_, 1, lean_box(0));
lean_closure_set(v___x_1381_, 2, v___x_1372_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = l_ReaderT_instMonad___redArg(v___x_1382_);
v_toApplicative_1384_ = lean_ctor_get(v_inst_1360_, 0);
v_toBind_1385_ = lean_ctor_get(v_inst_1360_, 1);
lean_inc_n(v_toBind_1385_, 3);
v_toPure_1386_ = lean_ctor_get(v_toApplicative_1384_, 1);
lean_inc_n(v_toPure_1386_, 4);
v___f_1387_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1387_, 0, v_toPure_1386_);
lean_inc_ref(v_a_1361_);
v___f_1388_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1388_, 0, v_toPure_1386_);
lean_closure_set(v___f_1388_, 1, v_inst_1360_);
lean_closure_set(v___f_1388_, 2, v_toBind_1385_);
lean_closure_set(v___f_1388_, 3, v___x_1383_);
lean_closure_set(v___f_1388_, 4, v_a_1361_);
lean_closure_set(v___f_1388_, 5, v___f_1387_);
v___f_1389_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1389_, 0, v_toPure_1386_);
lean_inc_ref(v_a_1362_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v_a_1362_);
lean_ctor_set(v___x_1390_, 1, v_a_1362_);
v___x_1391_ = lean_apply_2(v_toPure_1386_, lean_box(0), v___x_1390_);
v___x_1392_ = lean_apply_4(v_toBind_1385_, lean_box(0), lean_box(0), v___x_1391_, v___f_1389_);
v___x_1393_ = lean_apply_4(v_toBind_1385_, lean_box(0), lean_box(0), v___x_1392_, v___f_1388_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___boxed(lean_object* v_inst_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1394_, v_a_1395_, v_a_1396_);
lean_dec_ref(v_a_1395_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(lean_object* v_m_1398_, lean_object* v_inst_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1399_, v_a_1400_, v_a_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___boxed(lean_object* v_m_1403_, lean_object* v_inst_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(v_m_1403_, v_inst_1404_, v_a_1405_, v_a_1406_);
lean_dec_ref(v_a_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(lean_object* v_toApplicative_1408_, lean_object* v_inst_1409_, lean_object* v_a_1410_, lean_object* v_____x_1411_){
_start:
{
lean_object* v_fst_1412_; 
v_fst_1412_ = lean_ctor_get(v_____x_1411_, 0);
lean_inc(v_fst_1412_);
if (lean_obj_tag(v_fst_1412_) == 0)
{
lean_object* v_snd_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1430_; 
lean_dec_ref(v_inst_1409_);
v_snd_1413_ = lean_ctor_get(v_____x_1411_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_____x_1411_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; 
v_unused_1431_ = lean_ctor_get(v_____x_1411_, 0);
lean_dec(v_unused_1431_);
v___x_1415_ = v_____x_1411_;
v_isShared_1416_ = v_isSharedCheck_1430_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_snd_1413_);
lean_dec(v_____x_1411_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1430_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1429_; 
v_a_1417_ = lean_ctor_get(v_fst_1412_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_fst_1412_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1419_ = v_fst_1412_;
v_isShared_1420_ = v_isSharedCheck_1429_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v_fst_1412_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1429_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v_toPure_1421_; lean_object* v___x_1423_; 
v_toPure_1421_ = lean_ctor_get(v_toApplicative_1408_, 1);
lean_inc(v_toPure_1421_);
lean_dec_ref(v_toApplicative_1408_);
if (v_isShared_1420_ == 0)
{
v___x_1423_ = v___x_1419_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1417_);
v___x_1423_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1425_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1423_);
v___x_1425_ = v___x_1415_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_snd_1413_);
v___x_1425_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_apply_2(v_toPure_1421_, lean_box(0), v___x_1425_);
return v___x_1426_;
}
}
}
}
}
else
{
lean_object* v_a_1432_; uint8_t v_found_1433_; 
v_a_1432_ = lean_ctor_get(v_fst_1412_, 0);
lean_inc(v_a_1432_);
lean_dec_ref(v_fst_1412_);
v_found_1433_ = lean_ctor_get_uint8(v_a_1432_, sizeof(void*)*3);
lean_dec(v_a_1432_);
if (v_found_1433_ == 0)
{
lean_object* v_snd_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1444_; 
lean_dec_ref(v_inst_1409_);
v_snd_1434_ = lean_ctor_get(v_____x_1411_, 1);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_____x_1411_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; 
v_unused_1445_ = lean_ctor_get(v_____x_1411_, 0);
lean_dec(v_unused_1445_);
v___x_1436_ = v_____x_1411_;
v_isShared_1437_ = v_isSharedCheck_1444_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_snd_1434_);
lean_dec(v_____x_1411_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1444_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_toPure_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
v_toPure_1438_ = lean_ctor_get(v_toApplicative_1408_, 1);
lean_inc(v_toPure_1438_);
lean_dec_ref(v_toApplicative_1408_);
v___x_1439_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0));
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1439_);
v___x_1441_ = v___x_1436_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_snd_1434_);
v___x_1441_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_apply_2(v_toPure_1438_, lean_box(0), v___x_1441_);
return v___x_1442_;
}
}
}
else
{
lean_object* v_snd_1446_; lean_object* v___x_1447_; 
lean_dec_ref(v_toApplicative_1408_);
v_snd_1446_ = lean_ctor_get(v_____x_1411_, 1);
lean_inc(v_snd_1446_);
lean_dec_ref(v_____x_1411_);
v___x_1447_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1409_, v_a_1410_, v_snd_1446_);
return v___x_1447_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0___boxed(lean_object* v_toApplicative_1448_, lean_object* v_inst_1449_, lean_object* v_a_1450_, lean_object* v_____x_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(v_toApplicative_1448_, v_inst_1449_, v_a_1450_, v_____x_1451_);
lean_dec_ref(v_a_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2(lean_object* v_toApplicative_1453_, lean_object* v_toBind_1454_, lean_object* v___f_1455_, lean_object* v_____x_1456_){
_start:
{
lean_object* v_fst_1457_; 
v_fst_1457_ = lean_ctor_get(v_____x_1456_, 0);
if (lean_obj_tag(v_fst_1457_) == 0)
{
lean_object* v_toPure_1458_; lean_object* v___x_1459_; 
lean_dec(v___f_1455_);
lean_dec(v_toBind_1454_);
v_toPure_1458_ = lean_ctor_get(v_toApplicative_1453_, 1);
lean_inc(v_toPure_1458_);
lean_dec_ref(v_toApplicative_1453_);
v___x_1459_ = lean_apply_2(v_toPure_1458_, lean_box(0), v_____x_1456_);
return v___x_1459_;
}
else
{
lean_object* v_snd_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1472_; 
v_snd_1460_ = lean_ctor_get(v_____x_1456_, 1);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_____x_1456_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; 
v_unused_1473_ = lean_ctor_get(v_____x_1456_, 0);
lean_dec(v_unused_1473_);
v___x_1462_ = v_____x_1456_;
v_isShared_1463_ = v_isSharedCheck_1472_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_snd_1460_);
lean_dec(v_____x_1456_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1472_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v_toPure_1464_; lean_object* v___f_1465_; lean_object* v___x_1467_; 
v_toPure_1464_ = lean_ctor_get(v_toApplicative_1453_, 1);
lean_inc_n(v_toPure_1464_, 2);
lean_dec_ref(v_toApplicative_1453_);
v___f_1465_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1465_, 0, v_toPure_1464_);
lean_inc(v_snd_1460_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v_snd_1460_);
v___x_1467_ = v___x_1462_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_snd_1460_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_snd_1460_);
v___x_1467_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1468_ = lean_apply_2(v_toPure_1464_, lean_box(0), v___x_1467_);
lean_inc(v_toBind_1454_);
v___x_1469_ = lean_apply_4(v_toBind_1454_, lean_box(0), lean_box(0), v___x_1468_, v___f_1465_);
v___x_1470_ = lean_apply_4(v_toBind_1454_, lean_box(0), lean_box(0), v___x_1469_, v___f_1455_);
return v___x_1470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(lean_object* v_inst_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_toApplicative_1477_; lean_object* v_toBind_1478_; lean_object* v___f_1479_; lean_object* v___f_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v_toApplicative_1477_ = lean_ctor_get(v_inst_1474_, 0);
v_toBind_1478_ = lean_ctor_get(v_inst_1474_, 1);
lean_inc_n(v_toBind_1478_, 2);
lean_inc_ref(v_a_1475_);
lean_inc_ref(v_inst_1474_);
lean_inc_ref_n(v_toApplicative_1477_, 2);
v___f_1479_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1479_, 0, v_toApplicative_1477_);
lean_closure_set(v___f_1479_, 1, v_inst_1474_);
lean_closure_set(v___f_1479_, 2, v_a_1475_);
v___f_1480_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1480_, 0, v_toApplicative_1477_);
lean_closure_set(v___f_1480_, 1, v_toBind_1478_);
lean_closure_set(v___f_1480_, 2, v___f_1479_);
v___x_1481_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1474_, v_a_1475_, v_a_1476_);
v___x_1482_ = lean_apply_4(v_toBind_1478_, lean_box(0), lean_box(0), v___x_1481_, v___f_1480_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___boxed(lean_object* v_inst_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1483_, v_a_1484_, v_a_1485_);
lean_dec_ref(v_a_1484_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(lean_object* v_m_1487_, lean_object* v_inst_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1488_, v_a_1489_, v_a_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___boxed(lean_object* v_m_1492_, lean_object* v_inst_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(v_m_1492_, v_inst_1493_, v_a_1494_, v_a_1495_);
lean_dec_ref(v_a_1494_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__0(lean_object* v_toApplicative_1497_, lean_object* v_____x_1498_){
_start:
{
lean_object* v_snd_1499_; lean_object* v_fst_1500_; lean_object* v_cur_1501_; lean_object* v_numCalls_1502_; uint8_t v_found_1503_; uint8_t v___y_1505_; 
v_snd_1499_ = lean_ctor_get(v_____x_1498_, 1);
v_fst_1500_ = lean_ctor_get(v_____x_1498_, 0);
v_cur_1501_ = lean_ctor_get(v_snd_1499_, 0);
v_numCalls_1502_ = lean_ctor_get(v_snd_1499_, 2);
v_found_1503_ = lean_ctor_get_uint8(v_snd_1499_, sizeof(void*)*3);
if (v_found_1503_ == 0)
{
uint8_t v___x_1509_; 
v___x_1509_ = 0;
v___y_1505_ = v___x_1509_;
goto v___jp_1504_;
}
else
{
if (lean_obj_tag(v_fst_1500_) == 0)
{
uint8_t v___x_1510_; 
v___x_1510_ = 1;
v___y_1505_ = v___x_1510_;
goto v___jp_1504_;
}
else
{
uint8_t v___x_1511_; 
v___x_1511_ = 2;
v___y_1505_ = v___x_1511_;
goto v___jp_1504_;
}
}
v___jp_1504_:
{
lean_object* v_toPure_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v_toPure_1506_ = lean_ctor_get(v_toApplicative_1497_, 1);
lean_inc(v_toPure_1506_);
lean_dec_ref(v_toApplicative_1497_);
lean_inc(v_numCalls_1502_);
lean_inc_ref(v_cur_1501_);
v___x_1507_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1507_, 0, v_cur_1501_);
lean_ctor_set(v___x_1507_, 1, v_numCalls_1502_);
lean_ctor_set_uint8(v___x_1507_, sizeof(void*)*2, v___y_1505_);
v___x_1508_ = lean_apply_2(v_toPure_1506_, lean_box(0), v___x_1507_);
return v___x_1508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed(lean_object* v_toApplicative_1512_, lean_object* v_____x_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_Util_ParamMinimizer_search___redArg___lam__0(v_toApplicative_1512_, v_____x_1513_);
lean_dec_ref(v_____x_1513_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__1(lean_object* v_initialMask_1517_, lean_object* v_test_1518_, lean_object* v_maxCalls_1519_, lean_object* v_inst_1520_, lean_object* v_toBind_1521_, lean_object* v___f_1522_, lean_object* v_toApplicative_1523_, uint8_t v_____do__lift_1524_){
_start:
{
if (v_____do__lift_1524_ == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec_ref(v_toApplicative_1523_);
lean_inc_ref(v_initialMask_1517_);
v___x_1525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1525_, 0, v_initialMask_1517_);
lean_ctor_set(v___x_1525_, 1, v_test_1518_);
lean_ctor_set(v___x_1525_, 2, v_maxCalls_1519_);
v___x_1526_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0));
v___x_1527_ = lean_unsigned_to_nat(1u);
v___x_1528_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1528_, 0, v_initialMask_1517_);
lean_ctor_set(v___x_1528_, 1, v___x_1526_);
lean_ctor_set(v___x_1528_, 2, v___x_1527_);
lean_ctor_set_uint8(v___x_1528_, sizeof(void*)*3, v_____do__lift_1524_);
v___x_1529_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1520_, v___x_1525_, v___x_1528_);
lean_dec_ref(v___x_1525_);
v___x_1530_ = lean_apply_4(v_toBind_1521_, lean_box(0), lean_box(0), v___x_1529_, v___f_1522_);
return v___x_1530_;
}
else
{
lean_object* v_toPure_1531_; uint8_t v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_dec(v___f_1522_);
lean_dec(v_toBind_1521_);
lean_dec_ref(v_inst_1520_);
lean_dec(v_maxCalls_1519_);
lean_dec(v_test_1518_);
v_toPure_1531_ = lean_ctor_get(v_toApplicative_1523_, 1);
lean_inc(v_toPure_1531_);
lean_dec_ref(v_toApplicative_1523_);
v___x_1532_ = 2;
v___x_1533_ = lean_unsigned_to_nat(1u);
v___x_1534_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1534_, 0, v_initialMask_1517_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
lean_ctor_set_uint8(v___x_1534_, sizeof(void*)*2, v___x_1532_);
v___x_1535_ = lean_apply_2(v_toPure_1531_, lean_box(0), v___x_1534_);
return v___x_1535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed(lean_object* v_initialMask_1536_, lean_object* v_test_1537_, lean_object* v_maxCalls_1538_, lean_object* v_inst_1539_, lean_object* v_toBind_1540_, lean_object* v___f_1541_, lean_object* v_toApplicative_1542_, lean_object* v_____do__lift_1543_){
_start:
{
uint8_t v_____do__lift_277__boxed_1544_; lean_object* v_res_1545_; 
v_____do__lift_277__boxed_1544_ = lean_unbox(v_____do__lift_1543_);
v_res_1545_ = l_Lean_Util_ParamMinimizer_search___redArg___lam__1(v_initialMask_1536_, v_test_1537_, v_maxCalls_1538_, v_inst_1539_, v_toBind_1540_, v___f_1541_, v_toApplicative_1542_, v_____do__lift_277__boxed_1544_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg(lean_object* v_inst_1546_, lean_object* v_initialMask_1547_, lean_object* v_test_1548_, lean_object* v_maxCalls_1549_){
_start:
{
lean_object* v_toApplicative_1550_; lean_object* v_toBind_1551_; lean_object* v___f_1552_; lean_object* v___f_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v_toApplicative_1550_ = lean_ctor_get(v_inst_1546_, 0);
lean_inc_ref_n(v_toApplicative_1550_, 2);
v_toBind_1551_ = lean_ctor_get(v_inst_1546_, 1);
lean_inc_n(v_toBind_1551_, 2);
v___f_1552_ = lean_alloc_closure((void*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1552_, 0, v_toApplicative_1550_);
lean_inc(v_test_1548_);
lean_inc_ref(v_initialMask_1547_);
v___f_1553_ = lean_alloc_closure((void*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1553_, 0, v_initialMask_1547_);
lean_closure_set(v___f_1553_, 1, v_test_1548_);
lean_closure_set(v___f_1553_, 2, v_maxCalls_1549_);
lean_closure_set(v___f_1553_, 3, v_inst_1546_);
lean_closure_set(v___f_1553_, 4, v_toBind_1551_);
lean_closure_set(v___f_1553_, 5, v___f_1552_);
lean_closure_set(v___f_1553_, 6, v_toApplicative_1550_);
v___x_1554_ = lean_apply_1(v_test_1548_, v_initialMask_1547_);
v___x_1555_ = lean_apply_4(v_toBind_1551_, lean_box(0), lean_box(0), v___x_1554_, v___f_1553_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search(lean_object* v_m_1556_, lean_object* v_inst_1557_, lean_object* v_initialMask_1558_, lean_object* v_test_1559_, lean_object* v_maxCalls_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_Util_ParamMinimizer_search___redArg(v_inst_1557_, v_initialMask_1558_, v_test_1559_, v_maxCalls_1560_);
return v___x_1561_;
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_ParamMinimizer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
