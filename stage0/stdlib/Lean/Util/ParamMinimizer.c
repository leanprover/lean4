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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
static const lean_ctor_object l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0 = (const lean_object*)&l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0 = (const lean_object*)&l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_7310__boxed_394_; lean_object* v_res_395_; 
v___x_7310__boxed_394_ = lean_unbox(v___x_392_);
v_res_395_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0(v_toPure_391_, v___x_7310__boxed_394_, v_____x_393_);
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
lean_inc(v_toBind_435_);
v___x_464_ = lean_apply_4(v_toBind_435_, lean_box(0), lean_box(0), v___x_461_, v___f_463_);
lean_inc(v_toBind_435_);
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
lean_inc(v_toPure_480_);
v___f_508_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__4), 5, 4);
lean_closure_set(v___f_508_, 0, v_toPure_480_);
lean_closure_set(v___f_508_, 1, v_a_507_);
lean_closure_set(v___f_508_, 2, v_toBind_481_);
lean_closure_set(v___f_508_, 3, v___f_482_);
lean_inc(v_toPure_480_);
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
lean_dec_ref(v_a_519_);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(lean_object* v_toPure_563_, lean_object* v_inst_564_, lean_object* v_toBind_565_, lean_object* v_a_566_, lean_object* v_maxCalls_567_, lean_object* v_____x_568_){
_start:
{
lean_object* v_fst_569_; lean_object* v_snd_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_623_; 
v_fst_569_ = lean_ctor_get(v_____x_568_, 0);
v_snd_570_ = lean_ctor_get(v_____x_568_, 1);
v_isSharedCheck_623_ = !lean_is_exclusive(v_____x_568_);
if (v_isSharedCheck_623_ == 0)
{
v___x_572_ = v_____x_568_;
v_isShared_573_ = v_isSharedCheck_623_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_snd_570_);
lean_inc(v_fst_569_);
lean_dec(v_____x_568_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_623_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
uint8_t v___y_575_; 
if (lean_obj_tag(v_fst_569_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_617_; 
lean_del_object(v___x_572_);
lean_dec_ref(v_a_566_);
lean_dec(v_toBind_565_);
lean_dec_ref(v_inst_564_);
v_a_608_ = lean_ctor_get(v_fst_569_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v_fst_569_);
if (v_isSharedCheck_617_ == 0)
{
v___x_610_ = v_fst_569_;
v_isShared_611_ = v_isSharedCheck_617_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v_fst_569_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_617_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_616_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v_snd_570_);
v___x_615_ = lean_apply_2(v_toPure_563_, lean_box(0), v___x_614_);
return v___x_615_;
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_a_618_ = lean_ctor_get(v_fst_569_, 0);
lean_inc(v_a_618_);
lean_dec_ref(v_fst_569_);
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = lean_nat_dec_lt(v___x_619_, v_maxCalls_567_);
if (v___x_620_ == 0)
{
lean_dec(v_a_618_);
v___y_575_ = v___x_620_;
goto v___jp_574_;
}
else
{
lean_object* v_numCalls_621_; uint8_t v___x_622_; 
v_numCalls_621_ = lean_ctor_get(v_a_618_, 2);
lean_inc(v_numCalls_621_);
lean_dec(v_a_618_);
v___x_622_ = lean_nat_dec_le(v_maxCalls_567_, v_numCalls_621_);
lean_dec(v_numCalls_621_);
v___y_575_ = v___x_622_;
goto v___jp_574_;
}
}
v___jp_574_:
{
if (v___y_575_ == 0)
{
lean_object* v_cur_576_; lean_object* v_added_577_; lean_object* v_numCalls_578_; uint8_t v_found_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_602_; 
v_cur_576_ = lean_ctor_get(v_snd_570_, 0);
v_added_577_ = lean_ctor_get(v_snd_570_, 1);
v_numCalls_578_ = lean_ctor_get(v_snd_570_, 2);
v_found_579_ = lean_ctor_get_uint8(v_snd_570_, sizeof(void*)*3);
v_isSharedCheck_602_ = !lean_is_exclusive(v_snd_570_);
if (v_isSharedCheck_602_ == 0)
{
v___x_581_ = v_snd_570_;
v_isShared_582_ = v_isSharedCheck_602_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_numCalls_578_);
lean_inc(v_added_577_);
lean_inc(v_cur_576_);
lean_dec(v_snd_570_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_602_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___f_585_; lean_object* v___f_586_; lean_object* v___f_587_; lean_object* v___f_588_; lean_object* v___f_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_583_ = 1;
v___x_584_ = lean_box(v___x_583_);
lean_inc(v_toPure_563_);
v___f_585_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_585_, 0, v_toPure_563_);
lean_closure_set(v___f_585_, 1, v___x_584_);
lean_inc(v_toBind_565_);
lean_inc(v_toPure_563_);
v___f_586_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__1), 5, 4);
lean_closure_set(v___f_586_, 0, v_toPure_563_);
lean_closure_set(v___f_586_, 1, v_inst_564_);
lean_closure_set(v___f_586_, 2, v_toBind_565_);
lean_closure_set(v___f_586_, 3, v___f_585_);
lean_inc(v_toBind_565_);
lean_inc(v_toPure_563_);
v___f_587_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__6), 4, 3);
lean_closure_set(v___f_587_, 0, v_toPure_563_);
lean_closure_set(v___f_587_, 1, v_toBind_565_);
lean_closure_set(v___f_587_, 2, v___f_586_);
lean_inc(v_toBind_565_);
lean_inc(v_toPure_563_);
v___f_588_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7), 5, 4);
lean_closure_set(v___f_588_, 0, v_toPure_563_);
lean_closure_set(v___f_588_, 1, v_a_566_);
lean_closure_set(v___f_588_, 2, v_toBind_565_);
lean_closure_set(v___f_588_, 3, v___f_587_);
lean_inc(v_toPure_563_);
v___f_589_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_589_, 0, v_toPure_563_);
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
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 1, v___x_594_);
lean_ctor_set(v___x_572_, 0, v___x_590_);
v___x_596_ = v___x_572_;
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
v___x_597_ = lean_apply_2(v_toPure_563_, lean_box(0), v___x_596_);
lean_inc(v_toBind_565_);
v___x_598_ = lean_apply_4(v_toBind_565_, lean_box(0), lean_box(0), v___x_597_, v___f_589_);
v___x_599_ = lean_apply_4(v_toBind_565_, lean_box(0), lean_box(0), v___x_598_, v___f_588_);
return v___x_599_;
}
}
}
}
else
{
lean_object* v___x_603_; lean_object* v___x_605_; 
lean_dec_ref(v_a_566_);
lean_dec(v_toBind_565_);
lean_dec_ref(v_inst_564_);
v___x_603_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0));
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_603_);
v___x_605_ = v___x_572_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_snd_570_);
v___x_605_ = v_reuseFailAlloc_607_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; 
v___x_606_ = lean_apply_2(v_toPure_563_, lean_box(0), v___x_605_);
return v___x_606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed(lean_object* v_toPure_624_, lean_object* v_inst_625_, lean_object* v_toBind_626_, lean_object* v_a_627_, lean_object* v_maxCalls_628_, lean_object* v_____x_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(v_toPure_624_, v_inst_625_, v_toBind_626_, v_a_627_, v_maxCalls_628_, v_____x_629_);
lean_dec(v_maxCalls_628_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(lean_object* v_toPure_631_, lean_object* v_inst_632_, lean_object* v_toBind_633_, lean_object* v_a_634_, lean_object* v_____x_635_){
_start:
{
lean_object* v_fst_636_; 
v_fst_636_ = lean_ctor_get(v_____x_635_, 0);
lean_inc(v_fst_636_);
if (lean_obj_tag(v_fst_636_) == 0)
{
lean_object* v_snd_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_653_; 
lean_dec_ref(v_a_634_);
lean_dec(v_toBind_633_);
lean_dec_ref(v_inst_632_);
v_snd_637_ = lean_ctor_get(v_____x_635_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v_____x_635_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v_____x_635_, 0);
lean_dec(v_unused_654_);
v___x_639_ = v_____x_635_;
v_isShared_640_ = v_isSharedCheck_653_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_snd_637_);
lean_dec(v_____x_635_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_653_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_652_; 
v_a_641_ = lean_ctor_get(v_fst_636_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v_fst_636_);
if (v_isSharedCheck_652_ == 0)
{
v___x_643_ = v_fst_636_;
v_isShared_644_ = v_isSharedCheck_652_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v_fst_636_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_652_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_651_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_648_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_646_);
v___x_648_ = v___x_639_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_snd_637_);
v___x_648_ = v_reuseFailAlloc_650_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; 
v___x_649_ = lean_apply_2(v_toPure_631_, lean_box(0), v___x_648_);
return v___x_649_;
}
}
}
}
}
else
{
lean_object* v_a_655_; lean_object* v_snd_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_669_; 
v_a_655_ = lean_ctor_get(v_fst_636_, 0);
lean_inc(v_a_655_);
lean_dec_ref(v_fst_636_);
v_snd_656_ = lean_ctor_get(v_____x_635_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_____x_635_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v_____x_635_, 0);
lean_dec(v_unused_670_);
v___x_658_ = v_____x_635_;
v_isShared_659_ = v_isSharedCheck_669_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_snd_656_);
lean_dec(v_____x_635_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_669_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v_maxCalls_660_; lean_object* v___f_661_; lean_object* v___f_662_; lean_object* v___x_664_; 
v_maxCalls_660_ = lean_ctor_get(v_a_655_, 2);
lean_inc(v_maxCalls_660_);
lean_dec(v_a_655_);
lean_inc(v_toBind_633_);
lean_inc(v_toPure_631_);
v___f_661_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_661_, 0, v_toPure_631_);
lean_closure_set(v___f_661_, 1, v_inst_632_);
lean_closure_set(v___f_661_, 2, v_toBind_633_);
lean_closure_set(v___f_661_, 3, v_a_634_);
lean_closure_set(v___f_661_, 4, v_maxCalls_660_);
lean_inc(v_toPure_631_);
v___f_662_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_662_, 0, v_toPure_631_);
lean_inc(v_snd_656_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v_snd_656_);
v___x_664_ = v___x_658_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_snd_656_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_snd_656_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = lean_apply_2(v_toPure_631_, lean_box(0), v___x_664_);
lean_inc(v_toBind_633_);
v___x_666_ = lean_apply_4(v_toBind_633_, lean_box(0), lean_box(0), v___x_665_, v___f_662_);
v___x_667_ = lean_apply_4(v_toBind_633_, lean_box(0), lean_box(0), v___x_666_, v___f_661_);
return v___x_667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(lean_object* v_inst_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_toApplicative_674_; lean_object* v_toBind_675_; lean_object* v_toPure_676_; lean_object* v___f_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v_toApplicative_674_ = lean_ctor_get(v_inst_671_, 0);
v_toBind_675_ = lean_ctor_get(v_inst_671_, 1);
lean_inc(v_toBind_675_);
v_toPure_676_ = lean_ctor_get(v_toApplicative_674_, 1);
lean_inc(v_toPure_676_);
lean_inc_ref(v_a_672_);
lean_inc(v_toBind_675_);
lean_inc(v_toPure_676_);
v___f_677_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10), 5, 4);
lean_closure_set(v___f_677_, 0, v_toPure_676_);
lean_closure_set(v___f_677_, 1, v_inst_671_);
lean_closure_set(v___f_677_, 2, v_toBind_675_);
lean_closure_set(v___f_677_, 3, v_a_672_);
v___x_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_678_, 0, v_a_672_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v_a_673_);
v___x_680_ = lean_apply_2(v_toPure_676_, lean_box(0), v___x_679_);
v___x_681_ = lean_apply_4(v_toBind_675_, lean_box(0), lean_box(0), v___x_680_, v___f_677_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(lean_object* v_m_682_, lean_object* v_inst_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_683_, v_a_684_, v_a_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0(lean_object* v_toPure_687_, lean_object* v_____x_688_){
_start:
{
lean_object* v_fst_689_; 
v_fst_689_ = lean_ctor_get(v_____x_688_, 0);
lean_inc(v_fst_689_);
if (lean_obj_tag(v_fst_689_) == 0)
{
lean_object* v_snd_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_706_; 
v_snd_690_ = lean_ctor_get(v_____x_688_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v_____x_688_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v_____x_688_, 0);
lean_dec(v_unused_707_);
v___x_692_ = v_____x_688_;
v_isShared_693_ = v_isSharedCheck_706_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_snd_690_);
lean_dec(v_____x_688_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_706_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_705_; 
v_a_694_ = lean_ctor_get(v_fst_689_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_fst_689_);
if (v_isSharedCheck_705_ == 0)
{
v___x_696_ = v_fst_689_;
v_isShared_697_ = v_isSharedCheck_705_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v_fst_689_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_705_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_704_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_701_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_699_);
v___x_701_ = v___x_692_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_snd_690_);
v___x_701_ = v_reuseFailAlloc_703_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; 
v___x_702_ = lean_apply_2(v_toPure_687_, lean_box(0), v___x_701_);
return v___x_702_;
}
}
}
}
}
else
{
lean_object* v_snd_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_724_; 
v_snd_708_ = lean_ctor_get(v_____x_688_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_____x_688_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v_____x_688_, 0);
lean_dec(v_unused_725_);
v___x_710_ = v_____x_688_;
v_isShared_711_ = v_isSharedCheck_724_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_snd_708_);
lean_dec(v_____x_688_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_724_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_723_; 
v_a_712_ = lean_ctor_get(v_fst_689_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v_fst_689_);
if (v_isSharedCheck_723_ == 0)
{
v___x_714_ = v_fst_689_;
v_isShared_715_ = v_isSharedCheck_723_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v_fst_689_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_723_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_722_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_717_);
v___x_719_ = v___x_710_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_snd_708_);
v___x_719_ = v_reuseFailAlloc_721_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_720_; 
v___x_720_ = lean_apply_2(v_toPure_687_, lean_box(0), v___x_719_);
return v___x_720_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1(lean_object* v_toPure_726_, lean_object* v___x_727_, lean_object* v_____x_728_){
_start:
{
lean_object* v_fst_729_; 
v_fst_729_ = lean_ctor_get(v_____x_728_, 0);
lean_inc(v_fst_729_);
if (lean_obj_tag(v_fst_729_) == 0)
{
lean_object* v_snd_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_746_; 
v_snd_730_ = lean_ctor_get(v_____x_728_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_____x_728_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; 
v_unused_747_ = lean_ctor_get(v_____x_728_, 0);
lean_dec(v_unused_747_);
v___x_732_ = v_____x_728_;
v_isShared_733_ = v_isSharedCheck_746_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_snd_730_);
lean_dec(v_____x_728_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_746_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_745_; 
v_a_734_ = lean_ctor_get(v_fst_729_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v_fst_729_);
if (v_isSharedCheck_745_ == 0)
{
v___x_736_ = v_fst_729_;
v_isShared_737_ = v_isSharedCheck_745_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v_fst_729_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_745_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_744_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_741_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_739_);
v___x_741_ = v___x_732_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_snd_730_);
v___x_741_ = v_reuseFailAlloc_743_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; 
v___x_742_ = lean_apply_2(v_toPure_726_, lean_box(0), v___x_741_);
return v___x_742_;
}
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_775_; 
v_a_748_ = lean_ctor_get(v_fst_729_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v_fst_729_);
if (v_isSharedCheck_775_ == 0)
{
v___x_750_ = v_fst_729_;
v_isShared_751_ = v_isSharedCheck_775_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v_fst_729_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_775_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v_fst_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_773_; 
v_fst_752_ = lean_ctor_get(v_a_748_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v_a_748_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_a_748_, 1);
lean_dec(v_unused_774_);
v___x_754_ = v_a_748_;
v_isShared_755_ = v_isSharedCheck_773_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_fst_752_);
lean_dec(v_a_748_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_773_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
if (lean_obj_tag(v_fst_752_) == 0)
{
lean_object* v_snd_756_; lean_object* v___x_758_; 
v_snd_756_ = lean_ctor_get(v_____x_728_, 1);
lean_inc(v_snd_756_);
lean_dec_ref(v_____x_728_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_727_);
v___x_758_ = v___x_750_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_727_);
v___x_758_ = v_reuseFailAlloc_763_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_760_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v_snd_756_);
lean_ctor_set(v___x_754_, 0, v___x_758_);
v___x_760_ = v___x_754_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_snd_756_);
v___x_760_ = v_reuseFailAlloc_762_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; 
v___x_761_ = lean_apply_2(v_toPure_726_, lean_box(0), v___x_760_);
return v___x_761_;
}
}
}
else
{
lean_object* v_snd_764_; lean_object* v_val_765_; lean_object* v___x_767_; 
v_snd_764_ = lean_ctor_get(v_____x_728_, 1);
lean_inc(v_snd_764_);
lean_dec_ref(v_____x_728_);
v_val_765_ = lean_ctor_get(v_fst_752_, 0);
lean_inc(v_val_765_);
lean_dec_ref(v_fst_752_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v_val_765_);
v___x_767_ = v___x_750_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_val_765_);
v___x_767_ = v_reuseFailAlloc_772_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v_snd_764_);
lean_ctor_set(v___x_754_, 0, v___x_767_);
v___x_769_ = v___x_754_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_snd_764_);
v___x_769_ = v_reuseFailAlloc_771_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_770_; 
v___x_770_ = lean_apply_2(v_toPure_726_, lean_box(0), v___x_769_);
return v___x_770_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2(lean_object* v_toPure_776_, lean_object* v___x_777_, lean_object* v___x_778_, lean_object* v_____x_779_){
_start:
{
lean_object* v_fst_780_; 
v_fst_780_ = lean_ctor_get(v_____x_779_, 0);
lean_inc(v_fst_780_);
if (lean_obj_tag(v_fst_780_) == 0)
{
lean_object* v_snd_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_797_; 
lean_dec_ref(v___x_777_);
v_snd_781_ = lean_ctor_get(v_____x_779_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v_____x_779_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; 
v_unused_798_ = lean_ctor_get(v_____x_779_, 0);
lean_dec(v_unused_798_);
v___x_783_ = v_____x_779_;
v_isShared_784_ = v_isSharedCheck_797_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_snd_781_);
lean_dec(v_____x_779_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_797_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_796_; 
v_a_785_ = lean_ctor_get(v_fst_780_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_fst_780_);
if (v_isSharedCheck_796_ == 0)
{
v___x_787_ = v_fst_780_;
v_isShared_788_ = v_isSharedCheck_796_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v_fst_780_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_796_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_795_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_792_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_790_);
v___x_792_ = v___x_783_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_snd_781_);
v___x_792_ = v_reuseFailAlloc_794_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; 
v___x_793_ = lean_apply_2(v_toPure_776_, lean_box(0), v___x_792_);
return v___x_793_;
}
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_834_; 
v_a_799_ = lean_ctor_get(v_fst_780_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v_fst_780_);
if (v_isSharedCheck_834_ == 0)
{
v___x_801_ = v_fst_780_;
v_isShared_802_ = v_isSharedCheck_834_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v_fst_780_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_834_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
uint8_t v___x_803_; 
v___x_803_ = lean_unbox(v_a_799_);
lean_dec(v_a_799_);
if (v___x_803_ == 0)
{
lean_object* v_snd_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_816_; 
v_snd_804_ = lean_ctor_get(v_____x_779_, 1);
v_isSharedCheck_816_ = !lean_is_exclusive(v_____x_779_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v_____x_779_, 0);
lean_dec(v_unused_817_);
v___x_806_ = v_____x_779_;
v_isShared_807_ = v_isSharedCheck_816_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_snd_804_);
lean_dec(v_____x_779_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_816_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_777_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_808_);
v___x_810_ = v___x_801_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_815_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_812_; 
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_810_);
v___x_812_ = v___x_806_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_snd_804_);
v___x_812_ = v_reuseFailAlloc_814_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; 
v___x_813_ = lean_apply_2(v_toPure_776_, lean_box(0), v___x_812_);
return v___x_813_;
}
}
}
}
else
{
lean_object* v_snd_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref(v___x_777_);
v_snd_818_ = lean_ctor_get(v_____x_779_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v_____x_779_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v_____x_779_, 0);
lean_dec(v_unused_833_);
v___x_820_ = v_____x_779_;
v_isShared_821_ = v_isSharedCheck_832_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_snd_818_);
lean_dec(v_____x_779_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_832_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_778_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v___x_778_);
lean_ctor_set(v___x_820_, 0, v___x_822_);
v___x_824_ = v___x_820_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_778_);
v___x_824_ = v_reuseFailAlloc_831_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_825_);
v___x_827_ = v___x_801_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_830_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v_snd_818_);
v___x_829_ = lean_apply_2(v_toPure_776_, lean_box(0), v___x_828_);
return v___x_829_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(lean_object* v_inst_835_, lean_object* v_toBind_836_, lean_object* v___f_837_, lean_object* v_____r_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_835_, v___y_839_, v___y_840_);
v___x_842_ = lean_apply_4(v_toBind_836_, lean_box(0), lean_box(0), v___x_841_, v___f_837_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(lean_object* v_toPure_843_, lean_object* v_next_844_, lean_object* v_G_845_, lean_object* v___y_846_, lean_object* v_____x_847_){
_start:
{
lean_object* v_fst_848_; 
v_fst_848_ = lean_ctor_get(v_____x_847_, 0);
lean_inc(v_fst_848_);
if (lean_obj_tag(v_fst_848_) == 0)
{
lean_object* v_snd_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_865_; 
lean_dec_ref(v___y_846_);
lean_dec(v_G_845_);
v_snd_849_ = lean_ctor_get(v_____x_847_, 1);
v_isSharedCheck_865_ = !lean_is_exclusive(v_____x_847_);
if (v_isSharedCheck_865_ == 0)
{
lean_object* v_unused_866_; 
v_unused_866_ = lean_ctor_get(v_____x_847_, 0);
lean_dec(v_unused_866_);
v___x_851_ = v_____x_847_;
v_isShared_852_ = v_isSharedCheck_865_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_snd_849_);
lean_dec(v_____x_847_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_865_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_864_; 
v_a_853_ = lean_ctor_get(v_fst_848_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v_fst_848_);
if (v_isSharedCheck_864_ == 0)
{
v___x_855_ = v_fst_848_;
v_isShared_856_ = v_isSharedCheck_864_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v_fst_848_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_864_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_863_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_860_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_858_);
v___x_860_ = v___x_851_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_snd_849_);
v___x_860_ = v_reuseFailAlloc_862_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; 
v___x_861_ = lean_apply_2(v_toPure_843_, lean_box(0), v___x_860_);
return v___x_861_;
}
}
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_890_; 
v_a_867_ = lean_ctor_get(v_fst_848_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v_fst_848_);
if (v_isSharedCheck_890_ == 0)
{
v___x_869_ = v_fst_848_;
v_isShared_870_ = v_isSharedCheck_890_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v_fst_848_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_890_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
if (lean_obj_tag(v_a_867_) == 0)
{
lean_object* v_snd_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_883_; 
lean_dec_ref(v___y_846_);
lean_dec(v_G_845_);
v_snd_871_ = lean_ctor_get(v_____x_847_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v_____x_847_);
if (v_isSharedCheck_883_ == 0)
{
lean_object* v_unused_884_; 
v_unused_884_ = lean_ctor_get(v_____x_847_, 0);
lean_dec(v_unused_884_);
v___x_873_ = v_____x_847_;
v_isShared_874_ = v_isSharedCheck_883_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_snd_871_);
lean_dec(v_____x_847_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_883_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v_a_875_; lean_object* v___x_877_; 
v_a_875_ = lean_ctor_get(v_a_867_, 0);
lean_inc(v_a_875_);
lean_dec_ref(v_a_867_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v_a_875_);
v___x_877_ = v___x_869_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_875_);
v___x_877_ = v_reuseFailAlloc_882_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_879_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_877_);
v___x_879_ = v___x_873_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_snd_871_);
v___x_879_ = v_reuseFailAlloc_881_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_880_; 
v___x_880_ = lean_apply_2(v_toPure_843_, lean_box(0), v___x_879_);
return v___x_880_;
}
}
}
}
else
{
lean_object* v_snd_885_; lean_object* v_a_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_del_object(v___x_869_);
lean_dec(v_toPure_843_);
v_snd_885_ = lean_ctor_get(v_____x_847_, 1);
lean_inc(v_snd_885_);
lean_dec_ref(v_____x_847_);
v_a_886_ = lean_ctor_get(v_a_867_, 0);
lean_inc(v_a_886_);
lean_dec_ref(v_a_867_);
v___x_887_ = lean_unsigned_to_nat(1u);
v___x_888_ = lean_nat_add(v_next_844_, v___x_887_);
v___x_889_ = lean_apply_6(v_G_845_, v___x_888_, v_a_886_, lean_box(0), lean_box(0), v___y_846_, v_snd_885_);
return v___x_889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed(lean_object* v_toPure_891_, lean_object* v_next_892_, lean_object* v_G_893_, lean_object* v___y_894_, lean_object* v_____x_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(v_toPure_891_, v_next_892_, v_G_893_, v___y_894_, v_____x_895_);
lean_dec(v_next_892_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(lean_object* v_toPure_897_, lean_object* v___f_898_, lean_object* v___y_899_, lean_object* v_____x_900_){
_start:
{
lean_object* v_fst_901_; 
v_fst_901_ = lean_ctor_get(v_____x_900_, 0);
lean_inc(v_fst_901_);
if (lean_obj_tag(v_fst_901_) == 0)
{
lean_object* v_snd_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v___y_899_);
lean_dec(v___f_898_);
v_snd_902_ = lean_ctor_get(v_____x_900_, 1);
v_isSharedCheck_918_ = !lean_is_exclusive(v_____x_900_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v_____x_900_, 0);
lean_dec(v_unused_919_);
v___x_904_ = v_____x_900_;
v_isShared_905_ = v_isSharedCheck_918_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_snd_902_);
lean_dec(v_____x_900_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_918_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_917_; 
v_a_906_ = lean_ctor_get(v_fst_901_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v_fst_901_);
if (v_isSharedCheck_917_ == 0)
{
v___x_908_ = v_fst_901_;
v_isShared_909_ = v_isSharedCheck_917_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v_fst_901_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_917_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_916_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_913_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_911_);
v___x_913_ = v___x_904_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_snd_902_);
v___x_913_ = v_reuseFailAlloc_915_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; 
v___x_914_ = lean_apply_2(v_toPure_897_, lean_box(0), v___x_913_);
return v___x_914_;
}
}
}
}
}
else
{
lean_object* v_snd_920_; lean_object* v_a_921_; lean_object* v___x_922_; 
lean_dec(v_toPure_897_);
v_snd_920_ = lean_ctor_get(v_____x_900_, 1);
lean_inc(v_snd_920_);
lean_dec_ref(v_____x_900_);
v_a_921_ = lean_ctor_get(v_fst_901_, 0);
lean_inc(v_a_921_);
lean_dec_ref(v_fst_901_);
v___x_922_ = lean_apply_3(v___f_898_, v_a_921_, v___y_899_, v_snd_920_);
return v___x_922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(lean_object* v___x_923_, lean_object* v_toPure_924_, lean_object* v_toBind_925_, lean_object* v___f_926_, lean_object* v_initialMask_927_, lean_object* v___f_928_, lean_object* v_inst_929_, lean_object* v___x_930_, lean_object* v_next_931_, lean_object* v_acc_932_, lean_object* v_h_933_, lean_object* v_G_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
uint8_t v___x_937_; 
v___x_937_ = lean_nat_dec_lt(v_next_931_, v___x_923_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec_ref(v___y_935_);
lean_dec(v_G_934_);
lean_dec(v_next_931_);
lean_dec_ref(v_inst_929_);
lean_dec(v___f_928_);
lean_dec(v___f_926_);
lean_dec(v_toBind_925_);
v___x_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_938_, 0, v_acc_932_);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___y_936_);
v___x_940_ = lean_apply_2(v_toPure_924_, lean_box(0), v___x_939_);
return v___x_940_;
}
else
{
lean_object* v___f_941_; lean_object* v___y_943_; lean_object* v___x_946_; uint8_t v___x_947_; 
lean_dec_ref(v_acc_932_);
lean_inc_ref(v___y_935_);
lean_inc(v_next_931_);
lean_inc(v_toPure_924_);
v___f_941_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_941_, 0, v_toPure_924_);
lean_closure_set(v___f_941_, 1, v_next_931_);
lean_closure_set(v___f_941_, 2, v_G_934_);
lean_closure_set(v___f_941_, 3, v___y_935_);
v___x_946_ = lean_array_fget_borrowed(v_initialMask_927_, v_next_931_);
v___x_947_ = lean_unbox(v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___f_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___f_948_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5), 4, 3);
lean_closure_set(v___f_948_, 0, v_toPure_924_);
lean_closure_set(v___f_948_, 1, v___f_928_);
lean_closure_set(v___f_948_, 2, v___y_935_);
v___x_949_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(v_next_931_, v_inst_929_, v___y_936_);
lean_inc(v_toBind_925_);
v___x_950_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_949_, v___f_948_);
v___y_943_ = v___x_950_;
goto v___jp_942_;
}
else
{
lean_object* v___x_951_; 
lean_dec(v_next_931_);
lean_dec_ref(v_inst_929_);
lean_dec(v_toPure_924_);
v___x_951_ = lean_apply_3(v___f_928_, v___x_930_, v___y_935_, v___y_936_);
v___y_943_ = v___x_951_;
goto v___jp_942_;
}
v___jp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
lean_inc(v_toBind_925_);
v___x_944_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___y_943_, v___f_926_);
v___x_945_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_944_, v___f_941_);
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed(lean_object* v___x_952_, lean_object* v_toPure_953_, lean_object* v_toBind_954_, lean_object* v___f_955_, lean_object* v_initialMask_956_, lean_object* v___f_957_, lean_object* v_inst_958_, lean_object* v___x_959_, lean_object* v_next_960_, lean_object* v_acc_961_, lean_object* v_h_962_, lean_object* v_G_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(v___x_952_, v_toPure_953_, v_toBind_954_, v___f_955_, v_initialMask_956_, v___f_957_, v_inst_958_, v___x_959_, v_next_960_, v_acc_961_, v_h_962_, v_G_963_, v___y_964_, v___y_965_);
lean_dec_ref(v_initialMask_956_);
lean_dec(v___x_952_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(lean_object* v_toPure_970_, lean_object* v_inst_971_, lean_object* v_toBind_972_, lean_object* v___f_973_, lean_object* v_a_974_, lean_object* v_____x_975_){
_start:
{
lean_object* v_fst_976_; 
v_fst_976_ = lean_ctor_get(v_____x_975_, 0);
lean_inc(v_fst_976_);
if (lean_obj_tag(v_fst_976_) == 0)
{
lean_object* v_snd_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_993_; 
lean_dec_ref(v_a_974_);
lean_dec(v___f_973_);
lean_dec(v_toBind_972_);
lean_dec_ref(v_inst_971_);
v_snd_977_ = lean_ctor_get(v_____x_975_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v_____x_975_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; 
v_unused_994_ = lean_ctor_get(v_____x_975_, 0);
lean_dec(v_unused_994_);
v___x_979_ = v_____x_975_;
v_isShared_980_ = v_isSharedCheck_993_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_snd_977_);
lean_dec(v_____x_975_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_993_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_992_; 
v_a_981_ = lean_ctor_get(v_fst_976_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v_fst_976_);
if (v_isSharedCheck_992_ == 0)
{
v___x_983_ = v_fst_976_;
v_isShared_984_ = v_isSharedCheck_992_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v_fst_976_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_992_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_991_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_988_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_986_);
v___x_988_ = v___x_979_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_snd_977_);
v___x_988_ = v_reuseFailAlloc_990_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; 
v___x_989_ = lean_apply_2(v_toPure_970_, lean_box(0), v___x_988_);
return v___x_989_;
}
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v_snd_996_; lean_object* v_initialMask_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___f_1001_; lean_object* v___x_1002_; lean_object* v___f_1003_; lean_object* v___f_1004_; lean_object* v___f_1005_; lean_object* v___x_6350__overap_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_a_995_ = lean_ctor_get(v_fst_976_, 0);
lean_inc(v_a_995_);
lean_dec_ref(v_fst_976_);
v_snd_996_ = lean_ctor_get(v_____x_975_, 1);
lean_inc(v_snd_996_);
lean_dec_ref(v_____x_975_);
v_initialMask_997_ = lean_ctor_get(v_a_995_, 0);
lean_inc_ref(v_initialMask_997_);
lean_dec(v_a_995_);
v___x_998_ = lean_array_get_size(v_initialMask_997_);
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = lean_box(0);
lean_inc(v_toPure_970_);
v___f_1001_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1001_, 0, v_toPure_970_);
lean_closure_set(v___f_1001_, 1, v___x_1000_);
v___x_1002_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0));
lean_inc(v_toPure_970_);
v___f_1003_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1003_, 0, v_toPure_970_);
lean_closure_set(v___f_1003_, 1, v___x_1002_);
lean_closure_set(v___f_1003_, 2, v___x_1000_);
lean_inc(v_toBind_972_);
lean_inc_ref(v_inst_971_);
v___f_1004_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3), 6, 3);
lean_closure_set(v___f_1004_, 0, v_inst_971_);
lean_closure_set(v___f_1004_, 1, v_toBind_972_);
lean_closure_set(v___f_1004_, 2, v___f_1003_);
lean_inc(v_toBind_972_);
v___f_1005_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed), 14, 8);
lean_closure_set(v___f_1005_, 0, v___x_998_);
lean_closure_set(v___f_1005_, 1, v_toPure_970_);
lean_closure_set(v___f_1005_, 2, v_toBind_972_);
lean_closure_set(v___f_1005_, 3, v___f_973_);
lean_closure_set(v___f_1005_, 4, v_initialMask_997_);
lean_closure_set(v___f_1005_, 5, v___f_1004_);
lean_closure_set(v___f_1005_, 6, v_inst_971_);
lean_closure_set(v___f_1005_, 7, v___x_1000_);
v___x_6350__overap_1006_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1005_, v___x_999_, v___x_1002_, lean_box(0));
v___x_1007_ = lean_apply_2(v___x_6350__overap_1006_, v_a_974_, v_snd_996_);
v___x_1008_ = lean_apply_4(v_toBind_972_, lean_box(0), lean_box(0), v___x_1007_, v___f_1001_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(lean_object* v_inst_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v_toApplicative_1012_; lean_object* v_toBind_1013_; lean_object* v_toPure_1014_; lean_object* v___f_1015_; lean_object* v___f_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_toApplicative_1012_ = lean_ctor_get(v_inst_1009_, 0);
v_toBind_1013_ = lean_ctor_get(v_inst_1009_, 1);
lean_inc(v_toBind_1013_);
v_toPure_1014_ = lean_ctor_get(v_toApplicative_1012_, 1);
lean_inc(v_toPure_1014_);
lean_inc(v_toPure_1014_);
v___f_1015_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1015_, 0, v_toPure_1014_);
lean_inc_ref(v_a_1010_);
lean_inc(v_toBind_1013_);
lean_inc(v_toPure_1014_);
v___f_1016_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7), 6, 5);
lean_closure_set(v___f_1016_, 0, v_toPure_1014_);
lean_closure_set(v___f_1016_, 1, v_inst_1009_);
lean_closure_set(v___f_1016_, 2, v_toBind_1013_);
lean_closure_set(v___f_1016_, 3, v___f_1015_);
lean_closure_set(v___f_1016_, 4, v_a_1010_);
v___x_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1017_, 0, v_a_1010_);
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v_a_1011_);
v___x_1019_ = lean_apply_2(v_toPure_1014_, lean_box(0), v___x_1018_);
v___x_1020_ = lean_apply_4(v_toBind_1013_, lean_box(0), lean_box(0), v___x_1019_, v___f_1016_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(lean_object* v_m_1021_, lean_object* v_inst_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1022_, v_a_1023_, v_a_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0(lean_object* v_toPure_1028_, lean_object* v_____x_1029_){
_start:
{
lean_object* v_fst_1030_; 
v_fst_1030_ = lean_ctor_get(v_____x_1029_, 0);
lean_inc(v_fst_1030_);
if (lean_obj_tag(v_fst_1030_) == 0)
{
lean_object* v_snd_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1047_; 
v_snd_1031_ = lean_ctor_get(v_____x_1029_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_____x_1029_);
if (v_isSharedCheck_1047_ == 0)
{
lean_object* v_unused_1048_; 
v_unused_1048_ = lean_ctor_get(v_____x_1029_, 0);
lean_dec(v_unused_1048_);
v___x_1033_ = v_____x_1029_;
v_isShared_1034_ = v_isSharedCheck_1047_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_snd_1031_);
lean_dec(v_____x_1029_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1047_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1046_; 
v_a_1035_ = lean_ctor_get(v_fst_1030_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_fst_1030_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1037_ = v_fst_1030_;
v_isShared_1038_ = v_isSharedCheck_1046_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v_fst_1030_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1046_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1042_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1040_);
v___x_1042_ = v___x_1033_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v_snd_1031_);
v___x_1042_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_apply_2(v_toPure_1028_, lean_box(0), v___x_1042_);
return v___x_1043_;
}
}
}
}
}
else
{
lean_object* v_snd_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1058_; 
lean_dec_ref(v_fst_1030_);
v_snd_1049_ = lean_ctor_get(v_____x_1029_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_____x_1029_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; 
v_unused_1059_ = lean_ctor_get(v_____x_1029_, 0);
lean_dec(v_unused_1059_);
v___x_1051_ = v_____x_1029_;
v_isShared_1052_ = v_isSharedCheck_1058_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_snd_1049_);
lean_dec(v_____x_1029_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1058_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1053_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0));
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1053_);
v___x_1055_ = v___x_1051_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_snd_1049_);
v___x_1055_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_apply_2(v_toPure_1028_, lean_box(0), v___x_1055_);
return v___x_1056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1(lean_object* v_toPure_1060_, lean_object* v___x_1061_, lean_object* v_____x_1062_){
_start:
{
lean_object* v_fst_1063_; 
v_fst_1063_ = lean_ctor_get(v_____x_1062_, 0);
lean_inc(v_fst_1063_);
if (lean_obj_tag(v_fst_1063_) == 0)
{
lean_object* v_snd_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v___x_1061_);
v_snd_1064_ = lean_ctor_get(v_____x_1062_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_____x_1062_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v_____x_1062_, 0);
lean_dec(v_unused_1081_);
v___x_1066_ = v_____x_1062_;
v_isShared_1067_ = v_isSharedCheck_1080_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_snd_1064_);
lean_dec(v_____x_1062_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1080_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1079_; 
v_a_1068_ = lean_ctor_get(v_fst_1063_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_fst_1063_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1070_ = v_fst_1063_;
v_isShared_1071_ = v_isSharedCheck_1079_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v_fst_1063_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1079_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1075_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1073_);
v___x_1075_ = v___x_1066_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_snd_1064_);
v___x_1075_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_apply_2(v_toPure_1060_, lean_box(0), v___x_1075_);
return v___x_1076_;
}
}
}
}
}
else
{
lean_object* v_snd_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1099_; 
v_snd_1082_ = lean_ctor_get(v_____x_1062_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_____x_1062_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v_____x_1062_, 0);
lean_dec(v_unused_1100_);
v___x_1084_ = v_____x_1062_;
v_isShared_1085_ = v_isSharedCheck_1099_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_snd_1082_);
lean_dec(v_____x_1062_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1099_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1097_; 
v_isSharedCheck_1097_ = !lean_is_exclusive(v_fst_1063_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; 
v_unused_1098_ = lean_ctor_get(v_fst_1063_, 0);
lean_dec(v_unused_1098_);
v___x_1087_ = v_fst_1063_;
v_isShared_1088_ = v_isSharedCheck_1097_;
goto v_resetjp_1086_;
}
else
{
lean_dec(v_fst_1063_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1097_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1061_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1093_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1091_);
v___x_1093_ = v___x_1084_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_snd_1082_);
v___x_1093_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_apply_2(v_toPure_1060_, lean_box(0), v___x_1093_);
return v___x_1094_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2(lean_object* v_toPure_1101_, lean_object* v___x_1102_, lean_object* v_inst_1103_, lean_object* v_toBind_1104_, lean_object* v___f_1105_, lean_object* v___x_1106_, lean_object* v_____x_1107_){
_start:
{
lean_object* v_fst_1108_; 
v_fst_1108_ = lean_ctor_get(v_____x_1107_, 0);
lean_inc(v_fst_1108_);
if (lean_obj_tag(v_fst_1108_) == 0)
{
lean_object* v_snd_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v___x_1106_);
lean_dec(v___f_1105_);
lean_dec(v_toBind_1104_);
lean_dec_ref(v_inst_1103_);
v_snd_1109_ = lean_ctor_get(v_____x_1107_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_____x_1107_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v_____x_1107_, 0);
lean_dec(v_unused_1126_);
v___x_1111_ = v_____x_1107_;
v_isShared_1112_ = v_isSharedCheck_1125_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_snd_1109_);
lean_dec(v_____x_1107_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1125_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1124_; 
v_a_1113_ = lean_ctor_get(v_fst_1108_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_fst_1108_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1115_ = v_fst_1108_;
v_isShared_1116_ = v_isSharedCheck_1124_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v_fst_1108_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1124_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1120_; 
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1118_);
v___x_1120_ = v___x_1111_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_snd_1109_);
v___x_1120_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_apply_2(v_toPure_1101_, lean_box(0), v___x_1120_);
return v___x_1121_;
}
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1149_; 
v_a_1127_ = lean_ctor_get(v_fst_1108_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_fst_1108_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1129_ = v_fst_1108_;
v_isShared_1130_ = v_isSharedCheck_1149_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v_fst_1108_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1149_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_unbox(v_a_1127_);
lean_dec(v_a_1127_);
if (v___x_1131_ == 0)
{
lean_object* v_snd_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_del_object(v___x_1129_);
lean_dec(v___x_1106_);
lean_dec(v_toPure_1101_);
v_snd_1132_ = lean_ctor_get(v_____x_1107_, 1);
lean_inc(v_snd_1132_);
lean_dec_ref(v_____x_1107_);
v___x_1133_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(v___x_1102_, v_inst_1103_, v_snd_1132_);
v___x_1134_ = lean_apply_4(v_toBind_1104_, lean_box(0), lean_box(0), v___x_1133_, v___f_1105_);
return v___x_1134_;
}
else
{
lean_object* v_snd_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v___f_1105_);
lean_dec(v_toBind_1104_);
lean_dec_ref(v_inst_1103_);
v_snd_1135_ = lean_ctor_get(v_____x_1107_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_____x_1107_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; 
v_unused_1148_ = lean_ctor_get(v_____x_1107_, 0);
lean_dec(v_unused_1148_);
v___x_1137_ = v_____x_1107_;
v_isShared_1138_ = v_isSharedCheck_1147_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_snd_1135_);
lean_dec(v_____x_1107_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1147_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1106_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1139_);
v___x_1141_ = v___x_1129_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1143_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1141_);
v___x_1143_ = v___x_1137_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_snd_1135_);
v___x_1143_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_apply_2(v_toPure_1101_, lean_box(0), v___x_1143_);
return v___x_1144_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2___boxed(lean_object* v_toPure_1150_, lean_object* v___x_1151_, lean_object* v_inst_1152_, lean_object* v_toBind_1153_, lean_object* v___f_1154_, lean_object* v___x_1155_, lean_object* v_____x_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2(v_toPure_1150_, v___x_1151_, v_inst_1152_, v_toBind_1153_, v___f_1154_, v___x_1155_, v_____x_1156_);
lean_dec(v___x_1151_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(lean_object* v_toPure_1158_, lean_object* v_inst_1159_, lean_object* v___y_1160_, lean_object* v_toBind_1161_, lean_object* v___f_1162_, lean_object* v_____x_1163_){
_start:
{
lean_object* v_fst_1164_; 
v_fst_1164_ = lean_ctor_get(v_____x_1163_, 0);
lean_inc(v_fst_1164_);
if (lean_obj_tag(v_fst_1164_) == 0)
{
lean_object* v_snd_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1181_; 
lean_dec(v___f_1162_);
lean_dec(v_toBind_1161_);
lean_dec_ref(v___y_1160_);
lean_dec_ref(v_inst_1159_);
v_snd_1165_ = lean_ctor_get(v_____x_1163_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_____x_1163_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; 
v_unused_1182_ = lean_ctor_get(v_____x_1163_, 0);
lean_dec(v_unused_1182_);
v___x_1167_ = v_____x_1163_;
v_isShared_1168_ = v_isSharedCheck_1181_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_snd_1165_);
lean_dec(v_____x_1163_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1181_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1180_; 
v_a_1169_ = lean_ctor_get(v_fst_1164_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_fst_1164_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1171_ = v_fst_1164_;
v_isShared_1172_ = v_isSharedCheck_1180_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v_fst_1164_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1180_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1176_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1174_);
v___x_1176_ = v___x_1167_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_snd_1165_);
v___x_1176_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_apply_2(v_toPure_1158_, lean_box(0), v___x_1176_);
return v___x_1177_;
}
}
}
}
}
else
{
lean_object* v_snd_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec_ref(v_fst_1164_);
lean_dec(v_toPure_1158_);
v_snd_1183_ = lean_ctor_get(v_____x_1163_, 1);
lean_inc(v_snd_1183_);
lean_dec_ref(v_____x_1163_);
v___x_1184_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_1159_, v___y_1160_, v_snd_1183_);
v___x_1185_ = lean_apply_4(v_toBind_1161_, lean_box(0), lean_box(0), v___x_1184_, v___f_1162_);
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(lean_object* v_toPure_1186_, lean_object* v___x_1187_, lean_object* v_inst_1188_, lean_object* v_toBind_1189_, lean_object* v___f_1190_, lean_object* v___y_1191_, lean_object* v_____x_1192_){
_start:
{
lean_object* v_fst_1193_; 
v_fst_1193_ = lean_ctor_get(v_____x_1192_, 0);
lean_inc(v_fst_1193_);
if (lean_obj_tag(v_fst_1193_) == 0)
{
lean_object* v_snd_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v___y_1191_);
lean_dec(v___f_1190_);
lean_dec(v_toBind_1189_);
lean_dec_ref(v_inst_1188_);
lean_dec(v___x_1187_);
v_snd_1194_ = lean_ctor_get(v_____x_1192_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_____x_1192_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; 
v_unused_1211_ = lean_ctor_get(v_____x_1192_, 0);
lean_dec(v_unused_1211_);
v___x_1196_ = v_____x_1192_;
v_isShared_1197_ = v_isSharedCheck_1210_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_snd_1194_);
lean_dec(v_____x_1192_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1210_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1209_; 
v_a_1198_ = lean_ctor_get(v_fst_1193_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_fst_1193_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1200_ = v_fst_1193_;
v_isShared_1201_ = v_isSharedCheck_1209_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v_fst_1193_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1209_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1198_);
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
v___x_1206_ = lean_apply_2(v_toPure_1186_, lean_box(0), v___x_1205_);
return v___x_1206_;
}
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v_snd_1213_; lean_object* v_added_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___f_1217_; lean_object* v___f_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_a_1212_ = lean_ctor_get(v_fst_1193_, 0);
lean_inc(v_a_1212_);
lean_dec_ref(v_fst_1193_);
v_snd_1213_ = lean_ctor_get(v_____x_1192_, 1);
lean_inc(v_snd_1213_);
lean_dec_ref(v_____x_1192_);
v_added_1214_ = lean_ctor_get(v_a_1212_, 1);
lean_inc_ref(v_added_1214_);
lean_dec(v_a_1212_);
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = lean_array_get(v___x_1215_, v_added_1214_, v___x_1187_);
lean_dec_ref(v_added_1214_);
lean_inc(v_toBind_1189_);
lean_inc_ref(v_inst_1188_);
lean_inc(v___x_1216_);
lean_inc(v_toPure_1186_);
v___f_1217_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2___boxed), 7, 6);
lean_closure_set(v___f_1217_, 0, v_toPure_1186_);
lean_closure_set(v___f_1217_, 1, v___x_1216_);
lean_closure_set(v___f_1217_, 2, v_inst_1188_);
lean_closure_set(v___f_1217_, 3, v_toBind_1189_);
lean_closure_set(v___f_1217_, 4, v___f_1190_);
lean_closure_set(v___f_1217_, 5, v___x_1187_);
lean_inc(v_toBind_1189_);
lean_inc_ref(v_inst_1188_);
v___f_1218_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1218_, 0, v_toPure_1186_);
lean_closure_set(v___f_1218_, 1, v_inst_1188_);
lean_closure_set(v___f_1218_, 2, v___y_1191_);
lean_closure_set(v___f_1218_, 3, v_toBind_1189_);
lean_closure_set(v___f_1218_, 4, v___f_1217_);
v___x_1219_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(v___x_1216_, v_inst_1188_, v_snd_1213_);
lean_dec(v___x_1216_);
v___x_1220_ = lean_apply_4(v_toBind_1189_, lean_box(0), lean_box(0), v___x_1219_, v___f_1218_);
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(lean_object* v_toPure_1221_, lean_object* v___x_1222_, lean_object* v_inst_1223_, lean_object* v_toBind_1224_, lean_object* v_x_1225_, lean_object* v_____s_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = lean_nat_dec_lt(v___x_1229_, v_____s_1226_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec_ref(v___y_1227_);
lean_dec(v_toBind_1224_);
lean_dec_ref(v_inst_1223_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_____s_1226_);
v___x_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
v___x_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
lean_ctor_set(v___x_1233_, 1, v___y_1228_);
v___x_1234_ = lean_apply_2(v_toPure_1221_, lean_box(0), v___x_1233_);
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; lean_object* v___f_1236_; lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1235_ = lean_nat_sub(v_____s_1226_, v___x_1222_);
lean_dec(v_____s_1226_);
lean_inc(v___x_1235_);
lean_inc(v_toPure_1221_);
v___f_1236_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1236_, 0, v_toPure_1221_);
lean_closure_set(v___f_1236_, 1, v___x_1235_);
lean_inc(v_toBind_1224_);
lean_inc(v_toPure_1221_);
v___f_1237_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4), 7, 6);
lean_closure_set(v___f_1237_, 0, v_toPure_1221_);
lean_closure_set(v___f_1237_, 1, v___x_1235_);
lean_closure_set(v___f_1237_, 2, v_inst_1223_);
lean_closure_set(v___f_1237_, 3, v_toBind_1224_);
lean_closure_set(v___f_1237_, 4, v___f_1236_);
lean_closure_set(v___f_1237_, 5, v___y_1227_);
lean_inc(v_toPure_1221_);
v___f_1238_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1238_, 0, v_toPure_1221_);
lean_inc_ref(v___y_1228_);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___y_1228_);
lean_ctor_set(v___x_1239_, 1, v___y_1228_);
v___x_1240_ = lean_apply_2(v_toPure_1221_, lean_box(0), v___x_1239_);
lean_inc(v_toBind_1224_);
v___x_1241_ = lean_apply_4(v_toBind_1224_, lean_box(0), lean_box(0), v___x_1240_, v___f_1238_);
v___x_1242_ = lean_apply_4(v_toBind_1224_, lean_box(0), lean_box(0), v___x_1241_, v___f_1237_);
return v___x_1242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed(lean_object* v_toPure_1243_, lean_object* v___x_1244_, lean_object* v_inst_1245_, lean_object* v_toBind_1246_, lean_object* v_x_1247_, lean_object* v_____s_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(v_toPure_1243_, v___x_1244_, v_inst_1245_, v_toBind_1246_, v_x_1247_, v_____s_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___x_1244_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(lean_object* v_toPure_1252_, lean_object* v_inst_1253_, lean_object* v_toBind_1254_, lean_object* v___x_1255_, lean_object* v_a_1256_, lean_object* v___f_1257_, lean_object* v_____x_1258_){
_start:
{
lean_object* v_fst_1259_; 
v_fst_1259_ = lean_ctor_get(v_____x_1258_, 0);
lean_inc(v_fst_1259_);
if (lean_obj_tag(v_fst_1259_) == 0)
{
lean_object* v_snd_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1276_; 
lean_dec(v___f_1257_);
lean_dec_ref(v_a_1256_);
lean_dec_ref(v___x_1255_);
lean_dec(v_toBind_1254_);
lean_dec_ref(v_inst_1253_);
v_snd_1260_ = lean_ctor_get(v_____x_1258_, 1);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_____x_1258_);
if (v_isSharedCheck_1276_ == 0)
{
lean_object* v_unused_1277_; 
v_unused_1277_ = lean_ctor_get(v_____x_1258_, 0);
lean_dec(v_unused_1277_);
v___x_1262_ = v_____x_1258_;
v_isShared_1263_ = v_isSharedCheck_1276_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_snd_1260_);
lean_dec(v_____x_1258_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1276_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1275_; 
v_a_1264_ = lean_ctor_get(v_fst_1259_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_fst_1259_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1266_ = v_fst_1259_;
v_isShared_1267_ = v_isSharedCheck_1275_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v_fst_1259_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1275_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1271_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1269_);
v___x_1271_ = v___x_1262_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_snd_1260_);
v___x_1271_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_apply_2(v_toPure_1252_, lean_box(0), v___x_1271_);
return v___x_1272_;
}
}
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v_snd_1279_; lean_object* v_added_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___f_1283_; lean_object* v___x_1284_; lean_object* v___x_4699__overap_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v_a_1278_ = lean_ctor_get(v_fst_1259_, 0);
lean_inc(v_a_1278_);
lean_dec_ref(v_fst_1259_);
v_snd_1279_ = lean_ctor_get(v_____x_1258_, 1);
lean_inc(v_snd_1279_);
lean_dec_ref(v_____x_1258_);
v_added_1280_ = lean_ctor_get(v_a_1278_, 1);
lean_inc_ref(v_added_1280_);
lean_dec(v_a_1278_);
v___x_1281_ = lean_array_get_size(v_added_1280_);
lean_dec_ref(v_added_1280_);
v___x_1282_ = lean_unsigned_to_nat(1u);
lean_inc(v_toBind_1254_);
v___f_1283_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed), 8, 4);
lean_closure_set(v___f_1283_, 0, v_toPure_1252_);
lean_closure_set(v___f_1283_, 1, v___x_1282_);
lean_closure_set(v___f_1283_, 2, v_inst_1253_);
lean_closure_set(v___f_1283_, 3, v_toBind_1254_);
v___x_1284_ = lean_nat_sub(v___x_1281_, v___x_1282_);
v___x_4699__overap_1285_ = l___private_Init_While_0__Lean_Loop_forIn_loop(lean_box(0), lean_box(0), v___x_1255_, v___f_1283_, v___x_1284_);
v___x_1286_ = lean_apply_2(v___x_4699__overap_1285_, v_a_1256_, v_snd_1279_);
v___x_1287_ = lean_apply_4(v_toBind_1254_, lean_box(0), lean_box(0), v___x_1286_, v___f_1257_);
return v___x_1287_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(lean_object* v_inst_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v___f_1291_; lean_object* v___f_1292_; lean_object* v___f_1293_; lean_object* v___f_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___f_1301_; lean_object* v___f_1302_; lean_object* v___f_1303_; lean_object* v___f_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v_toApplicative_1312_; lean_object* v_toBind_1313_; lean_object* v_toPure_1314_; lean_object* v___f_1315_; lean_object* v___f_1316_; lean_object* v___f_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_inc_ref(v_inst_1288_);
v___f_1291_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1291_, 0, v_inst_1288_);
lean_inc_ref(v_inst_1288_);
v___f_1292_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1292_, 0, v_inst_1288_);
lean_inc_ref(v_inst_1288_);
v___f_1293_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1293_, 0, v_inst_1288_);
lean_inc_ref(v_inst_1288_);
v___f_1294_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1294_, 0, v_inst_1288_);
lean_inc_ref(v_inst_1288_);
v___x_1295_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1295_, 0, lean_box(0));
lean_closure_set(v___x_1295_, 1, lean_box(0));
lean_closure_set(v___x_1295_, 2, v_inst_1288_);
v___x_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set(v___x_1296_, 1, v___f_1291_);
lean_inc_ref(v_inst_1288_);
v___x_1297_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1297_, 0, lean_box(0));
lean_closure_set(v___x_1297_, 1, lean_box(0));
lean_closure_set(v___x_1297_, 2, v_inst_1288_);
v___x_1298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1296_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
lean_ctor_set(v___x_1298_, 2, v___f_1292_);
lean_ctor_set(v___x_1298_, 3, v___f_1293_);
lean_ctor_set(v___x_1298_, 4, v___f_1294_);
lean_inc_ref(v_inst_1288_);
v___x_1299_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1299_, 0, lean_box(0));
lean_closure_set(v___x_1299_, 1, lean_box(0));
lean_closure_set(v___x_1299_, 2, v_inst_1288_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
lean_inc_ref(v___x_1300_);
v___f_1301_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1301_, 0, v___x_1300_);
lean_inc_ref(v___x_1300_);
v___f_1302_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1302_, 0, v___x_1300_);
lean_inc_ref(v___x_1300_);
v___f_1303_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1303_, 0, v___x_1300_);
lean_inc_ref(v___x_1300_);
v___f_1304_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1304_, 0, v___x_1300_);
lean_inc_ref(v___x_1300_);
v___x_1305_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1305_, 0, lean_box(0));
lean_closure_set(v___x_1305_, 1, lean_box(0));
lean_closure_set(v___x_1305_, 2, v___x_1300_);
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v___f_1301_);
lean_inc_ref(v___x_1300_);
v___x_1307_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1307_, 0, lean_box(0));
lean_closure_set(v___x_1307_, 1, lean_box(0));
lean_closure_set(v___x_1307_, 2, v___x_1300_);
v___x_1308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
lean_ctor_set(v___x_1308_, 2, v___f_1302_);
lean_ctor_set(v___x_1308_, 3, v___f_1303_);
lean_ctor_set(v___x_1308_, 4, v___f_1304_);
v___x_1309_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1309_, 0, lean_box(0));
lean_closure_set(v___x_1309_, 1, lean_box(0));
lean_closure_set(v___x_1309_, 2, v___x_1300_);
v___x_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1308_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = l_ReaderT_instMonad___redArg(v___x_1310_);
v_toApplicative_1312_ = lean_ctor_get(v_inst_1288_, 0);
v_toBind_1313_ = lean_ctor_get(v_inst_1288_, 1);
lean_inc(v_toBind_1313_);
v_toPure_1314_ = lean_ctor_get(v_toApplicative_1312_, 1);
lean_inc(v_toPure_1314_);
lean_inc(v_toPure_1314_);
v___f_1315_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1315_, 0, v_toPure_1314_);
lean_inc(v_toBind_1313_);
lean_inc(v_toPure_1314_);
v___f_1316_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5), 7, 6);
lean_closure_set(v___f_1316_, 0, v_toPure_1314_);
lean_closure_set(v___f_1316_, 1, v_inst_1288_);
lean_closure_set(v___f_1316_, 2, v_toBind_1313_);
lean_closure_set(v___f_1316_, 3, v___x_1311_);
lean_closure_set(v___f_1316_, 4, v_a_1289_);
lean_closure_set(v___f_1316_, 5, v___f_1315_);
lean_inc(v_toPure_1314_);
v___f_1317_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1317_, 0, v_toPure_1314_);
lean_inc_ref(v_a_1290_);
v___x_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1318_, 0, v_a_1290_);
lean_ctor_set(v___x_1318_, 1, v_a_1290_);
v___x_1319_ = lean_apply_2(v_toPure_1314_, lean_box(0), v___x_1318_);
lean_inc(v_toBind_1313_);
v___x_1320_ = lean_apply_4(v_toBind_1313_, lean_box(0), lean_box(0), v___x_1319_, v___f_1317_);
v___x_1321_ = lean_apply_4(v_toBind_1313_, lean_box(0), lean_box(0), v___x_1320_, v___f_1316_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(lean_object* v_m_1322_, lean_object* v_inst_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1323_, v_a_1324_, v_a_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(lean_object* v_toApplicative_1327_, lean_object* v_inst_1328_, lean_object* v_a_1329_, lean_object* v_____x_1330_){
_start:
{
lean_object* v_fst_1331_; 
v_fst_1331_ = lean_ctor_get(v_____x_1330_, 0);
lean_inc(v_fst_1331_);
if (lean_obj_tag(v_fst_1331_) == 0)
{
lean_object* v_snd_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref(v_a_1329_);
lean_dec_ref(v_inst_1328_);
v_snd_1332_ = lean_ctor_get(v_____x_1330_, 1);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_____x_1330_);
if (v_isSharedCheck_1349_ == 0)
{
lean_object* v_unused_1350_; 
v_unused_1350_ = lean_ctor_get(v_____x_1330_, 0);
lean_dec(v_unused_1350_);
v___x_1334_ = v_____x_1330_;
v_isShared_1335_ = v_isSharedCheck_1349_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_snd_1332_);
lean_dec(v_____x_1330_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1349_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1348_; 
v_a_1336_ = lean_ctor_get(v_fst_1331_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_fst_1331_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1338_ = v_fst_1331_;
v_isShared_1339_ = v_isSharedCheck_1348_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v_fst_1331_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1348_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v_toPure_1340_; lean_object* v___x_1342_; 
v_toPure_1340_ = lean_ctor_get(v_toApplicative_1327_, 1);
lean_inc(v_toPure_1340_);
lean_dec_ref(v_toApplicative_1327_);
if (v_isShared_1339_ == 0)
{
v___x_1342_ = v___x_1338_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1336_);
v___x_1342_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1344_; 
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1342_);
v___x_1344_ = v___x_1334_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_snd_1332_);
v___x_1344_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_apply_2(v_toPure_1340_, lean_box(0), v___x_1344_);
return v___x_1345_;
}
}
}
}
}
else
{
lean_object* v_a_1351_; uint8_t v_found_1352_; 
v_a_1351_ = lean_ctor_get(v_fst_1331_, 0);
lean_inc(v_a_1351_);
lean_dec_ref(v_fst_1331_);
v_found_1352_ = lean_ctor_get_uint8(v_a_1351_, sizeof(void*)*3);
lean_dec(v_a_1351_);
if (v_found_1352_ == 0)
{
lean_object* v_snd_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1363_; 
lean_dec_ref(v_a_1329_);
lean_dec_ref(v_inst_1328_);
v_snd_1353_ = lean_ctor_get(v_____x_1330_, 1);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_____x_1330_);
if (v_isSharedCheck_1363_ == 0)
{
lean_object* v_unused_1364_; 
v_unused_1364_ = lean_ctor_get(v_____x_1330_, 0);
lean_dec(v_unused_1364_);
v___x_1355_ = v_____x_1330_;
v_isShared_1356_ = v_isSharedCheck_1363_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_snd_1353_);
lean_dec(v_____x_1330_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1363_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v_toPure_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
v_toPure_1357_ = lean_ctor_get(v_toApplicative_1327_, 1);
lean_inc(v_toPure_1357_);
lean_dec_ref(v_toApplicative_1327_);
v___x_1358_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0));
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1358_);
v___x_1360_ = v___x_1355_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_snd_1353_);
v___x_1360_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_apply_2(v_toPure_1357_, lean_box(0), v___x_1360_);
return v___x_1361_;
}
}
}
else
{
lean_object* v_snd_1365_; lean_object* v___x_1366_; 
lean_dec_ref(v_toApplicative_1327_);
v_snd_1365_ = lean_ctor_get(v_____x_1330_, 1);
lean_inc(v_snd_1365_);
lean_dec_ref(v_____x_1330_);
v___x_1366_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1328_, v_a_1329_, v_snd_1365_);
return v___x_1366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2(lean_object* v_toApplicative_1367_, lean_object* v_toBind_1368_, lean_object* v___f_1369_, lean_object* v_____x_1370_){
_start:
{
lean_object* v_fst_1371_; 
v_fst_1371_ = lean_ctor_get(v_____x_1370_, 0);
if (lean_obj_tag(v_fst_1371_) == 0)
{
lean_object* v_toPure_1372_; lean_object* v___x_1373_; 
lean_dec(v___f_1369_);
lean_dec(v_toBind_1368_);
v_toPure_1372_ = lean_ctor_get(v_toApplicative_1367_, 1);
lean_inc(v_toPure_1372_);
lean_dec_ref(v_toApplicative_1367_);
v___x_1373_ = lean_apply_2(v_toPure_1372_, lean_box(0), v_____x_1370_);
return v___x_1373_;
}
else
{
lean_object* v_snd_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1386_; 
v_snd_1374_ = lean_ctor_get(v_____x_1370_, 1);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_____x_1370_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; 
v_unused_1387_ = lean_ctor_get(v_____x_1370_, 0);
lean_dec(v_unused_1387_);
v___x_1376_ = v_____x_1370_;
v_isShared_1377_ = v_isSharedCheck_1386_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_snd_1374_);
lean_dec(v_____x_1370_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1386_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v_toPure_1378_; lean_object* v___f_1379_; lean_object* v___x_1381_; 
v_toPure_1378_ = lean_ctor_get(v_toApplicative_1367_, 1);
lean_inc(v_toPure_1378_);
lean_dec_ref(v_toApplicative_1367_);
lean_inc(v_toPure_1378_);
v___f_1379_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1379_, 0, v_toPure_1378_);
lean_inc(v_snd_1374_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v_snd_1374_);
v___x_1381_ = v___x_1376_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_snd_1374_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_snd_1374_);
v___x_1381_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = lean_apply_2(v_toPure_1378_, lean_box(0), v___x_1381_);
lean_inc(v_toBind_1368_);
v___x_1383_ = lean_apply_4(v_toBind_1368_, lean_box(0), lean_box(0), v___x_1382_, v___f_1379_);
v___x_1384_ = lean_apply_4(v_toBind_1368_, lean_box(0), lean_box(0), v___x_1383_, v___f_1369_);
return v___x_1384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(lean_object* v_inst_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_toApplicative_1391_; lean_object* v_toBind_1392_; lean_object* v___f_1393_; lean_object* v___f_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v_toApplicative_1391_ = lean_ctor_get(v_inst_1388_, 0);
v_toBind_1392_ = lean_ctor_get(v_inst_1388_, 1);
lean_inc(v_toBind_1392_);
lean_inc_ref(v_a_1389_);
lean_inc_ref(v_inst_1388_);
lean_inc_ref(v_toApplicative_1391_);
v___f_1393_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1393_, 0, v_toApplicative_1391_);
lean_closure_set(v___f_1393_, 1, v_inst_1388_);
lean_closure_set(v___f_1393_, 2, v_a_1389_);
lean_inc(v_toBind_1392_);
lean_inc_ref(v_toApplicative_1391_);
v___f_1394_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1394_, 0, v_toApplicative_1391_);
lean_closure_set(v___f_1394_, 1, v_toBind_1392_);
lean_closure_set(v___f_1394_, 2, v___f_1393_);
v___x_1395_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1388_, v_a_1389_, v_a_1390_);
v___x_1396_ = lean_apply_4(v_toBind_1392_, lean_box(0), lean_box(0), v___x_1395_, v___f_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(lean_object* v_m_1397_, lean_object* v_inst_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1398_, v_a_1399_, v_a_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__0(lean_object* v_toApplicative_1402_, lean_object* v_____x_1403_){
_start:
{
lean_object* v_snd_1404_; lean_object* v_fst_1405_; lean_object* v_cur_1406_; lean_object* v_numCalls_1407_; uint8_t v_found_1408_; uint8_t v___y_1410_; 
v_snd_1404_ = lean_ctor_get(v_____x_1403_, 1);
v_fst_1405_ = lean_ctor_get(v_____x_1403_, 0);
v_cur_1406_ = lean_ctor_get(v_snd_1404_, 0);
v_numCalls_1407_ = lean_ctor_get(v_snd_1404_, 2);
v_found_1408_ = lean_ctor_get_uint8(v_snd_1404_, sizeof(void*)*3);
if (v_found_1408_ == 0)
{
uint8_t v___x_1414_; 
v___x_1414_ = 0;
v___y_1410_ = v___x_1414_;
goto v___jp_1409_;
}
else
{
if (lean_obj_tag(v_fst_1405_) == 0)
{
uint8_t v___x_1415_; 
v___x_1415_ = 1;
v___y_1410_ = v___x_1415_;
goto v___jp_1409_;
}
else
{
uint8_t v___x_1416_; 
v___x_1416_ = 2;
v___y_1410_ = v___x_1416_;
goto v___jp_1409_;
}
}
v___jp_1409_:
{
lean_object* v_toPure_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v_toPure_1411_ = lean_ctor_get(v_toApplicative_1402_, 1);
lean_inc(v_toPure_1411_);
lean_dec_ref(v_toApplicative_1402_);
lean_inc(v_numCalls_1407_);
lean_inc_ref(v_cur_1406_);
v___x_1412_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1412_, 0, v_cur_1406_);
lean_ctor_set(v___x_1412_, 1, v_numCalls_1407_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*2, v___y_1410_);
v___x_1413_ = lean_apply_2(v_toPure_1411_, lean_box(0), v___x_1412_);
return v___x_1413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed(lean_object* v_toApplicative_1417_, lean_object* v_____x_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_Util_ParamMinimizer_search___redArg___lam__0(v_toApplicative_1417_, v_____x_1418_);
lean_dec_ref(v_____x_1418_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__1(lean_object* v_initialMask_1422_, lean_object* v_test_1423_, lean_object* v_maxCalls_1424_, lean_object* v_inst_1425_, lean_object* v_toBind_1426_, lean_object* v___f_1427_, lean_object* v_toApplicative_1428_, uint8_t v_____do__lift_1429_){
_start:
{
if (v_____do__lift_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_dec_ref(v_toApplicative_1428_);
lean_inc_ref(v_initialMask_1422_);
v___x_1430_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1430_, 0, v_initialMask_1422_);
lean_ctor_set(v___x_1430_, 1, v_test_1423_);
lean_ctor_set(v___x_1430_, 2, v_maxCalls_1424_);
v___x_1431_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0));
v___x_1432_ = lean_unsigned_to_nat(1u);
v___x_1433_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1433_, 0, v_initialMask_1422_);
lean_ctor_set(v___x_1433_, 1, v___x_1431_);
lean_ctor_set(v___x_1433_, 2, v___x_1432_);
lean_ctor_set_uint8(v___x_1433_, sizeof(void*)*3, v_____do__lift_1429_);
v___x_1434_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1425_, v___x_1430_, v___x_1433_);
v___x_1435_ = lean_apply_4(v_toBind_1426_, lean_box(0), lean_box(0), v___x_1434_, v___f_1427_);
return v___x_1435_;
}
else
{
lean_object* v_toPure_1436_; uint8_t v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec(v___f_1427_);
lean_dec(v_toBind_1426_);
lean_dec_ref(v_inst_1425_);
lean_dec(v_maxCalls_1424_);
lean_dec(v_test_1423_);
v_toPure_1436_ = lean_ctor_get(v_toApplicative_1428_, 1);
lean_inc(v_toPure_1436_);
lean_dec_ref(v_toApplicative_1428_);
v___x_1437_ = 2;
v___x_1438_ = lean_unsigned_to_nat(1u);
v___x_1439_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1439_, 0, v_initialMask_1422_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
lean_ctor_set_uint8(v___x_1439_, sizeof(void*)*2, v___x_1437_);
v___x_1440_ = lean_apply_2(v_toPure_1436_, lean_box(0), v___x_1439_);
return v___x_1440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed(lean_object* v_initialMask_1441_, lean_object* v_test_1442_, lean_object* v_maxCalls_1443_, lean_object* v_inst_1444_, lean_object* v_toBind_1445_, lean_object* v___f_1446_, lean_object* v_toApplicative_1447_, lean_object* v_____do__lift_1448_){
_start:
{
uint8_t v_____do__lift_277__boxed_1449_; lean_object* v_res_1450_; 
v_____do__lift_277__boxed_1449_ = lean_unbox(v_____do__lift_1448_);
v_res_1450_ = l_Lean_Util_ParamMinimizer_search___redArg___lam__1(v_initialMask_1441_, v_test_1442_, v_maxCalls_1443_, v_inst_1444_, v_toBind_1445_, v___f_1446_, v_toApplicative_1447_, v_____do__lift_277__boxed_1449_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg(lean_object* v_inst_1451_, lean_object* v_initialMask_1452_, lean_object* v_test_1453_, lean_object* v_maxCalls_1454_){
_start:
{
lean_object* v_toApplicative_1455_; lean_object* v_toBind_1456_; lean_object* v___f_1457_; lean_object* v___f_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v_toApplicative_1455_ = lean_ctor_get(v_inst_1451_, 0);
lean_inc_ref(v_toApplicative_1455_);
v_toBind_1456_ = lean_ctor_get(v_inst_1451_, 1);
lean_inc(v_toBind_1456_);
lean_inc_ref(v_toApplicative_1455_);
v___f_1457_ = lean_alloc_closure((void*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1457_, 0, v_toApplicative_1455_);
lean_inc(v_toBind_1456_);
lean_inc(v_test_1453_);
lean_inc_ref(v_initialMask_1452_);
v___f_1458_ = lean_alloc_closure((void*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1458_, 0, v_initialMask_1452_);
lean_closure_set(v___f_1458_, 1, v_test_1453_);
lean_closure_set(v___f_1458_, 2, v_maxCalls_1454_);
lean_closure_set(v___f_1458_, 3, v_inst_1451_);
lean_closure_set(v___f_1458_, 4, v_toBind_1456_);
lean_closure_set(v___f_1458_, 5, v___f_1457_);
lean_closure_set(v___f_1458_, 6, v_toApplicative_1455_);
v___x_1459_ = lean_apply_1(v_test_1453_, v_initialMask_1452_);
v___x_1460_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1459_, v___f_1458_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search(lean_object* v_m_1461_, lean_object* v_inst_1462_, lean_object* v_initialMask_1463_, lean_object* v_test_1464_, lean_object* v_maxCalls_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_Util_ParamMinimizer_search___redArg(v_inst_1462_, v_initialMask_1463_, v_test_1464_, v_maxCalls_1465_);
return v___x_1466_;
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
