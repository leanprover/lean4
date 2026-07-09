// Lean compiler output
// Module: Lean.Meta.Sym.LooseBVarsS
// Imports: public import Lean.Meta.Sym.ReplaceS
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
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_map, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_pure, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_seqRight, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_bind, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.Sym.ReplaceS.0.Lean.Meta.Sym.visit"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.ReplaceS"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_lowerLooseBVarsS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Sym.AlphaShareBuilder"};
static const lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_lowerLooseBVarsS___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_lowerLooseBVarsS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Sym.Internal.liftBuilderM"};
static const lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_lowerLooseBVarsS___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(lean_object* v_idx_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = l_Lean_Expr_bvar___override(v_idx_1_);
v___x_4_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_3_, v___y_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(lean_object* v_idx_5_, uint8_t v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v_idx_5_, v___y_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___boxed(lean_object* v_idx_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
uint8_t v___y_24041__boxed_14_; lean_object* v_res_15_; 
v___y_24041__boxed_14_ = lean_unbox(v___y_11_);
v_res_15_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(v_idx_10_, v___y_24041__boxed_14_, v___y_12_, v___y_13_);
lean_dec_ref(v___y_12_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(lean_object* v_x_16_, uint8_t v_bi_17_, lean_object* v_t_18_, lean_object* v_b_19_, lean_object* v___y_20_, uint8_t v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___y_25_; lean_object* v___y_26_; 
if (v___y_21_ == 0)
{
v___y_25_ = v___y_20_;
v___y_26_ = v___y_23_;
goto v___jp_24_;
}
else
{
lean_object* v___x_48_; 
lean_inc_ref(v_t_18_);
v___x_48_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_18_, v___y_21_, v___y_22_, v___y_23_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v_a_49_; lean_object* v___x_50_; 
v_a_49_ = lean_ctor_get(v___x_48_, 1);
lean_inc(v_a_49_);
lean_dec_ref_known(v___x_48_, 2);
lean_inc_ref(v_b_19_);
v___x_50_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_19_, v___y_21_, v___y_22_, v_a_49_);
if (lean_obj_tag(v___x_50_) == 0)
{
lean_object* v_a_51_; 
v_a_51_ = lean_ctor_get(v___x_50_, 1);
lean_inc(v_a_51_);
lean_dec_ref_known(v___x_50_, 2);
v___y_25_ = v___y_20_;
v___y_26_ = v_a_51_;
goto v___jp_24_;
}
else
{
lean_object* v_a_52_; lean_object* v_a_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
lean_dec_ref(v___y_20_);
lean_dec_ref(v_b_19_);
lean_dec_ref(v_t_18_);
lean_dec(v_x_16_);
v_a_52_ = lean_ctor_get(v___x_50_, 0);
v_a_53_ = lean_ctor_get(v___x_50_, 1);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_60_ == 0)
{
v___x_55_ = v___x_50_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_a_53_);
lean_inc(v_a_52_);
lean_dec(v___x_50_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_a_52_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_a_53_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
else
{
lean_object* v_a_61_; lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
lean_dec_ref(v___y_20_);
lean_dec_ref(v_b_19_);
lean_dec_ref(v_t_18_);
lean_dec(v_x_16_);
v_a_61_ = lean_ctor_get(v___x_48_, 0);
v_a_62_ = lean_ctor_get(v___x_48_, 1);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_48_);
if (v_isSharedCheck_69_ == 0)
{
v___x_64_ = v___x_48_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_inc(v_a_61_);
lean_dec(v___x_48_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_61_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
v___jp_24_:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = l_Lean_Expr_forallE___override(v_x_16_, v_t_18_, v_b_19_, v_bi_17_);
v___x_28_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_27_, v___y_26_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_38_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
v_a_30_ = lean_ctor_get(v___x_28_, 1);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_38_ == 0)
{
v___x_32_ = v___x_28_;
v_isShared_33_ = v_isSharedCheck_38_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_inc(v_a_29_);
lean_dec(v___x_28_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_38_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_34_; lean_object* v___x_36_; 
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v_a_29_);
lean_ctor_set(v___x_34_, 1, v___y_25_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v___x_34_);
v___x_36_ = v___x_32_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_a_30_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
lean_object* v_a_39_; lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_47_; 
lean_dec_ref(v___y_25_);
v_a_39_ = lean_ctor_get(v___x_28_, 0);
v_a_40_ = lean_ctor_get(v___x_28_, 1);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_47_ == 0)
{
v___x_42_ = v___x_28_;
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_inc(v_a_39_);
lean_dec(v___x_28_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_45_; 
if (v_isShared_43_ == 0)
{
v___x_45_ = v___x_42_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_a_39_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_a_40_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4___boxed(lean_object* v_x_70_, lean_object* v_bi_71_, lean_object* v_t_72_, lean_object* v_b_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
uint8_t v_bi_boxed_78_; uint8_t v___y_24053__boxed_79_; lean_object* v_res_80_; 
v_bi_boxed_78_ = lean_unbox(v_bi_71_);
v___y_24053__boxed_79_ = lean_unbox(v___y_75_);
v_res_80_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_x_70_, v_bi_boxed_78_, v_t_72_, v_b_73_, v___y_74_, v___y_24053__boxed_79_, v___y_76_, v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(lean_object* v_structName_81_, lean_object* v_idx_82_, lean_object* v_struct_83_, lean_object* v___y_84_, uint8_t v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___y_89_; lean_object* v___y_90_; 
if (v___y_85_ == 0)
{
v___y_89_ = v___y_84_;
v___y_90_ = v___y_87_;
goto v___jp_88_;
}
else
{
lean_object* v___x_112_; 
lean_inc_ref(v_struct_83_);
v___x_112_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_83_, v___y_85_, v___y_86_, v___y_87_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; 
v_a_113_ = lean_ctor_get(v___x_112_, 1);
lean_inc(v_a_113_);
lean_dec_ref_known(v___x_112_, 2);
v___y_89_ = v___y_84_;
v___y_90_ = v_a_113_;
goto v___jp_88_;
}
else
{
lean_object* v_a_114_; lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_dec_ref(v___y_84_);
lean_dec_ref(v_struct_83_);
lean_dec(v_idx_82_);
lean_dec(v_structName_81_);
v_a_114_ = lean_ctor_get(v___x_112_, 0);
v_a_115_ = lean_ctor_get(v___x_112_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_112_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_inc(v_a_114_);
lean_dec(v___x_112_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_114_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
v___jp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = l_Lean_Expr_proj___override(v_structName_81_, v_idx_82_, v_struct_83_);
v___x_92_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_91_, v___y_90_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_102_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_a_94_ = lean_ctor_get(v___x_92_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_102_ == 0)
{
v___x_96_ = v___x_92_;
v_isShared_97_ = v_isSharedCheck_102_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_102_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v_a_93_);
lean_ctor_set(v___x_98_, 1, v___y_89_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v___x_98_);
v___x_100_ = v___x_96_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_a_94_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
else
{
lean_object* v_a_103_; lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
lean_dec_ref(v___y_89_);
v_a_103_ = lean_ctor_get(v___x_92_, 0);
v_a_104_ = lean_ctor_get(v___x_92_, 1);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_92_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_inc(v_a_103_);
lean_dec(v___x_92_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_103_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7___boxed(lean_object* v_structName_123_, lean_object* v_idx_124_, lean_object* v_struct_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
uint8_t v___y_24159__boxed_130_; lean_object* v_res_131_; 
v___y_24159__boxed_130_ = lean_unbox(v___y_127_);
v_res_131_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_structName_123_, v_idx_124_, v_struct_125_, v___y_126_, v___y_24159__boxed_130_, v___y_128_, v___y_129_);
lean_dec_ref(v___y_128_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(lean_object* v_x_132_, uint8_t v_bi_133_, lean_object* v_t_134_, lean_object* v_b_135_, lean_object* v___y_136_, uint8_t v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v___y_141_; lean_object* v___y_142_; 
if (v___y_137_ == 0)
{
v___y_141_ = v___y_136_;
v___y_142_ = v___y_139_;
goto v___jp_140_;
}
else
{
lean_object* v___x_164_; 
lean_inc_ref(v_t_134_);
v___x_164_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_134_, v___y_137_, v___y_138_, v___y_139_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_166_; 
v_a_165_ = lean_ctor_get(v___x_164_, 1);
lean_inc(v_a_165_);
lean_dec_ref_known(v___x_164_, 2);
lean_inc_ref(v_b_135_);
v___x_166_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_135_, v___y_137_, v___y_138_, v_a_165_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; 
v_a_167_ = lean_ctor_get(v___x_166_, 1);
lean_inc(v_a_167_);
lean_dec_ref_known(v___x_166_, 2);
v___y_141_ = v___y_136_;
v___y_142_ = v_a_167_;
goto v___jp_140_;
}
else
{
lean_object* v_a_168_; lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
lean_dec_ref(v___y_136_);
lean_dec_ref(v_b_135_);
lean_dec_ref(v_t_134_);
lean_dec(v_x_132_);
v_a_168_ = lean_ctor_get(v___x_166_, 0);
v_a_169_ = lean_ctor_get(v___x_166_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_166_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_inc(v_a_168_);
lean_dec(v___x_166_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_168_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
else
{
lean_object* v_a_177_; lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_dec_ref(v___y_136_);
lean_dec_ref(v_b_135_);
lean_dec_ref(v_t_134_);
lean_dec(v_x_132_);
v_a_177_ = lean_ctor_get(v___x_164_, 0);
v_a_178_ = lean_ctor_get(v___x_164_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_164_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_inc(v_a_177_);
lean_dec(v___x_164_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_177_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
v___jp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = l_Lean_Expr_lam___override(v_x_132_, v_t_134_, v_b_135_, v_bi_133_);
v___x_144_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_143_, v___y_142_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_154_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
v_a_146_ = lean_ctor_get(v___x_144_, 1);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_154_ == 0)
{
v___x_148_ = v___x_144_;
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_inc(v_a_145_);
lean_dec(v___x_144_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v_a_145_);
lean_ctor_set(v___x_150_, 1, v___y_141_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_150_);
v___x_152_ = v___x_148_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_a_146_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
else
{
lean_object* v_a_155_; lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_dec_ref(v___y_141_);
v_a_155_ = lean_ctor_get(v___x_144_, 0);
v_a_156_ = lean_ctor_get(v___x_144_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_144_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_inc(v_a_155_);
lean_dec(v___x_144_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_155_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3___boxed(lean_object* v_x_186_, lean_object* v_bi_187_, lean_object* v_t_188_, lean_object* v_b_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
uint8_t v_bi_boxed_194_; uint8_t v___y_24242__boxed_195_; lean_object* v_res_196_; 
v_bi_boxed_194_ = lean_unbox(v_bi_187_);
v___y_24242__boxed_195_ = lean_unbox(v___y_191_);
v_res_196_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_x_186_, v_bi_boxed_194_, v_t_188_, v_b_189_, v___y_190_, v___y_24242__boxed_195_, v___y_192_, v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(lean_object* v_msg_204_, lean_object* v___y_205_, uint8_t v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___f_209_; lean_object* v___f_210_; lean_object* v___f_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_23770__overap_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___f_209_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0));
v___f_210_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1));
v___f_211_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2));
v___x_212_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3));
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v___f_209_);
v___x_214_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4));
v___x_215_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5));
v___x_216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_216_, 0, v___x_213_);
lean_ctor_set(v___x_216_, 1, v___x_214_);
lean_ctor_set(v___x_216_, 2, v___f_210_);
lean_ctor_set(v___x_216_, 3, v___f_211_);
lean_ctor_set(v___x_216_, 4, v___x_215_);
v___x_217_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6));
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = l_ReaderT_instMonad___redArg(v___x_218_);
v___x_220_ = l_ReaderT_instMonad___redArg(v___x_219_);
lean_inc_ref_n(v___x_220_, 6);
v___f_221_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_221_, 0, v___x_220_);
v___f_222_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_222_, 0, v___x_220_);
v___f_223_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_223_, 0, v___x_220_);
v___f_224_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_224_, 0, v___x_220_);
v___x_225_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_225_, 0, lean_box(0));
lean_closure_set(v___x_225_, 1, lean_box(0));
lean_closure_set(v___x_225_, 2, v___x_220_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___f_221_);
v___x_227_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_227_, 0, lean_box(0));
lean_closure_set(v___x_227_, 1, lean_box(0));
lean_closure_set(v___x_227_, 2, v___x_220_);
v___x_228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
lean_ctor_set(v___x_228_, 2, v___f_222_);
lean_ctor_set(v___x_228_, 3, v___f_223_);
lean_ctor_set(v___x_228_, 4, v___f_224_);
v___x_229_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_229_, 0, lean_box(0));
lean_closure_set(v___x_229_, 1, lean_box(0));
lean_closure_set(v___x_229_, 2, v___x_220_);
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = l_Lean_instInhabitedExpr;
v___x_232_ = l_instInhabitedOfMonad___redArg(v___x_230_, v___x_231_);
v___x_23770__overap_233_ = lean_panic_fn_borrowed(v___x_232_, v_msg_204_);
lean_dec(v___x_232_);
v___x_234_ = lean_box(v___y_206_);
lean_inc_ref(v___y_207_);
v___x_235_ = lean_apply_4(v___x_23770__overap_233_, v___y_205_, v___x_234_, v___y_207_, v___y_208_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___boxed(lean_object* v_msg_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
uint8_t v___y_24362__boxed_241_; lean_object* v_res_242_; 
v___y_24362__boxed_241_ = lean_unbox(v___y_238_);
v_res_242_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v_msg_236_, v___y_237_, v___y_24362__boxed_241_, v___y_239_, v___y_240_);
lean_dec_ref(v___y_239_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(lean_object* v_f_243_, lean_object* v_a_244_, lean_object* v___y_245_, uint8_t v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v___y_250_; lean_object* v___y_251_; 
if (v___y_246_ == 0)
{
v___y_250_ = v___y_245_;
v___y_251_ = v___y_248_;
goto v___jp_249_;
}
else
{
lean_object* v___x_273_; 
lean_inc_ref(v_f_243_);
v___x_273_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_243_, v___y_246_, v___y_247_, v___y_248_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_275_; 
v_a_274_ = lean_ctor_get(v___x_273_, 1);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_273_, 2);
lean_inc_ref(v_a_244_);
v___x_275_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_244_, v___y_246_, v___y_247_, v_a_274_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; 
v_a_276_ = lean_ctor_get(v___x_275_, 1);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 2);
v___y_250_ = v___y_245_;
v___y_251_ = v_a_276_;
goto v___jp_249_;
}
else
{
lean_object* v_a_277_; lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v___y_245_);
lean_dec_ref(v_a_244_);
lean_dec_ref(v_f_243_);
v_a_277_ = lean_ctor_get(v___x_275_, 0);
v_a_278_ = lean_ctor_get(v___x_275_, 1);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_275_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_inc(v_a_277_);
lean_dec(v___x_275_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_277_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec_ref(v___y_245_);
lean_dec_ref(v_a_244_);
lean_dec_ref(v_f_243_);
v_a_286_ = lean_ctor_get(v___x_273_, 0);
v_a_287_ = lean_ctor_get(v___x_273_, 1);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_273_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_inc(v_a_286_);
lean_dec(v___x_273_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_286_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
v___jp_249_:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = l_Lean_Expr_app___override(v_f_243_, v_a_244_);
v___x_253_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_252_, v___y_251_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_263_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
v_a_255_ = lean_ctor_get(v___x_253_, 1);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_263_ == 0)
{
v___x_257_ = v___x_253_;
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_inc(v_a_254_);
lean_dec(v___x_253_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v_a_254_);
lean_ctor_set(v___x_259_, 1, v___y_250_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_259_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_a_255_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
else
{
lean_object* v_a_264_; lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec_ref(v___y_250_);
v_a_264_ = lean_ctor_get(v___x_253_, 0);
v_a_265_ = lean_ctor_get(v___x_253_, 1);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_253_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_inc(v_a_264_);
lean_dec(v___x_253_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_264_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2___boxed(lean_object* v_f_295_, lean_object* v_a_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
uint8_t v___y_24433__boxed_301_; lean_object* v_res_302_; 
v___y_24433__boxed_301_ = lean_unbox(v___y_298_);
v_res_302_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_f_295_, v_a_296_, v___y_297_, v___y_24433__boxed_301_, v___y_299_, v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(lean_object* v_a_303_, lean_object* v_x_304_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
lean_object* v___x_305_; 
v___x_305_ = lean_box(0);
return v___x_305_;
}
else
{
lean_object* v_key_306_; lean_object* v_value_307_; lean_object* v_tail_308_; uint8_t v___y_310_; lean_object* v_fst_313_; lean_object* v_snd_314_; lean_object* v_fst_315_; lean_object* v_snd_316_; uint8_t v___x_317_; 
v_key_306_ = lean_ctor_get(v_x_304_, 0);
v_value_307_ = lean_ctor_get(v_x_304_, 1);
v_tail_308_ = lean_ctor_get(v_x_304_, 2);
v_fst_313_ = lean_ctor_get(v_key_306_, 0);
v_snd_314_ = lean_ctor_get(v_key_306_, 1);
v_fst_315_ = lean_ctor_get(v_a_303_, 0);
v_snd_316_ = lean_ctor_get(v_a_303_, 1);
v___x_317_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_313_, v_fst_315_);
if (v___x_317_ == 0)
{
v___y_310_ = v___x_317_;
goto v___jp_309_;
}
else
{
uint8_t v___x_318_; 
v___x_318_ = lean_nat_dec_eq(v_snd_314_, v_snd_316_);
v___y_310_ = v___x_318_;
goto v___jp_309_;
}
v___jp_309_:
{
if (v___y_310_ == 0)
{
v_x_304_ = v_tail_308_;
goto _start;
}
else
{
lean_object* v___x_312_; 
lean_inc(v_value_307_);
v___x_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_312_, 0, v_value_307_);
return v___x_312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg___boxed(lean_object* v_a_319_, lean_object* v_x_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_319_, v_x_320_);
lean_dec(v_x_320_);
lean_dec_ref(v_a_319_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(lean_object* v_m_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_buckets_324_; lean_object* v_fst_325_; lean_object* v_snd_326_; lean_object* v___x_327_; uint64_t v___x_328_; uint64_t v___x_329_; uint64_t v___x_330_; uint64_t v___x_331_; uint64_t v___x_332_; uint64_t v_fold_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; size_t v___x_337_; size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_buckets_324_ = lean_ctor_get(v_m_322_, 1);
v_fst_325_ = lean_ctor_get(v_a_323_, 0);
v_snd_326_ = lean_ctor_get(v_a_323_, 1);
v___x_327_ = lean_array_get_size(v_buckets_324_);
v___x_328_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_325_);
v___x_329_ = lean_uint64_of_nat(v_snd_326_);
v___x_330_ = lean_uint64_mix_hash(v___x_328_, v___x_329_);
v___x_331_ = 32ULL;
v___x_332_ = lean_uint64_shift_right(v___x_330_, v___x_331_);
v_fold_333_ = lean_uint64_xor(v___x_330_, v___x_332_);
v___x_334_ = 16ULL;
v___x_335_ = lean_uint64_shift_right(v_fold_333_, v___x_334_);
v___x_336_ = lean_uint64_xor(v_fold_333_, v___x_335_);
v___x_337_ = lean_uint64_to_usize(v___x_336_);
v___x_338_ = lean_usize_of_nat(v___x_327_);
v___x_339_ = ((size_t)1ULL);
v___x_340_ = lean_usize_sub(v___x_338_, v___x_339_);
v___x_341_ = lean_usize_land(v___x_337_, v___x_340_);
v___x_342_ = lean_array_uget_borrowed(v_buckets_324_, v___x_341_);
v___x_343_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_323_, v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_m_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_344_, v_a_345_);
lean_dec_ref(v_a_345_);
lean_dec_ref(v_m_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(lean_object* v_x_347_, lean_object* v_t_348_, lean_object* v_v_349_, lean_object* v_b_350_, uint8_t v_nondep_351_, lean_object* v___y_352_, uint8_t v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___y_357_; lean_object* v___y_358_; 
if (v___y_353_ == 0)
{
v___y_357_ = v___y_352_;
v___y_358_ = v___y_355_;
goto v___jp_356_;
}
else
{
lean_object* v___x_380_; 
lean_inc_ref(v_t_348_);
v___x_380_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_348_, v___y_353_, v___y_354_, v___y_355_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_382_; 
v_a_381_ = lean_ctor_get(v___x_380_, 1);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_380_, 2);
lean_inc_ref(v_v_349_);
v___x_382_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_349_, v___y_353_, v___y_354_, v_a_381_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_384_; 
v_a_383_ = lean_ctor_get(v___x_382_, 1);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_382_, 2);
lean_inc_ref(v_b_350_);
v___x_384_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_350_, v___y_353_, v___y_354_, v_a_383_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; 
v_a_385_ = lean_ctor_get(v___x_384_, 1);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 2);
v___y_357_ = v___y_352_;
v___y_358_ = v_a_385_;
goto v___jp_356_;
}
else
{
lean_object* v_a_386_; lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec_ref(v___y_352_);
lean_dec_ref(v_b_350_);
lean_dec_ref(v_v_349_);
lean_dec_ref(v_t_348_);
lean_dec(v_x_347_);
v_a_386_ = lean_ctor_get(v___x_384_, 0);
v_a_387_ = lean_ctor_get(v___x_384_, 1);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_384_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_inc(v_a_386_);
lean_dec(v___x_384_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_386_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
else
{
lean_object* v_a_395_; lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec_ref(v___y_352_);
lean_dec_ref(v_b_350_);
lean_dec_ref(v_v_349_);
lean_dec_ref(v_t_348_);
lean_dec(v_x_347_);
v_a_395_ = lean_ctor_get(v___x_382_, 0);
v_a_396_ = lean_ctor_get(v___x_382_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_382_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_inc(v_a_395_);
lean_dec(v___x_382_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_395_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
else
{
lean_object* v_a_404_; lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref(v___y_352_);
lean_dec_ref(v_b_350_);
lean_dec_ref(v_v_349_);
lean_dec_ref(v_t_348_);
lean_dec(v_x_347_);
v_a_404_ = lean_ctor_get(v___x_380_, 0);
v_a_405_ = lean_ctor_get(v___x_380_, 1);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_380_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_inc(v_a_404_);
lean_dec(v___x_380_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_404_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
v___jp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = l_Lean_Expr_letE___override(v_x_347_, v_t_348_, v_v_349_, v_b_350_, v_nondep_351_);
v___x_360_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_359_, v___y_358_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_370_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_a_362_ = lean_ctor_get(v___x_360_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_370_ == 0)
{
v___x_364_ = v___x_360_;
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_a_361_);
lean_ctor_set(v___x_366_, 1, v___y_357_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_366_);
v___x_368_ = v___x_364_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_a_362_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v_a_371_; lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec_ref(v___y_357_);
v_a_371_ = lean_ctor_get(v___x_360_, 0);
v_a_372_ = lean_ctor_get(v___x_360_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_360_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_inc(v_a_371_);
lean_dec(v___x_360_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_371_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_a_372_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5___boxed(lean_object* v_x_413_, lean_object* v_t_414_, lean_object* v_v_415_, lean_object* v_b_416_, lean_object* v_nondep_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
uint8_t v_nondep_boxed_422_; uint8_t v___y_24608__boxed_423_; lean_object* v_res_424_; 
v_nondep_boxed_422_ = lean_unbox(v_nondep_417_);
v___y_24608__boxed_423_ = lean_unbox(v___y_419_);
v_res_424_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_x_413_, v_t_414_, v_v_415_, v_b_416_, v_nondep_boxed_422_, v___y_418_, v___y_24608__boxed_423_, v___y_420_, v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(lean_object* v_d_425_, lean_object* v_e_426_, lean_object* v___y_427_, uint8_t v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___y_432_; lean_object* v___y_433_; 
if (v___y_428_ == 0)
{
v___y_432_ = v___y_427_;
v___y_433_ = v___y_430_;
goto v___jp_431_;
}
else
{
lean_object* v___x_455_; 
lean_inc_ref(v_e_426_);
v___x_455_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_426_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; 
v_a_456_ = lean_ctor_get(v___x_455_, 1);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_455_, 2);
v___y_432_ = v___y_427_;
v___y_433_ = v_a_456_;
goto v___jp_431_;
}
else
{
lean_object* v_a_457_; lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec_ref(v___y_427_);
lean_dec_ref(v_e_426_);
lean_dec(v_d_425_);
v_a_457_ = lean_ctor_get(v___x_455_, 0);
v_a_458_ = lean_ctor_get(v___x_455_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_455_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_inc(v_a_457_);
lean_dec(v___x_455_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_457_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
v___jp_431_:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = l_Lean_Expr_mdata___override(v_d_425_, v_e_426_);
v___x_435_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_434_, v___y_433_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_445_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_a_437_ = lean_ctor_get(v___x_435_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_445_ == 0)
{
v___x_439_ = v___x_435_;
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v_a_436_);
lean_ctor_set(v___x_441_, 1, v___y_432_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_441_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_a_437_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
else
{
lean_object* v_a_446_; lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec_ref(v___y_432_);
v_a_446_ = lean_ctor_get(v___x_435_, 0);
v_a_447_ = lean_ctor_get(v___x_435_, 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_435_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_inc(v_a_446_);
lean_dec(v___x_435_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_446_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6___boxed(lean_object* v_d_466_, lean_object* v_e_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
uint8_t v___y_24737__boxed_472_; lean_object* v_res_473_; 
v___y_24737__boxed_472_ = lean_unbox(v___y_469_);
v_res_473_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_d_466_, v_e_467_, v___y_468_, v___y_24737__boxed_472_, v___y_470_, v___y_471_);
lean_dec_ref(v___y_470_);
return v_res_473_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_477_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2));
v___x_478_ = lean_unsigned_to_nat(67u);
v___x_479_ = lean_unsigned_to_nat(35u);
v___x_480_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1));
v___x_481_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0));
v___x_482_ = l_mkPanicMessageWithDecl(v___x_481_, v___x_480_, v___x_479_, v___x_478_, v___x_477_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(lean_object* v_s_483_, lean_object* v_d_484_, lean_object* v_e_485_, lean_object* v_offset_486_, lean_object* v_a_487_, uint8_t v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
switch(lean_obj_tag(v_e_485_))
{
case 5:
{
lean_object* v_fn_491_; lean_object* v_arg_492_; lean_object* v___x_493_; 
v_fn_491_ = lean_ctor_get(v_e_485_, 0);
v_arg_492_ = lean_ctor_get(v_e_485_, 1);
lean_inc(v_offset_486_);
lean_inc_ref(v_fn_491_);
v___x_493_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_483_, v_d_484_, v_fn_491_, v_offset_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v_a_495_; lean_object* v_fst_496_; lean_object* v_snd_497_; lean_object* v___x_498_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
v_a_495_ = lean_ctor_get(v___x_493_, 1);
lean_inc(v_a_495_);
lean_dec_ref_known(v___x_493_, 2);
v_fst_496_ = lean_ctor_get(v_a_494_, 0);
lean_inc(v_fst_496_);
v_snd_497_ = lean_ctor_get(v_a_494_, 1);
lean_inc(v_snd_497_);
lean_dec(v_a_494_);
lean_inc_ref(v_arg_492_);
v___x_498_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_483_, v_d_484_, v_arg_492_, v_offset_486_, v_snd_497_, v_a_488_, v_a_489_, v_a_495_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_521_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_a_500_ = lean_ctor_get(v___x_498_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_521_ == 0)
{
v___x_502_ = v___x_498_;
v_isShared_503_ = v_isSharedCheck_521_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_521_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v_fst_504_; lean_object* v_snd_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_520_; 
v_fst_504_ = lean_ctor_get(v_a_499_, 0);
v_snd_505_ = lean_ctor_get(v_a_499_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_a_499_);
if (v_isSharedCheck_520_ == 0)
{
v___x_507_ = v_a_499_;
v_isShared_508_ = v_isSharedCheck_520_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_snd_505_);
lean_inc(v_fst_504_);
lean_dec(v_a_499_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_520_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
uint8_t v___y_510_; uint8_t v___x_518_; 
v___x_518_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_491_, v_fst_496_);
if (v___x_518_ == 0)
{
v___y_510_ = v___x_518_;
goto v___jp_509_;
}
else
{
uint8_t v___x_519_; 
v___x_519_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_492_, v_fst_504_);
v___y_510_ = v___x_519_;
goto v___jp_509_;
}
v___jp_509_:
{
if (v___y_510_ == 0)
{
lean_object* v___x_511_; 
lean_del_object(v___x_507_);
lean_del_object(v___x_502_);
lean_dec_ref_known(v_e_485_, 2);
v___x_511_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_496_, v_fst_504_, v_snd_505_, v_a_488_, v_a_489_, v_a_500_);
return v___x_511_;
}
else
{
lean_object* v___x_513_; 
lean_dec(v_fst_504_);
lean_dec(v_fst_496_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v_e_485_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_e_485_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_snd_505_);
v___x_513_ = v_reuseFailAlloc_517_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_515_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_513_);
v___x_515_ = v___x_502_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_a_500_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_496_);
lean_dec_ref_known(v_e_485_, 2);
return v___x_498_;
}
}
else
{
lean_dec_ref_known(v_e_485_, 2);
lean_dec(v_offset_486_);
return v___x_493_;
}
}
case 6:
{
lean_object* v_binderName_522_; lean_object* v_binderType_523_; lean_object* v_body_524_; uint8_t v_binderInfo_525_; lean_object* v___x_526_; 
v_binderName_522_ = lean_ctor_get(v_e_485_, 0);
v_binderType_523_ = lean_ctor_get(v_e_485_, 1);
v_body_524_ = lean_ctor_get(v_e_485_, 2);
v_binderInfo_525_ = lean_ctor_get_uint8(v_e_485_, sizeof(void*)*3 + 8);
lean_inc(v_offset_486_);
lean_inc_ref(v_binderType_523_);
v___x_526_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_483_, v_d_484_, v_binderType_523_, v_offset_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v_a_528_; lean_object* v_fst_529_; lean_object* v_snd_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
v_a_528_ = lean_ctor_get(v___x_526_, 1);
lean_inc(v_a_528_);
lean_dec_ref_known(v___x_526_, 2);
v_fst_529_ = lean_ctor_get(v_a_527_, 0);
lean_inc(v_fst_529_);
v_snd_530_ = lean_ctor_get(v_a_527_, 1);
lean_inc(v_snd_530_);
lean_dec(v_a_527_);
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_nat_add(v_offset_486_, v___x_531_);
lean_dec(v_offset_486_);
lean_inc_ref(v_body_524_);
v___x_533_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_483_, v_d_484_, v_body_524_, v___x_532_, v_snd_530_, v_a_488_, v_a_489_, v_a_528_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_556_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_a_535_ = lean_ctor_get(v___x_533_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_556_ == 0)
{
v___x_537_ = v___x_533_;
v_isShared_538_ = v_isSharedCheck_556_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_556_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v_fst_539_; lean_object* v_snd_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_555_; 
v_fst_539_ = lean_ctor_get(v_a_534_, 0);
v_snd_540_ = lean_ctor_get(v_a_534_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v_a_534_);
if (v_isSharedCheck_555_ == 0)
{
v___x_542_ = v_a_534_;
v_isShared_543_ = v_isSharedCheck_555_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_snd_540_);
lean_inc(v_fst_539_);
lean_dec(v_a_534_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_555_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
uint8_t v___y_545_; uint8_t v___x_553_; 
v___x_553_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_523_, v_fst_529_);
if (v___x_553_ == 0)
{
v___y_545_ = v___x_553_;
goto v___jp_544_;
}
else
{
uint8_t v___x_554_; 
v___x_554_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_524_, v_fst_539_);
v___y_545_ = v___x_554_;
goto v___jp_544_;
}
v___jp_544_:
{
if (v___y_545_ == 0)
{
lean_object* v___x_546_; 
lean_inc(v_binderName_522_);
lean_del_object(v___x_542_);
lean_del_object(v___x_537_);
lean_dec_ref_known(v_e_485_, 3);
v___x_546_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_522_, v_binderInfo_525_, v_fst_529_, v_fst_539_, v_snd_540_, v_a_488_, v_a_489_, v_a_535_);
return v___x_546_;
}
else
{
lean_object* v___x_548_; 
lean_dec(v_fst_539_);
lean_dec(v_fst_529_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v_e_485_);
v___x_548_ = v___x_542_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_e_485_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_snd_540_);
v___x_548_ = v_reuseFailAlloc_552_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_550_; 
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_548_);
v___x_550_ = v___x_537_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_a_535_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_529_);
lean_dec_ref_known(v_e_485_, 3);
return v___x_533_;
}
}
else
{
lean_dec_ref_known(v_e_485_, 3);
lean_dec(v_offset_486_);
return v___x_526_;
}
}
case 7:
{
lean_object* v_binderName_557_; lean_object* v_binderType_558_; lean_object* v_body_559_; uint8_t v_binderInfo_560_; lean_object* v___x_561_; 
v_binderName_557_ = lean_ctor_get(v_e_485_, 0);
v_binderType_558_ = lean_ctor_get(v_e_485_, 1);
v_body_559_ = lean_ctor_get(v_e_485_, 2);
v_binderInfo_560_ = lean_ctor_get_uint8(v_e_485_, sizeof(void*)*3 + 8);
lean_inc(v_offset_486_);
lean_inc_ref(v_binderType_558_);
v___x_561_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_483_, v_d_484_, v_binderType_558_, v_offset_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v_a_563_; lean_object* v_fst_564_; lean_object* v_snd_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
v_a_563_ = lean_ctor_get(v___x_561_, 1);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_561_, 2);
v_fst_564_ = lean_ctor_get(v_a_562_, 0);
lean_inc(v_fst_564_);
v_snd_565_ = lean_ctor_get(v_a_562_, 1);
lean_inc(v_snd_565_);
lean_dec(v_a_562_);
v___x_566_ = lean_unsigned_to_nat(1u);
v___x_567_ = lean_nat_add(v_offset_486_, v___x_566_);
lean_dec(v_offset_486_);
lean_inc_ref(v_body_559_);
v___x_568_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_483_, v_d_484_, v_body_559_, v___x_567_, v_snd_565_, v_a_488_, v_a_489_, v_a_563_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_591_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_a_570_ = lean_ctor_get(v___x_568_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_591_ == 0)
{
v___x_572_ = v___x_568_;
v_isShared_573_ = v_isSharedCheck_591_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_591_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v_fst_574_; lean_object* v_snd_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_590_; 
v_fst_574_ = lean_ctor_get(v_a_569_, 0);
v_snd_575_ = lean_ctor_get(v_a_569_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v_a_569_);
if (v_isSharedCheck_590_ == 0)
{
v___x_577_ = v_a_569_;
v_isShared_578_ = v_isSharedCheck_590_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_snd_575_);
lean_inc(v_fst_574_);
lean_dec(v_a_569_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_590_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
uint8_t v___y_580_; uint8_t v___x_588_; 
v___x_588_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_558_, v_fst_564_);
if (v___x_588_ == 0)
{
v___y_580_ = v___x_588_;
goto v___jp_579_;
}
else
{
uint8_t v___x_589_; 
v___x_589_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_559_, v_fst_574_);
v___y_580_ = v___x_589_;
goto v___jp_579_;
}
v___jp_579_:
{
if (v___y_580_ == 0)
{
lean_object* v___x_581_; 
lean_inc(v_binderName_557_);
lean_del_object(v___x_577_);
lean_del_object(v___x_572_);
lean_dec_ref_known(v_e_485_, 3);
v___x_581_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_557_, v_binderInfo_560_, v_fst_564_, v_fst_574_, v_snd_575_, v_a_488_, v_a_489_, v_a_570_);
return v___x_581_;
}
else
{
lean_object* v___x_583_; 
lean_dec(v_fst_574_);
lean_dec(v_fst_564_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v_e_485_);
v___x_583_ = v___x_577_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_e_485_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_snd_575_);
v___x_583_ = v_reuseFailAlloc_587_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_585_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_583_);
v___x_585_ = v___x_572_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_a_570_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_564_);
lean_dec_ref_known(v_e_485_, 3);
return v___x_568_;
}
}
else
{
lean_dec_ref_known(v_e_485_, 3);
lean_dec(v_offset_486_);
return v___x_561_;
}
}
case 8:
{
lean_object* v_declName_592_; lean_object* v_type_593_; lean_object* v_value_594_; lean_object* v_body_595_; uint8_t v_nondep_596_; lean_object* v___x_597_; 
v_declName_592_ = lean_ctor_get(v_e_485_, 0);
v_type_593_ = lean_ctor_get(v_e_485_, 1);
v_value_594_ = lean_ctor_get(v_e_485_, 2);
v_body_595_ = lean_ctor_get(v_e_485_, 3);
v_nondep_596_ = lean_ctor_get_uint8(v_e_485_, sizeof(void*)*4 + 8);
lean_inc(v_offset_486_);
lean_inc_ref(v_type_593_);
v___x_597_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_483_, v_d_484_, v_type_593_, v_offset_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v_a_599_; lean_object* v_fst_600_; lean_object* v_snd_601_; lean_object* v___x_602_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
v_a_599_ = lean_ctor_get(v___x_597_, 1);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_597_, 2);
v_fst_600_ = lean_ctor_get(v_a_598_, 0);
lean_inc(v_fst_600_);
v_snd_601_ = lean_ctor_get(v_a_598_, 1);
lean_inc(v_snd_601_);
lean_dec(v_a_598_);
lean_inc(v_offset_486_);
lean_inc_ref(v_value_594_);
v___x_602_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_483_, v_d_484_, v_value_594_, v_offset_486_, v_snd_601_, v_a_488_, v_a_489_, v_a_599_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v_a_604_; lean_object* v_fst_605_; lean_object* v_snd_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
v_a_604_ = lean_ctor_get(v___x_602_, 1);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_602_, 2);
v_fst_605_ = lean_ctor_get(v_a_603_, 0);
lean_inc(v_fst_605_);
v_snd_606_ = lean_ctor_get(v_a_603_, 1);
lean_inc(v_snd_606_);
lean_dec(v_a_603_);
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = lean_nat_add(v_offset_486_, v___x_607_);
lean_dec(v_offset_486_);
lean_inc_ref(v_body_595_);
v___x_609_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_483_, v_d_484_, v_body_595_, v___x_608_, v_snd_606_, v_a_488_, v_a_489_, v_a_604_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_634_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_a_611_ = lean_ctor_get(v___x_609_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_634_ == 0)
{
v___x_613_ = v___x_609_;
v_isShared_614_ = v_isSharedCheck_634_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_634_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_fst_615_; lean_object* v_snd_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_633_; 
v_fst_615_ = lean_ctor_get(v_a_610_, 0);
v_snd_616_ = lean_ctor_get(v_a_610_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_a_610_);
if (v_isSharedCheck_633_ == 0)
{
v___x_618_ = v_a_610_;
v_isShared_619_ = v_isSharedCheck_633_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_snd_616_);
lean_inc(v_fst_615_);
lean_dec(v_a_610_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_633_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
uint8_t v___y_621_; uint8_t v___x_631_; 
v___x_631_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_593_, v_fst_600_);
if (v___x_631_ == 0)
{
v___y_621_ = v___x_631_;
goto v___jp_620_;
}
else
{
uint8_t v___x_632_; 
v___x_632_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_594_, v_fst_605_);
v___y_621_ = v___x_632_;
goto v___jp_620_;
}
v___jp_620_:
{
if (v___y_621_ == 0)
{
lean_object* v___x_622_; 
lean_inc(v_declName_592_);
lean_del_object(v___x_618_);
lean_del_object(v___x_613_);
lean_dec_ref_known(v_e_485_, 4);
v___x_622_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_592_, v_fst_600_, v_fst_605_, v_fst_615_, v_nondep_596_, v_snd_616_, v_a_488_, v_a_489_, v_a_611_);
return v___x_622_;
}
else
{
uint8_t v___x_623_; 
v___x_623_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_595_, v_fst_615_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
lean_inc(v_declName_592_);
lean_del_object(v___x_618_);
lean_del_object(v___x_613_);
lean_dec_ref_known(v_e_485_, 4);
v___x_624_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_592_, v_fst_600_, v_fst_605_, v_fst_615_, v_nondep_596_, v_snd_616_, v_a_488_, v_a_489_, v_a_611_);
return v___x_624_;
}
else
{
lean_object* v___x_626_; 
lean_dec(v_fst_615_);
lean_dec(v_fst_605_);
lean_dec(v_fst_600_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v_e_485_);
v___x_626_ = v___x_618_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_e_485_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_snd_616_);
v___x_626_ = v_reuseFailAlloc_630_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_628_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_626_);
v___x_628_ = v___x_613_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_a_611_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_605_);
lean_dec(v_fst_600_);
lean_dec_ref_known(v_e_485_, 4);
return v___x_609_;
}
}
else
{
lean_dec(v_fst_600_);
lean_dec_ref_known(v_e_485_, 4);
lean_dec(v_offset_486_);
return v___x_602_;
}
}
else
{
lean_dec_ref_known(v_e_485_, 4);
lean_dec(v_offset_486_);
return v___x_597_;
}
}
case 10:
{
lean_object* v_data_635_; lean_object* v_expr_636_; lean_object* v___x_637_; 
v_data_635_ = lean_ctor_get(v_e_485_, 0);
v_expr_636_ = lean_ctor_get(v_e_485_, 1);
lean_inc_ref(v_expr_636_);
v___x_637_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_483_, v_d_484_, v_expr_636_, v_offset_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_657_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_a_639_ = lean_ctor_get(v___x_637_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_657_ == 0)
{
v___x_641_ = v___x_637_;
v_isShared_642_ = v_isSharedCheck_657_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_657_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_fst_643_; lean_object* v_snd_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_656_; 
v_fst_643_ = lean_ctor_get(v_a_638_, 0);
v_snd_644_ = lean_ctor_get(v_a_638_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_a_638_);
if (v_isSharedCheck_656_ == 0)
{
v___x_646_ = v_a_638_;
v_isShared_647_ = v_isSharedCheck_656_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_snd_644_);
lean_inc(v_fst_643_);
lean_dec(v_a_638_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_656_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
uint8_t v___x_648_; 
v___x_648_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_636_, v_fst_643_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; 
lean_inc(v_data_635_);
lean_del_object(v___x_646_);
lean_del_object(v___x_641_);
lean_dec_ref_known(v_e_485_, 2);
v___x_649_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_635_, v_fst_643_, v_snd_644_, v_a_488_, v_a_489_, v_a_639_);
return v___x_649_;
}
else
{
lean_object* v___x_651_; 
lean_dec(v_fst_643_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v_e_485_);
v___x_651_ = v___x_646_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_e_485_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_snd_644_);
v___x_651_ = v_reuseFailAlloc_655_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_651_);
v___x_653_ = v___x_641_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_a_639_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_485_, 2);
return v___x_637_;
}
}
case 11:
{
lean_object* v_typeName_658_; lean_object* v_idx_659_; lean_object* v_struct_660_; lean_object* v___x_661_; 
v_typeName_658_ = lean_ctor_get(v_e_485_, 0);
v_idx_659_ = lean_ctor_get(v_e_485_, 1);
v_struct_660_ = lean_ctor_get(v_e_485_, 2);
lean_inc_ref(v_struct_660_);
v___x_661_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_483_, v_d_484_, v_struct_660_, v_offset_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_681_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
v_a_663_ = lean_ctor_get(v___x_661_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_681_ == 0)
{
v___x_665_ = v___x_661_;
v_isShared_666_ = v_isSharedCheck_681_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_inc(v_a_662_);
lean_dec(v___x_661_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_681_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_fst_667_; lean_object* v_snd_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_680_; 
v_fst_667_ = lean_ctor_get(v_a_662_, 0);
v_snd_668_ = lean_ctor_get(v_a_662_, 1);
v_isSharedCheck_680_ = !lean_is_exclusive(v_a_662_);
if (v_isSharedCheck_680_ == 0)
{
v___x_670_ = v_a_662_;
v_isShared_671_ = v_isSharedCheck_680_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_snd_668_);
lean_inc(v_fst_667_);
lean_dec(v_a_662_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_680_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
uint8_t v___x_672_; 
v___x_672_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_660_, v_fst_667_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
lean_inc(v_idx_659_);
lean_inc(v_typeName_658_);
lean_del_object(v___x_670_);
lean_del_object(v___x_665_);
lean_dec_ref_known(v_e_485_, 3);
v___x_673_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_658_, v_idx_659_, v_fst_667_, v_snd_668_, v_a_488_, v_a_489_, v_a_663_);
return v___x_673_;
}
else
{
lean_object* v___x_675_; 
lean_dec(v_fst_667_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v_e_485_);
v___x_675_ = v___x_670_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_e_485_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_snd_668_);
v___x_675_ = v_reuseFailAlloc_679_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_677_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_675_);
v___x_677_ = v___x_665_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_a_663_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_485_, 3);
return v___x_661_;
}
}
default: 
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v_offset_486_);
lean_dec_ref(v_e_485_);
v___x_682_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
v___x_683_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_682_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
return v___x_683_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(lean_object* v_s_684_, lean_object* v_d_685_, lean_object* v_e_686_, lean_object* v_offset_687_, lean_object* v_a_688_, uint8_t v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_key_692_; lean_object* v_a_694_; lean_object* v___x_707_; 
lean_inc(v_offset_687_);
lean_inc_ref(v_e_686_);
v_key_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_692_, 0, v_e_686_);
lean_ctor_set(v_key_692_, 1, v_offset_687_);
v___x_707_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_688_, v_key_692_);
if (lean_obj_tag(v___x_707_) == 1)
{
lean_object* v_val_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec_ref_known(v_key_692_, 2);
lean_dec(v_offset_687_);
lean_dec_ref(v_e_686_);
v_val_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_val_708_);
lean_dec_ref_known(v___x_707_, 1);
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v_val_708_);
lean_ctor_set(v___x_709_, 1, v_a_688_);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v_a_691_);
return v___x_710_;
}
else
{
lean_object* v_s_u2081_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
lean_dec(v___x_707_);
v_s_u2081_711_ = lean_nat_add(v_s_684_, v_offset_687_);
v___x_712_ = l_Lean_Expr_looseBVarRange(v_e_686_);
v___x_713_ = lean_nat_dec_le(v___x_712_, v_s_u2081_711_);
lean_dec(v___x_712_);
if (v___x_713_ == 0)
{
if (lean_obj_tag(v_e_686_) == 0)
{
lean_object* v_deBruijnIndex_714_; uint8_t v___x_715_; 
v_deBruijnIndex_714_ = lean_ctor_get(v_e_686_, 0);
v___x_715_ = lean_nat_dec_le(v_s_u2081_711_, v_deBruijnIndex_714_);
lean_dec(v_s_u2081_711_);
if (v___x_715_ == 0)
{
v_a_694_ = v_a_691_;
goto v___jp_693_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_inc(v_deBruijnIndex_714_);
lean_dec_ref_known(v_e_686_, 1);
lean_dec(v_offset_687_);
v___x_716_ = lean_nat_sub(v_deBruijnIndex_714_, v_d_685_);
lean_dec(v_deBruijnIndex_714_);
v___x_717_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_716_, v_a_691_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v_a_719_; lean_object* v___x_720_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
v_a_719_ = lean_ctor_get(v___x_717_, 1);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_717_, 2);
v___x_720_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_692_, v_a_718_, v_a_688_, v_a_689_, v_a_690_, v_a_719_);
return v___x_720_;
}
else
{
lean_object* v_a_721_; lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec_ref_known(v_key_692_, 2);
lean_dec_ref(v_a_688_);
v_a_721_ = lean_ctor_get(v___x_717_, 0);
v_a_722_ = lean_ctor_get(v___x_717_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_717_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_inc(v_a_721_);
lean_dec(v___x_717_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_721_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
else
{
lean_dec(v_s_u2081_711_);
v_a_694_ = v_a_691_;
goto v___jp_693_;
}
}
else
{
lean_object* v___x_730_; 
lean_dec(v_s_u2081_711_);
lean_dec(v_offset_687_);
v___x_730_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_692_, v_e_686_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
return v___x_730_;
}
}
v___jp_693_:
{
switch(lean_obj_tag(v_e_686_))
{
case 9:
{
lean_object* v___x_695_; 
lean_dec(v_offset_687_);
v___x_695_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_692_, v_e_686_, v_a_688_, v_a_689_, v_a_690_, v_a_694_);
return v___x_695_;
}
case 2:
{
lean_object* v___x_696_; 
lean_dec(v_offset_687_);
v___x_696_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_692_, v_e_686_, v_a_688_, v_a_689_, v_a_690_, v_a_694_);
return v___x_696_;
}
case 0:
{
lean_object* v___x_697_; 
lean_dec(v_offset_687_);
v___x_697_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_692_, v_e_686_, v_a_688_, v_a_689_, v_a_690_, v_a_694_);
return v___x_697_;
}
case 1:
{
lean_object* v___x_698_; 
lean_dec(v_offset_687_);
v___x_698_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_692_, v_e_686_, v_a_688_, v_a_689_, v_a_690_, v_a_694_);
return v___x_698_;
}
case 4:
{
lean_object* v___x_699_; 
lean_dec(v_offset_687_);
v___x_699_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_692_, v_e_686_, v_a_688_, v_a_689_, v_a_690_, v_a_694_);
return v___x_699_;
}
case 3:
{
lean_object* v___x_700_; 
lean_dec(v_offset_687_);
v___x_700_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_692_, v_e_686_, v_a_688_, v_a_689_, v_a_690_, v_a_694_);
return v___x_700_;
}
default: 
{
lean_object* v___x_701_; 
v___x_701_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_684_, v_d_685_, v_e_686_, v_offset_687_, v_a_688_, v_a_689_, v_a_690_, v_a_694_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v_a_703_; lean_object* v_fst_704_; lean_object* v_snd_705_; lean_object* v___x_706_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
v_a_703_ = lean_ctor_get(v___x_701_, 1);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_701_, 2);
v_fst_704_ = lean_ctor_get(v_a_702_, 0);
lean_inc(v_fst_704_);
v_snd_705_ = lean_ctor_get(v_a_702_, 1);
lean_inc(v_snd_705_);
lean_dec(v_a_702_);
v___x_706_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_692_, v_fst_704_, v_snd_705_, v_a_689_, v_a_690_, v_a_703_);
return v___x_706_;
}
else
{
lean_dec_ref_known(v_key_692_, 2);
return v___x_701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1___boxed(lean_object* v_s_731_, lean_object* v_d_732_, lean_object* v_e_733_, lean_object* v_offset_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
uint8_t v_a_boxed_739_; lean_object* v_res_740_; 
v_a_boxed_739_ = lean_unbox(v_a_736_);
v_res_740_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_731_, v_d_732_, v_e_733_, v_offset_734_, v_a_735_, v_a_boxed_739_, v_a_737_, v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_d_732_);
lean_dec(v_s_731_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___boxed(lean_object* v_s_741_, lean_object* v_d_742_, lean_object* v_e_743_, lean_object* v_offset_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
uint8_t v_a_boxed_749_; lean_object* v_res_750_; 
v_a_boxed_749_ = lean_unbox(v_a_746_);
v_res_750_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_741_, v_d_742_, v_e_743_, v_offset_744_, v_a_745_, v_a_boxed_749_, v_a_747_, v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_d_742_);
lean_dec(v_s_741_);
return v_res_750_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = lean_box(0);
v___x_752_ = lean_unsigned_to_nat(16u);
v___x_753_ = lean_mk_array(v___x_752_, v___x_751_);
return v___x_753_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0);
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v___x_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27(lean_object* v_e_757_, lean_object* v_s_758_, lean_object* v_d_759_, uint8_t v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_763_ = l_Lean_Expr_looseBVarRange(v_e_757_);
v___x_764_ = lean_nat_dec_le(v___x_763_, v_s_758_);
lean_dec(v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v_a_767_; 
v___x_765_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_e_757_) == 0)
{
lean_object* v_deBruijnIndex_795_; uint8_t v___x_796_; 
v_deBruijnIndex_795_ = lean_ctor_get(v_e_757_, 0);
v___x_796_ = lean_nat_dec_le(v_s_758_, v_deBruijnIndex_795_);
if (v___x_796_ == 0)
{
v_a_767_ = v_a_762_;
goto v___jp_766_;
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; 
lean_inc(v_deBruijnIndex_795_);
lean_dec_ref_known(v_e_757_, 1);
v___x_797_ = lean_nat_sub(v_deBruijnIndex_795_, v_d_759_);
lean_dec(v_deBruijnIndex_795_);
v___x_798_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_797_, v_a_762_);
return v___x_798_;
}
}
else
{
v_a_767_ = v_a_762_;
goto v___jp_766_;
}
v___jp_766_:
{
switch(lean_obj_tag(v_e_757_))
{
case 9:
{
lean_object* v___x_768_; 
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v_e_757_);
lean_ctor_set(v___x_768_, 1, v_a_767_);
return v___x_768_;
}
case 2:
{
lean_object* v___x_769_; 
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v_e_757_);
lean_ctor_set(v___x_769_, 1, v_a_767_);
return v___x_769_;
}
case 0:
{
lean_object* v___x_770_; 
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v_e_757_);
lean_ctor_set(v___x_770_, 1, v_a_767_);
return v___x_770_;
}
case 1:
{
lean_object* v___x_771_; 
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_e_757_);
lean_ctor_set(v___x_771_, 1, v_a_767_);
return v___x_771_;
}
case 4:
{
lean_object* v___x_772_; 
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_e_757_);
lean_ctor_set(v___x_772_, 1, v_a_767_);
return v___x_772_;
}
case 3:
{
lean_object* v___x_773_; 
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v_e_757_);
lean_ctor_set(v___x_773_, 1, v_a_767_);
return v___x_773_;
}
default: 
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1);
v___x_775_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_758_, v_d_759_, v_e_757_, v___x_765_, v___x_774_, v_a_760_, v_a_761_, v_a_767_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_785_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
v_a_777_ = lean_ctor_get(v___x_775_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_785_ == 0)
{
v___x_779_ = v___x_775_;
v_isShared_780_ = v_isSharedCheck_785_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_inc(v_a_776_);
lean_dec(v___x_775_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_785_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v_fst_781_; lean_object* v___x_783_; 
v_fst_781_ = lean_ctor_get(v_a_776_, 0);
lean_inc(v_fst_781_);
lean_dec(v_a_776_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v_fst_781_);
v___x_783_ = v___x_779_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_fst_781_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_a_777_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
else
{
lean_object* v_a_786_; lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
v_a_786_ = lean_ctor_get(v___x_775_, 0);
v_a_787_ = lean_ctor_get(v___x_775_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_775_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_inc(v_a_786_);
lean_dec(v___x_775_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_786_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_799_; 
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v_e_757_);
lean_ctor_set(v___x_799_, 1, v_a_762_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed(lean_object* v_e_800_, lean_object* v_s_801_, lean_object* v_d_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
uint8_t v_a_boxed_806_; lean_object* v_res_807_; 
v_a_boxed_806_ = lean_unbox(v_a_803_);
v_res_807_ = l_Lean_Meta_Sym_lowerLooseBVarsS_x27(v_e_800_, v_s_801_, v_d_802_, v_a_boxed_806_, v_a_804_, v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_d_802_);
lean_dec(v_s_801_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_808_, lean_object* v_m_809_, lean_object* v_a_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_809_, v_a_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_812_, lean_object* v_m_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(v_00_u03b2_812_, v_m_813_, v_a_814_);
lean_dec_ref(v_a_814_);
lean_dec_ref(v_m_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(lean_object* v_00_u03b2_816_, lean_object* v_a_817_, lean_object* v_x_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_817_, v_x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___boxed(lean_object* v_00_u03b2_820_, lean_object* v_a_821_, lean_object* v_x_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(v_00_u03b2_820_, v_a_821_, v_x_822_);
lean_dec(v_x_822_);
lean_dec_ref(v_a_821_);
return v_res_823_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0(void){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(lean_object* v_msg_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_44__overap_834_; lean_object* v___x_835_; 
v___x_833_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0);
v___x_44__overap_834_ = lean_panic_fn_borrowed(v___x_833_, v_msg_825_);
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
lean_inc(v___y_829_);
lean_inc_ref(v___y_828_);
lean_inc(v___y_827_);
lean_inc_ref(v___y_826_);
v___x_835_ = lean_apply_7(v___x_44__overap_834_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, lean_box(0));
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___boxed(lean_object* v_msg_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(v_msg_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
return v_res_844_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_847_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2));
v___x_848_ = lean_unsigned_to_nat(16u);
v___x_849_ = lean_unsigned_to_nat(62u);
v___x_850_ = ((lean_object*)(l_Lean_Meta_Sym_lowerLooseBVarsS___closed__1));
v___x_851_ = ((lean_object*)(l_Lean_Meta_Sym_lowerLooseBVarsS___closed__0));
v___x_852_ = l_mkPanicMessageWithDecl(v___x_851_, v___x_850_, v___x_849_, v___x_848_, v___x_847_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS(lean_object* v_e_853_, lean_object* v_s_854_, lean_object* v_d_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v_debug_865_; lean_object* v_env_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_863_ = lean_st_ref_get(v_a_857_);
v___x_864_ = lean_st_ref_get(v_a_861_);
v_debug_865_ = lean_ctor_get_uint8(v___x_863_, sizeof(void*)*10);
lean_dec(v___x_863_);
v_env_866_ = lean_ctor_get(v___x_864_, 0);
lean_inc_ref(v_env_866_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(v_debug_865_);
v___x_868_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed), 6, 4);
lean_closure_set(v___x_868_, 0, v_e_853_);
lean_closure_set(v___x_868_, 1, v_s_854_);
lean_closure_set(v___x_868_, 2, v_d_855_);
lean_closure_set(v___x_868_, 3, v___x_867_);
v___x_869_ = 0;
v___x_870_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_870_, 0, v_env_866_);
lean_ctor_set_uint8(v___x_870_, sizeof(void*)*1, v___x_869_);
lean_ctor_set_uint8(v___x_870_, sizeof(void*)*1 + 1, v___x_869_);
v___x_871_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_868_, v___x_870_, v_a_857_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_882_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_882_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_882_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_882_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
if (lean_obj_tag(v_a_872_) == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; 
lean_dec_ref_known(v_a_872_, 1);
lean_del_object(v___x_874_);
v___x_876_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2, &l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2);
v___x_877_ = l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(v___x_876_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
return v___x_877_;
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; 
v_a_878_ = lean_ctor_get(v_a_872_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v_a_872_, 1);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v_a_878_);
v___x_880_ = v___x_874_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_a_883_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_871_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_871_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___boxed(lean_object* v_e_891_, lean_object* v_s_892_, lean_object* v_d_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_Meta_Sym_lowerLooseBVarsS(v_e_891_, v_s_892_, v_d_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(lean_object* v_s_902_, lean_object* v_d_903_, lean_object* v_e_904_, lean_object* v_offset_905_, lean_object* v_a_906_, uint8_t v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
switch(lean_obj_tag(v_e_904_))
{
case 5:
{
lean_object* v_fn_910_; lean_object* v_arg_911_; lean_object* v___x_912_; 
v_fn_910_ = lean_ctor_get(v_e_904_, 0);
v_arg_911_ = lean_ctor_get(v_e_904_, 1);
lean_inc(v_offset_905_);
lean_inc_ref(v_fn_910_);
v___x_912_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_902_, v_d_903_, v_fn_910_, v_offset_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v_a_914_; lean_object* v_fst_915_; lean_object* v_snd_916_; lean_object* v___x_917_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
v_a_914_ = lean_ctor_get(v___x_912_, 1);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_912_, 2);
v_fst_915_ = lean_ctor_get(v_a_913_, 0);
lean_inc(v_fst_915_);
v_snd_916_ = lean_ctor_get(v_a_913_, 1);
lean_inc(v_snd_916_);
lean_dec(v_a_913_);
lean_inc_ref(v_arg_911_);
v___x_917_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_902_, v_d_903_, v_arg_911_, v_offset_905_, v_snd_916_, v_a_907_, v_a_908_, v_a_914_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_940_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_a_919_ = lean_ctor_get(v___x_917_, 1);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_940_ == 0)
{
v___x_921_ = v___x_917_;
v_isShared_922_ = v_isSharedCheck_940_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_940_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v_fst_923_; lean_object* v_snd_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_939_; 
v_fst_923_ = lean_ctor_get(v_a_918_, 0);
v_snd_924_ = lean_ctor_get(v_a_918_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_a_918_);
if (v_isSharedCheck_939_ == 0)
{
v___x_926_ = v_a_918_;
v_isShared_927_ = v_isSharedCheck_939_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_snd_924_);
lean_inc(v_fst_923_);
lean_dec(v_a_918_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_939_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
uint8_t v___y_929_; uint8_t v___x_937_; 
v___x_937_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_910_, v_fst_915_);
if (v___x_937_ == 0)
{
v___y_929_ = v___x_937_;
goto v___jp_928_;
}
else
{
uint8_t v___x_938_; 
v___x_938_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_911_, v_fst_923_);
v___y_929_ = v___x_938_;
goto v___jp_928_;
}
v___jp_928_:
{
if (v___y_929_ == 0)
{
lean_object* v___x_930_; 
lean_del_object(v___x_926_);
lean_del_object(v___x_921_);
lean_dec_ref_known(v_e_904_, 2);
v___x_930_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_915_, v_fst_923_, v_snd_924_, v_a_907_, v_a_908_, v_a_919_);
return v___x_930_;
}
else
{
lean_object* v___x_932_; 
lean_dec(v_fst_923_);
lean_dec(v_fst_915_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v_e_904_);
v___x_932_ = v___x_926_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_e_904_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_snd_924_);
v___x_932_ = v_reuseFailAlloc_936_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_934_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_932_);
v___x_934_ = v___x_921_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_a_919_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_915_);
lean_dec_ref_known(v_e_904_, 2);
return v___x_917_;
}
}
else
{
lean_dec_ref_known(v_e_904_, 2);
lean_dec(v_offset_905_);
return v___x_912_;
}
}
case 6:
{
lean_object* v_binderName_941_; lean_object* v_binderType_942_; lean_object* v_body_943_; uint8_t v_binderInfo_944_; lean_object* v___x_945_; 
v_binderName_941_ = lean_ctor_get(v_e_904_, 0);
v_binderType_942_ = lean_ctor_get(v_e_904_, 1);
v_body_943_ = lean_ctor_get(v_e_904_, 2);
v_binderInfo_944_ = lean_ctor_get_uint8(v_e_904_, sizeof(void*)*3 + 8);
lean_inc(v_offset_905_);
lean_inc_ref(v_binderType_942_);
v___x_945_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_902_, v_d_903_, v_binderType_942_, v_offset_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v_a_947_; lean_object* v_fst_948_; lean_object* v_snd_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
v_a_947_ = lean_ctor_get(v___x_945_, 1);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_945_, 2);
v_fst_948_ = lean_ctor_get(v_a_946_, 0);
lean_inc(v_fst_948_);
v_snd_949_ = lean_ctor_get(v_a_946_, 1);
lean_inc(v_snd_949_);
lean_dec(v_a_946_);
v___x_950_ = lean_unsigned_to_nat(1u);
v___x_951_ = lean_nat_add(v_offset_905_, v___x_950_);
lean_dec(v_offset_905_);
lean_inc_ref(v_body_943_);
v___x_952_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_902_, v_d_903_, v_body_943_, v___x_951_, v_snd_949_, v_a_907_, v_a_908_, v_a_947_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_975_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_a_954_ = lean_ctor_get(v___x_952_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_975_ == 0)
{
v___x_956_ = v___x_952_;
v_isShared_957_ = v_isSharedCheck_975_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_975_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_fst_958_; lean_object* v_snd_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_974_; 
v_fst_958_ = lean_ctor_get(v_a_953_, 0);
v_snd_959_ = lean_ctor_get(v_a_953_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v_a_953_);
if (v_isSharedCheck_974_ == 0)
{
v___x_961_ = v_a_953_;
v_isShared_962_ = v_isSharedCheck_974_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_snd_959_);
lean_inc(v_fst_958_);
lean_dec(v_a_953_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_974_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
uint8_t v___y_964_; uint8_t v___x_972_; 
v___x_972_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_942_, v_fst_948_);
if (v___x_972_ == 0)
{
v___y_964_ = v___x_972_;
goto v___jp_963_;
}
else
{
uint8_t v___x_973_; 
v___x_973_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_943_, v_fst_958_);
v___y_964_ = v___x_973_;
goto v___jp_963_;
}
v___jp_963_:
{
if (v___y_964_ == 0)
{
lean_object* v___x_965_; 
lean_inc(v_binderName_941_);
lean_del_object(v___x_961_);
lean_del_object(v___x_956_);
lean_dec_ref_known(v_e_904_, 3);
v___x_965_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_941_, v_binderInfo_944_, v_fst_948_, v_fst_958_, v_snd_959_, v_a_907_, v_a_908_, v_a_954_);
return v___x_965_;
}
else
{
lean_object* v___x_967_; 
lean_dec(v_fst_958_);
lean_dec(v_fst_948_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v_e_904_);
v___x_967_ = v___x_961_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_e_904_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_snd_959_);
v___x_967_ = v_reuseFailAlloc_971_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_969_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_967_);
v___x_969_ = v___x_956_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_a_954_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_948_);
lean_dec_ref_known(v_e_904_, 3);
return v___x_952_;
}
}
else
{
lean_dec_ref_known(v_e_904_, 3);
lean_dec(v_offset_905_);
return v___x_945_;
}
}
case 7:
{
lean_object* v_binderName_976_; lean_object* v_binderType_977_; lean_object* v_body_978_; uint8_t v_binderInfo_979_; lean_object* v___x_980_; 
v_binderName_976_ = lean_ctor_get(v_e_904_, 0);
v_binderType_977_ = lean_ctor_get(v_e_904_, 1);
v_body_978_ = lean_ctor_get(v_e_904_, 2);
v_binderInfo_979_ = lean_ctor_get_uint8(v_e_904_, sizeof(void*)*3 + 8);
lean_inc(v_offset_905_);
lean_inc_ref(v_binderType_977_);
v___x_980_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_902_, v_d_903_, v_binderType_977_, v_offset_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v_a_982_; lean_object* v_fst_983_; lean_object* v_snd_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
v_a_982_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_980_, 2);
v_fst_983_ = lean_ctor_get(v_a_981_, 0);
lean_inc(v_fst_983_);
v_snd_984_ = lean_ctor_get(v_a_981_, 1);
lean_inc(v_snd_984_);
lean_dec(v_a_981_);
v___x_985_ = lean_unsigned_to_nat(1u);
v___x_986_ = lean_nat_add(v_offset_905_, v___x_985_);
lean_dec(v_offset_905_);
lean_inc_ref(v_body_978_);
v___x_987_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_902_, v_d_903_, v_body_978_, v___x_986_, v_snd_984_, v_a_907_, v_a_908_, v_a_982_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1010_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_a_989_ = lean_ctor_get(v___x_987_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_991_ = v___x_987_;
v_isShared_992_ = v_isSharedCheck_1010_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1010_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v_fst_993_; lean_object* v_snd_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1009_; 
v_fst_993_ = lean_ctor_get(v_a_988_, 0);
v_snd_994_ = lean_ctor_get(v_a_988_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_a_988_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_996_ = v_a_988_;
v_isShared_997_ = v_isSharedCheck_1009_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_snd_994_);
lean_inc(v_fst_993_);
lean_dec(v_a_988_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1009_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
uint8_t v___y_999_; uint8_t v___x_1007_; 
v___x_1007_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_977_, v_fst_983_);
if (v___x_1007_ == 0)
{
v___y_999_ = v___x_1007_;
goto v___jp_998_;
}
else
{
uint8_t v___x_1008_; 
v___x_1008_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_978_, v_fst_993_);
v___y_999_ = v___x_1008_;
goto v___jp_998_;
}
v___jp_998_:
{
if (v___y_999_ == 0)
{
lean_object* v___x_1000_; 
lean_inc(v_binderName_976_);
lean_del_object(v___x_996_);
lean_del_object(v___x_991_);
lean_dec_ref_known(v_e_904_, 3);
v___x_1000_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_976_, v_binderInfo_979_, v_fst_983_, v_fst_993_, v_snd_994_, v_a_907_, v_a_908_, v_a_989_);
return v___x_1000_;
}
else
{
lean_object* v___x_1002_; 
lean_dec(v_fst_993_);
lean_dec(v_fst_983_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v_e_904_);
v___x_1002_ = v___x_996_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_e_904_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_snd_994_);
v___x_1002_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1004_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_1002_);
v___x_1004_ = v___x_991_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_a_989_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_983_);
lean_dec_ref_known(v_e_904_, 3);
return v___x_987_;
}
}
else
{
lean_dec_ref_known(v_e_904_, 3);
lean_dec(v_offset_905_);
return v___x_980_;
}
}
case 8:
{
lean_object* v_declName_1011_; lean_object* v_type_1012_; lean_object* v_value_1013_; lean_object* v_body_1014_; uint8_t v_nondep_1015_; lean_object* v___x_1016_; 
v_declName_1011_ = lean_ctor_get(v_e_904_, 0);
v_type_1012_ = lean_ctor_get(v_e_904_, 1);
v_value_1013_ = lean_ctor_get(v_e_904_, 2);
v_body_1014_ = lean_ctor_get(v_e_904_, 3);
v_nondep_1015_ = lean_ctor_get_uint8(v_e_904_, sizeof(void*)*4 + 8);
lean_inc(v_offset_905_);
lean_inc_ref(v_type_1012_);
v___x_1016_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_902_, v_d_903_, v_type_1012_, v_offset_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v_a_1018_; lean_object* v_fst_1019_; lean_object* v_snd_1020_; lean_object* v___x_1021_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
v_a_1018_ = lean_ctor_get(v___x_1016_, 1);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1016_, 2);
v_fst_1019_ = lean_ctor_get(v_a_1017_, 0);
lean_inc(v_fst_1019_);
v_snd_1020_ = lean_ctor_get(v_a_1017_, 1);
lean_inc(v_snd_1020_);
lean_dec(v_a_1017_);
lean_inc(v_offset_905_);
lean_inc_ref(v_value_1013_);
v___x_1021_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_902_, v_d_903_, v_value_1013_, v_offset_905_, v_snd_1020_, v_a_907_, v_a_908_, v_a_1018_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v_a_1023_; lean_object* v_fst_1024_; lean_object* v_snd_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
v_a_1023_ = lean_ctor_get(v___x_1021_, 1);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1021_, 2);
v_fst_1024_ = lean_ctor_get(v_a_1022_, 0);
lean_inc(v_fst_1024_);
v_snd_1025_ = lean_ctor_get(v_a_1022_, 1);
lean_inc(v_snd_1025_);
lean_dec(v_a_1022_);
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = lean_nat_add(v_offset_905_, v___x_1026_);
lean_dec(v_offset_905_);
lean_inc_ref(v_body_1014_);
v___x_1028_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_902_, v_d_903_, v_body_1014_, v___x_1027_, v_snd_1025_, v_a_907_, v_a_908_, v_a_1023_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1053_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_a_1030_ = lean_ctor_get(v___x_1028_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1032_ = v___x_1028_;
v_isShared_1033_ = v_isSharedCheck_1053_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1053_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_fst_1034_; lean_object* v_snd_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1052_; 
v_fst_1034_ = lean_ctor_get(v_a_1029_, 0);
v_snd_1035_ = lean_ctor_get(v_a_1029_, 1);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_a_1029_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1037_ = v_a_1029_;
v_isShared_1038_ = v_isSharedCheck_1052_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_snd_1035_);
lean_inc(v_fst_1034_);
lean_dec(v_a_1029_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1052_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
uint8_t v___y_1040_; uint8_t v___x_1050_; 
v___x_1050_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1012_, v_fst_1019_);
if (v___x_1050_ == 0)
{
v___y_1040_ = v___x_1050_;
goto v___jp_1039_;
}
else
{
uint8_t v___x_1051_; 
v___x_1051_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1013_, v_fst_1024_);
v___y_1040_ = v___x_1051_;
goto v___jp_1039_;
}
v___jp_1039_:
{
if (v___y_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_inc(v_declName_1011_);
lean_del_object(v___x_1037_);
lean_del_object(v___x_1032_);
lean_dec_ref_known(v_e_904_, 4);
v___x_1041_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1011_, v_fst_1019_, v_fst_1024_, v_fst_1034_, v_nondep_1015_, v_snd_1035_, v_a_907_, v_a_908_, v_a_1030_);
return v___x_1041_;
}
else
{
uint8_t v___x_1042_; 
v___x_1042_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1014_, v_fst_1034_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; 
lean_inc(v_declName_1011_);
lean_del_object(v___x_1037_);
lean_del_object(v___x_1032_);
lean_dec_ref_known(v_e_904_, 4);
v___x_1043_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1011_, v_fst_1019_, v_fst_1024_, v_fst_1034_, v_nondep_1015_, v_snd_1035_, v_a_907_, v_a_908_, v_a_1030_);
return v___x_1043_;
}
else
{
lean_object* v___x_1045_; 
lean_dec(v_fst_1034_);
lean_dec(v_fst_1024_);
lean_dec(v_fst_1019_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v_e_904_);
v___x_1045_ = v___x_1037_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_e_904_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_snd_1035_);
v___x_1045_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1047_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1045_);
v___x_1047_ = v___x_1032_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_a_1030_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1024_);
lean_dec(v_fst_1019_);
lean_dec_ref_known(v_e_904_, 4);
return v___x_1028_;
}
}
else
{
lean_dec(v_fst_1019_);
lean_dec_ref_known(v_e_904_, 4);
lean_dec(v_offset_905_);
return v___x_1021_;
}
}
else
{
lean_dec_ref_known(v_e_904_, 4);
lean_dec(v_offset_905_);
return v___x_1016_;
}
}
case 10:
{
lean_object* v_data_1054_; lean_object* v_expr_1055_; lean_object* v___x_1056_; 
v_data_1054_ = lean_ctor_get(v_e_904_, 0);
v_expr_1055_ = lean_ctor_get(v_e_904_, 1);
lean_inc_ref(v_expr_1055_);
v___x_1056_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_902_, v_d_903_, v_expr_1055_, v_offset_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1076_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_a_1058_ = lean_ctor_get(v___x_1056_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1060_ = v___x_1056_;
v_isShared_1061_ = v_isSharedCheck_1076_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1076_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v_fst_1062_; lean_object* v_snd_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1075_; 
v_fst_1062_ = lean_ctor_get(v_a_1057_, 0);
v_snd_1063_ = lean_ctor_get(v_a_1057_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_a_1057_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1065_ = v_a_1057_;
v_isShared_1066_ = v_isSharedCheck_1075_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_snd_1063_);
lean_inc(v_fst_1062_);
lean_dec(v_a_1057_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1075_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
uint8_t v___x_1067_; 
v___x_1067_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1055_, v_fst_1062_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
lean_inc(v_data_1054_);
lean_del_object(v___x_1065_);
lean_del_object(v___x_1060_);
lean_dec_ref_known(v_e_904_, 2);
v___x_1068_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_1054_, v_fst_1062_, v_snd_1063_, v_a_907_, v_a_908_, v_a_1058_);
return v___x_1068_;
}
else
{
lean_object* v___x_1070_; 
lean_dec(v_fst_1062_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v_e_904_);
v___x_1070_ = v___x_1065_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_e_904_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_snd_1063_);
v___x_1070_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1072_; 
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1070_);
v___x_1072_ = v___x_1060_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_a_1058_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_904_, 2);
return v___x_1056_;
}
}
case 11:
{
lean_object* v_typeName_1077_; lean_object* v_idx_1078_; lean_object* v_struct_1079_; lean_object* v___x_1080_; 
v_typeName_1077_ = lean_ctor_get(v_e_904_, 0);
v_idx_1078_ = lean_ctor_get(v_e_904_, 1);
v_struct_1079_ = lean_ctor_get(v_e_904_, 2);
lean_inc_ref(v_struct_1079_);
v___x_1080_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_902_, v_d_903_, v_struct_1079_, v_offset_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1100_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_a_1082_ = lean_ctor_get(v___x_1080_, 1);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1084_ = v___x_1080_;
v_isShared_1085_ = v_isSharedCheck_1100_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1100_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v_fst_1086_; lean_object* v_snd_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1099_; 
v_fst_1086_ = lean_ctor_get(v_a_1081_, 0);
v_snd_1087_ = lean_ctor_get(v_a_1081_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_a_1081_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1089_ = v_a_1081_;
v_isShared_1090_ = v_isSharedCheck_1099_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_snd_1087_);
lean_inc(v_fst_1086_);
lean_dec(v_a_1081_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1099_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
uint8_t v___x_1091_; 
v___x_1091_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1079_, v_fst_1086_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; 
lean_inc(v_idx_1078_);
lean_inc(v_typeName_1077_);
lean_del_object(v___x_1089_);
lean_del_object(v___x_1084_);
lean_dec_ref_known(v_e_904_, 3);
v___x_1092_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_1077_, v_idx_1078_, v_fst_1086_, v_snd_1087_, v_a_907_, v_a_908_, v_a_1082_);
return v___x_1092_;
}
else
{
lean_object* v___x_1094_; 
lean_dec(v_fst_1086_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v_e_904_);
v___x_1094_ = v___x_1089_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_e_904_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_snd_1087_);
v___x_1094_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1096_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1094_);
v___x_1096_ = v___x_1084_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_a_1082_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_904_, 3);
return v___x_1080_;
}
}
default: 
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_dec(v_offset_905_);
lean_dec_ref(v_e_904_);
v___x_1101_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
v___x_1102_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_1101_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
return v___x_1102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(lean_object* v_s_1103_, lean_object* v_d_1104_, lean_object* v_e_1105_, lean_object* v_offset_1106_, lean_object* v_a_1107_, uint8_t v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_key_1111_; lean_object* v_a_1113_; lean_object* v___x_1126_; 
lean_inc(v_offset_1106_);
lean_inc_ref(v_e_1105_);
v_key_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1111_, 0, v_e_1105_);
lean_ctor_set(v_key_1111_, 1, v_offset_1106_);
v___x_1126_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_1107_, v_key_1111_);
if (lean_obj_tag(v___x_1126_) == 1)
{
lean_object* v_val_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_dec_ref_known(v_key_1111_, 2);
lean_dec(v_offset_1106_);
lean_dec_ref(v_e_1105_);
v_val_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_val_1127_);
lean_dec_ref_known(v___x_1126_, 1);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v_val_1127_);
lean_ctor_set(v___x_1128_, 1, v_a_1107_);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v_a_1110_);
return v___x_1129_;
}
else
{
lean_object* v_s_u2081_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
lean_dec(v___x_1126_);
v_s_u2081_1130_ = lean_nat_add(v_s_1103_, v_offset_1106_);
v___x_1131_ = l_Lean_Expr_looseBVarRange(v_e_1105_);
v___x_1132_ = lean_nat_dec_le(v___x_1131_, v_s_u2081_1130_);
lean_dec(v___x_1131_);
if (v___x_1132_ == 0)
{
if (lean_obj_tag(v_e_1105_) == 0)
{
lean_object* v_deBruijnIndex_1133_; uint8_t v___x_1134_; 
v_deBruijnIndex_1133_ = lean_ctor_get(v_e_1105_, 0);
v___x_1134_ = lean_nat_dec_le(v_s_u2081_1130_, v_deBruijnIndex_1133_);
lean_dec(v_s_u2081_1130_);
if (v___x_1134_ == 0)
{
v_a_1113_ = v_a_1110_;
goto v___jp_1112_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_inc(v_deBruijnIndex_1133_);
lean_dec_ref_known(v_e_1105_, 1);
lean_dec(v_offset_1106_);
v___x_1135_ = lean_nat_add(v_deBruijnIndex_1133_, v_d_1104_);
lean_dec(v_deBruijnIndex_1133_);
v___x_1136_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_1135_, v_a_1110_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v_a_1138_; lean_object* v___x_1139_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
v_a_1138_ = lean_ctor_get(v___x_1136_, 1);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1136_, 2);
v___x_1139_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1111_, v_a_1137_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1138_);
return v___x_1139_;
}
else
{
lean_object* v_a_1140_; lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec_ref_known(v_key_1111_, 2);
lean_dec_ref(v_a_1107_);
v_a_1140_ = lean_ctor_get(v___x_1136_, 0);
v_a_1141_ = lean_ctor_get(v___x_1136_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1136_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_inc(v_a_1140_);
lean_dec(v___x_1136_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1140_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
else
{
lean_dec(v_s_u2081_1130_);
v_a_1113_ = v_a_1110_;
goto v___jp_1112_;
}
}
else
{
lean_object* v___x_1149_; 
lean_dec(v_s_u2081_1130_);
lean_dec(v_offset_1106_);
v___x_1149_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1111_, v_e_1105_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
return v___x_1149_;
}
}
v___jp_1112_:
{
switch(lean_obj_tag(v_e_1105_))
{
case 9:
{
lean_object* v___x_1114_; 
lean_dec(v_offset_1106_);
v___x_1114_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1111_, v_e_1105_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1113_);
return v___x_1114_;
}
case 2:
{
lean_object* v___x_1115_; 
lean_dec(v_offset_1106_);
v___x_1115_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1111_, v_e_1105_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1113_);
return v___x_1115_;
}
case 0:
{
lean_object* v___x_1116_; 
lean_dec(v_offset_1106_);
v___x_1116_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1111_, v_e_1105_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1113_);
return v___x_1116_;
}
case 1:
{
lean_object* v___x_1117_; 
lean_dec(v_offset_1106_);
v___x_1117_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1111_, v_e_1105_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1113_);
return v___x_1117_;
}
case 4:
{
lean_object* v___x_1118_; 
lean_dec(v_offset_1106_);
v___x_1118_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1111_, v_e_1105_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1113_);
return v___x_1118_;
}
case 3:
{
lean_object* v___x_1119_; 
lean_dec(v_offset_1106_);
v___x_1119_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1111_, v_e_1105_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1113_);
return v___x_1119_;
}
default: 
{
lean_object* v___x_1120_; 
v___x_1120_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_1103_, v_d_1104_, v_e_1105_, v_offset_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1113_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v_a_1122_; lean_object* v_fst_1123_; lean_object* v_snd_1124_; lean_object* v___x_1125_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
v_a_1122_ = lean_ctor_get(v___x_1120_, 1);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1120_, 2);
v_fst_1123_ = lean_ctor_get(v_a_1121_, 0);
lean_inc(v_fst_1123_);
v_snd_1124_ = lean_ctor_get(v_a_1121_, 1);
lean_inc(v_snd_1124_);
lean_dec(v_a_1121_);
v___x_1125_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1111_, v_fst_1123_, v_snd_1124_, v_a_1108_, v_a_1109_, v_a_1122_);
return v___x_1125_;
}
else
{
lean_dec_ref_known(v_key_1111_, 2);
return v___x_1120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0___boxed(lean_object* v_s_1150_, lean_object* v_d_1151_, lean_object* v_e_1152_, lean_object* v_offset_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
uint8_t v_a_boxed_1158_; lean_object* v_res_1159_; 
v_a_boxed_1158_ = lean_unbox(v_a_1155_);
v_res_1159_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1150_, v_d_1151_, v_e_1152_, v_offset_1153_, v_a_1154_, v_a_boxed_1158_, v_a_1156_, v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_d_1151_);
lean_dec(v_s_1150_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0___boxed(lean_object* v_s_1160_, lean_object* v_d_1161_, lean_object* v_e_1162_, lean_object* v_offset_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
uint8_t v_a_boxed_1168_; lean_object* v_res_1169_; 
v_a_boxed_1168_ = lean_unbox(v_a_1165_);
v_res_1169_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_1160_, v_d_1161_, v_e_1162_, v_offset_1163_, v_a_1164_, v_a_boxed_1168_, v_a_1166_, v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_d_1161_);
lean_dec(v_s_1160_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27(lean_object* v_e_1170_, lean_object* v_s_1171_, lean_object* v_d_1172_, uint8_t v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = l_Lean_Expr_looseBVarRange(v_e_1170_);
v___x_1177_ = lean_nat_dec_le(v___x_1176_, v_s_1171_);
lean_dec(v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v_a_1180_; 
v___x_1178_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_e_1170_) == 0)
{
lean_object* v_deBruijnIndex_1208_; uint8_t v___x_1209_; 
v_deBruijnIndex_1208_ = lean_ctor_get(v_e_1170_, 0);
v___x_1209_ = lean_nat_dec_le(v_s_1171_, v_deBruijnIndex_1208_);
if (v___x_1209_ == 0)
{
v_a_1180_ = v_a_1175_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_inc(v_deBruijnIndex_1208_);
lean_dec_ref_known(v_e_1170_, 1);
v___x_1210_ = lean_nat_add(v_deBruijnIndex_1208_, v_d_1172_);
lean_dec(v_deBruijnIndex_1208_);
v___x_1211_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_1210_, v_a_1175_);
return v___x_1211_;
}
}
else
{
v_a_1180_ = v_a_1175_;
goto v___jp_1179_;
}
v___jp_1179_:
{
switch(lean_obj_tag(v_e_1170_))
{
case 9:
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v_e_1170_);
lean_ctor_set(v___x_1181_, 1, v_a_1180_);
return v___x_1181_;
}
case 2:
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1182_, 0, v_e_1170_);
lean_ctor_set(v___x_1182_, 1, v_a_1180_);
return v___x_1182_;
}
case 0:
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v_e_1170_);
lean_ctor_set(v___x_1183_, 1, v_a_1180_);
return v___x_1183_;
}
case 1:
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v_e_1170_);
lean_ctor_set(v___x_1184_, 1, v_a_1180_);
return v___x_1184_;
}
case 4:
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1185_, 0, v_e_1170_);
lean_ctor_set(v___x_1185_, 1, v_a_1180_);
return v___x_1185_;
}
case 3:
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v_e_1170_);
lean_ctor_set(v___x_1186_, 1, v_a_1180_);
return v___x_1186_;
}
default: 
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1);
v___x_1188_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_1171_, v_d_1172_, v_e_1170_, v___x_1178_, v___x_1187_, v_a_1173_, v_a_1174_, v_a_1180_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1198_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
v_a_1190_ = lean_ctor_get(v___x_1188_, 1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1192_ = v___x_1188_;
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_inc(v_a_1189_);
lean_dec(v___x_1188_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_fst_1194_; lean_object* v___x_1196_; 
v_fst_1194_ = lean_ctor_get(v_a_1189_, 0);
lean_inc(v_fst_1194_);
lean_dec(v_a_1189_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v_fst_1194_);
v___x_1196_ = v___x_1192_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_fst_1194_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_a_1190_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
v_a_1199_ = lean_ctor_get(v___x_1188_, 0);
v_a_1200_ = lean_ctor_get(v___x_1188_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1188_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_inc(v_a_1199_);
lean_dec(v___x_1188_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1199_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v_e_1170_);
lean_ctor_set(v___x_1212_, 1, v_a_1175_);
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27___boxed(lean_object* v_e_1213_, lean_object* v_s_1214_, lean_object* v_d_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
uint8_t v_a_boxed_1219_; lean_object* v_res_1220_; 
v_a_boxed_1219_ = lean_unbox(v_a_1216_);
v_res_1220_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_e_1213_, v_s_1214_, v_d_1215_, v_a_boxed_1219_, v_a_1217_, v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_d_1215_);
lean_dec(v_s_1214_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS(lean_object* v_e_1221_, lean_object* v_s_1222_, lean_object* v_d_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v_debug_1233_; lean_object* v_env_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1231_ = lean_st_ref_get(v_a_1225_);
v___x_1232_ = lean_st_ref_get(v_a_1229_);
v_debug_1233_ = lean_ctor_get_uint8(v___x_1231_, sizeof(void*)*10);
lean_dec(v___x_1231_);
v_env_1234_ = lean_ctor_get(v___x_1232_, 0);
lean_inc_ref(v_env_1234_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(v_debug_1233_);
v___x_1236_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_liftLooseBVarsS_x27___boxed), 6, 4);
lean_closure_set(v___x_1236_, 0, v_e_1221_);
lean_closure_set(v___x_1236_, 1, v_s_1222_);
lean_closure_set(v___x_1236_, 2, v_d_1223_);
lean_closure_set(v___x_1236_, 3, v___x_1235_);
v___x_1237_ = 0;
v___x_1238_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1238_, 0, v_env_1234_);
lean_ctor_set_uint8(v___x_1238_, sizeof(void*)*1, v___x_1237_);
lean_ctor_set_uint8(v___x_1238_, sizeof(void*)*1 + 1, v___x_1237_);
v___x_1239_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_1236_, v___x_1238_, v_a_1225_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1250_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1250_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1250_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
if (lean_obj_tag(v_a_1240_) == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec_ref_known(v_a_1240_, 1);
lean_del_object(v___x_1242_);
v___x_1244_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2, &l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2);
v___x_1245_ = l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(v___x_1244_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
return v___x_1245_;
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; 
v_a_1246_ = lean_ctor_get(v_a_1240_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v_a_1240_, 1);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v_a_1246_);
v___x_1248_ = v___x_1242_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
v_a_1251_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1239_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1239_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___boxed(lean_object* v_e_1259_, lean_object* v_s_1260_, lean_object* v_d_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_Meta_Sym_liftLooseBVarsS(v_e_1259_, v_s_1260_, v_d_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
return v_res_1269_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_LooseBVarsS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_LooseBVarsS(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_LooseBVarsS(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
}
#ifdef __cplusplus
}
#endif
