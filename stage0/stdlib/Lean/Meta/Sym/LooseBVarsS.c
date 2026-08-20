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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*, lean_object*);
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
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
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
uint8_t v___y_24179__boxed_14_; lean_object* v_res_15_; 
v___y_24179__boxed_14_ = lean_unbox(v___y_11_);
v_res_15_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(v_idx_10_, v___y_24179__boxed_14_, v___y_12_, v___y_13_);
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
v___x_48_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_18_, v___y_21_, v___y_22_, v___y_23_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v_a_49_; lean_object* v___x_50_; 
v_a_49_ = lean_ctor_get(v___x_48_, 1);
lean_inc(v_a_49_);
lean_dec_ref_known(v___x_48_, 2);
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
uint8_t v_bi_boxed_78_; uint8_t v___y_24191__boxed_79_; lean_object* v_res_80_; 
v_bi_boxed_78_ = lean_unbox(v_bi_71_);
v___y_24191__boxed_79_ = lean_unbox(v___y_75_);
v_res_80_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_x_70_, v_bi_boxed_78_, v_t_72_, v_b_73_, v___y_74_, v___y_24191__boxed_79_, v___y_76_, v___y_77_);
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
uint8_t v___y_24297__boxed_130_; lean_object* v_res_131_; 
v___y_24297__boxed_130_ = lean_unbox(v___y_127_);
v_res_131_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_structName_123_, v_idx_124_, v_struct_125_, v___y_126_, v___y_24297__boxed_130_, v___y_128_, v___y_129_);
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
v___x_164_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_134_, v___y_137_, v___y_138_, v___y_139_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_166_; 
v_a_165_ = lean_ctor_get(v___x_164_, 1);
lean_inc(v_a_165_);
lean_dec_ref_known(v___x_164_, 2);
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
uint8_t v_bi_boxed_194_; uint8_t v___y_24380__boxed_195_; lean_object* v_res_196_; 
v_bi_boxed_194_ = lean_unbox(v_bi_187_);
v___y_24380__boxed_195_ = lean_unbox(v___y_191_);
v_res_196_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_x_186_, v_bi_boxed_194_, v_t_188_, v_b_189_, v___y_190_, v___y_24380__boxed_195_, v___y_192_, v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(lean_object* v_msg_204_, lean_object* v___y_205_, uint8_t v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___f_209_; lean_object* v___f_210_; lean_object* v___f_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_23834__overap_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
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
v___x_23834__overap_233_ = lean_panic_fn_borrowed(v___x_232_, v_msg_204_);
lean_dec(v___x_232_);
v___x_234_ = lean_box(v___y_206_);
lean_inc_ref(v___y_207_);
v___x_235_ = lean_apply_4(v___x_23834__overap_233_, v___y_205_, v___x_234_, v___y_207_, v___y_208_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___boxed(lean_object* v_msg_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
uint8_t v___y_24500__boxed_241_; lean_object* v_res_242_; 
v___y_24500__boxed_241_ = lean_unbox(v___y_238_);
v_res_242_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v_msg_236_, v___y_237_, v___y_24500__boxed_241_, v___y_239_, v___y_240_);
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
v___x_273_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_243_, v___y_246_, v___y_247_, v___y_248_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_275_; 
v_a_274_ = lean_ctor_get(v___x_273_, 1);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_273_, 2);
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
uint8_t v___y_24571__boxed_301_; lean_object* v_res_302_; 
v___y_24571__boxed_301_ = lean_unbox(v___y_298_);
v_res_302_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_f_295_, v_a_296_, v___y_297_, v___y_24571__boxed_301_, v___y_299_, v___y_300_);
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
lean_object* v_key_306_; lean_object* v_value_307_; lean_object* v_tail_308_; lean_object* v_fst_309_; lean_object* v_snd_310_; lean_object* v_fst_311_; lean_object* v_snd_312_; size_t v___x_313_; size_t v___x_314_; uint8_t v___x_315_; 
v_key_306_ = lean_ctor_get(v_x_304_, 0);
v_value_307_ = lean_ctor_get(v_x_304_, 1);
v_tail_308_ = lean_ctor_get(v_x_304_, 2);
v_fst_309_ = lean_ctor_get(v_key_306_, 0);
v_snd_310_ = lean_ctor_get(v_key_306_, 1);
v_fst_311_ = lean_ctor_get(v_a_303_, 0);
v_snd_312_ = lean_ctor_get(v_a_303_, 1);
v___x_313_ = lean_ptr_addr(v_fst_309_);
v___x_314_ = lean_ptr_addr(v_fst_311_);
v___x_315_ = lean_usize_dec_eq(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
v_x_304_ = v_tail_308_;
goto _start;
}
else
{
uint8_t v___x_317_; 
v___x_317_ = lean_nat_dec_eq(v_snd_310_, v_snd_312_);
if (v___x_317_ == 0)
{
v_x_304_ = v_tail_308_;
goto _start;
}
else
{
lean_object* v___x_319_; 
lean_inc(v_value_307_);
v___x_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_319_, 0, v_value_307_);
return v___x_319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg___boxed(lean_object* v_a_320_, lean_object* v_x_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_320_, v_x_321_);
lean_dec(v_x_321_);
lean_dec_ref(v_a_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(lean_object* v_m_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_buckets_325_; lean_object* v_fst_326_; lean_object* v_snd_327_; lean_object* v___x_328_; size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; uint64_t v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v_fold_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; size_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_buckets_325_ = lean_ctor_get(v_m_323_, 1);
v_fst_326_ = lean_ctor_get(v_a_324_, 0);
v_snd_327_ = lean_ctor_get(v_a_324_, 1);
v___x_328_ = lean_array_get_size(v_buckets_325_);
v___x_329_ = lean_ptr_addr(v_fst_326_);
v___x_330_ = ((size_t)3ULL);
v___x_331_ = lean_usize_shift_right(v___x_329_, v___x_330_);
v___x_332_ = lean_usize_to_uint64(v___x_331_);
v___x_333_ = lean_uint64_of_nat(v_snd_327_);
v___x_334_ = lean_uint64_mix_hash(v___x_332_, v___x_333_);
v___x_335_ = 32ULL;
v___x_336_ = lean_uint64_shift_right(v___x_334_, v___x_335_);
v_fold_337_ = lean_uint64_xor(v___x_334_, v___x_336_);
v___x_338_ = 16ULL;
v___x_339_ = lean_uint64_shift_right(v_fold_337_, v___x_338_);
v___x_340_ = lean_uint64_xor(v_fold_337_, v___x_339_);
v___x_341_ = lean_uint64_to_usize(v___x_340_);
v___x_342_ = lean_usize_of_nat(v___x_328_);
v___x_343_ = ((size_t)1ULL);
v___x_344_ = lean_usize_sub(v___x_342_, v___x_343_);
v___x_345_ = lean_usize_land(v___x_341_, v___x_344_);
v___x_346_ = lean_array_uget_borrowed(v_buckets_325_, v___x_345_);
v___x_347_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_324_, v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_m_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_348_, v_a_349_);
lean_dec_ref(v_a_349_);
lean_dec_ref(v_m_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(lean_object* v_x_351_, lean_object* v_t_352_, lean_object* v_v_353_, lean_object* v_b_354_, uint8_t v_nondep_355_, lean_object* v___y_356_, uint8_t v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___y_361_; lean_object* v___y_362_; 
if (v___y_357_ == 0)
{
v___y_361_ = v___y_356_;
v___y_362_ = v___y_359_;
goto v___jp_360_;
}
else
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_352_, v___y_357_, v___y_358_, v___y_359_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; 
v_a_385_ = lean_ctor_get(v___x_384_, 1);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 2);
v___x_386_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_353_, v___y_357_, v___y_358_, v_a_385_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_388_; 
v_a_387_ = lean_ctor_get(v___x_386_, 1);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_386_, 2);
v___x_388_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_354_, v___y_357_, v___y_358_, v_a_387_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; 
v_a_389_ = lean_ctor_get(v___x_388_, 1);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_388_, 2);
v___y_361_ = v___y_356_;
v___y_362_ = v_a_389_;
goto v___jp_360_;
}
else
{
lean_object* v_a_390_; lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec_ref(v___y_356_);
lean_dec_ref(v_b_354_);
lean_dec_ref(v_v_353_);
lean_dec_ref(v_t_352_);
lean_dec(v_x_351_);
v_a_390_ = lean_ctor_get(v___x_388_, 0);
v_a_391_ = lean_ctor_get(v___x_388_, 1);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_388_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_inc(v_a_390_);
lean_dec(v___x_388_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_390_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec_ref(v___y_356_);
lean_dec_ref(v_b_354_);
lean_dec_ref(v_v_353_);
lean_dec_ref(v_t_352_);
lean_dec(v_x_351_);
v_a_399_ = lean_ctor_get(v___x_386_, 0);
v_a_400_ = lean_ctor_get(v___x_386_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_386_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_inc(v_a_399_);
lean_dec(v___x_386_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_399_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
else
{
lean_object* v_a_408_; lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_dec_ref(v___y_356_);
lean_dec_ref(v_b_354_);
lean_dec_ref(v_v_353_);
lean_dec_ref(v_t_352_);
lean_dec(v_x_351_);
v_a_408_ = lean_ctor_get(v___x_384_, 0);
v_a_409_ = lean_ctor_get(v___x_384_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_384_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_inc(v_a_408_);
lean_dec(v___x_384_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_408_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
v___jp_360_:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = l_Lean_Expr_letE___override(v_x_351_, v_t_352_, v_v_353_, v_b_354_, v_nondep_355_);
v___x_364_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_363_, v___y_362_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_374_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_a_366_ = lean_ctor_get(v___x_364_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_374_ == 0)
{
v___x_368_ = v___x_364_;
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v_a_365_);
lean_ctor_set(v___x_370_, 1, v___y_361_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_370_);
v___x_372_ = v___x_368_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_a_366_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
else
{
lean_object* v_a_375_; lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec_ref(v___y_361_);
v_a_375_ = lean_ctor_get(v___x_364_, 0);
v_a_376_ = lean_ctor_get(v___x_364_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_364_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_inc(v_a_375_);
lean_dec(v___x_364_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_375_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5___boxed(lean_object* v_x_417_, lean_object* v_t_418_, lean_object* v_v_419_, lean_object* v_b_420_, lean_object* v_nondep_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
uint8_t v_nondep_boxed_426_; uint8_t v___y_24754__boxed_427_; lean_object* v_res_428_; 
v_nondep_boxed_426_ = lean_unbox(v_nondep_421_);
v___y_24754__boxed_427_ = lean_unbox(v___y_423_);
v_res_428_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_x_417_, v_t_418_, v_v_419_, v_b_420_, v_nondep_boxed_426_, v___y_422_, v___y_24754__boxed_427_, v___y_424_, v___y_425_);
lean_dec_ref(v___y_424_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(lean_object* v_d_429_, lean_object* v_e_430_, lean_object* v___y_431_, uint8_t v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___y_436_; lean_object* v___y_437_; 
if (v___y_432_ == 0)
{
v___y_436_ = v___y_431_;
v___y_437_ = v___y_434_;
goto v___jp_435_;
}
else
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_430_, v___y_432_, v___y_433_, v___y_434_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; 
v_a_460_ = lean_ctor_get(v___x_459_, 1);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_459_, 2);
v___y_436_ = v___y_431_;
v___y_437_ = v_a_460_;
goto v___jp_435_;
}
else
{
lean_object* v_a_461_; lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec_ref(v___y_431_);
lean_dec_ref(v_e_430_);
lean_dec(v_d_429_);
v_a_461_ = lean_ctor_get(v___x_459_, 0);
v_a_462_ = lean_ctor_get(v___x_459_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_459_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_inc(v_a_461_);
lean_dec(v___x_459_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_461_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
v___jp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = l_Lean_Expr_mdata___override(v_d_429_, v_e_430_);
v___x_439_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_438_, v___y_437_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_449_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_a_441_ = lean_ctor_get(v___x_439_, 1);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_449_ == 0)
{
v___x_443_ = v___x_439_;
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v_a_440_);
lean_ctor_set(v___x_445_, 1, v___y_436_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_445_);
v___x_447_ = v___x_443_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_a_441_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
else
{
lean_object* v_a_450_; lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref(v___y_436_);
v_a_450_ = lean_ctor_get(v___x_439_, 0);
v_a_451_ = lean_ctor_get(v___x_439_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_439_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_inc(v_a_450_);
lean_dec(v___x_439_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_450_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6___boxed(lean_object* v_d_470_, lean_object* v_e_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
uint8_t v___y_24883__boxed_476_; lean_object* v_res_477_; 
v___y_24883__boxed_476_ = lean_unbox(v___y_473_);
v_res_477_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_d_470_, v_e_471_, v___y_472_, v___y_24883__boxed_476_, v___y_474_, v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_477_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_481_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2));
v___x_482_ = lean_unsigned_to_nat(67u);
v___x_483_ = lean_unsigned_to_nat(35u);
v___x_484_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1));
v___x_485_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0));
v___x_486_ = l_mkPanicMessageWithDecl(v___x_485_, v___x_484_, v___x_483_, v___x_482_, v___x_481_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(lean_object* v_s_487_, lean_object* v_d_488_, lean_object* v_e_489_, lean_object* v_offset_490_, lean_object* v_a_491_, uint8_t v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
switch(lean_obj_tag(v_e_489_))
{
case 5:
{
lean_object* v_fn_495_; lean_object* v_arg_496_; lean_object* v___x_497_; 
v_fn_495_ = lean_ctor_get(v_e_489_, 0);
v_arg_496_ = lean_ctor_get(v_e_489_, 1);
lean_inc(v_offset_490_);
lean_inc_ref(v_fn_495_);
v___x_497_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_487_, v_d_488_, v_fn_495_, v_offset_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v_a_499_; lean_object* v_fst_500_; lean_object* v_snd_501_; lean_object* v___x_502_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
v_a_499_ = lean_ctor_get(v___x_497_, 1);
lean_inc(v_a_499_);
lean_dec_ref_known(v___x_497_, 2);
v_fst_500_ = lean_ctor_get(v_a_498_, 0);
lean_inc(v_fst_500_);
v_snd_501_ = lean_ctor_get(v_a_498_, 1);
lean_inc(v_snd_501_);
lean_dec(v_a_498_);
lean_inc_ref(v_arg_496_);
v___x_502_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_487_, v_d_488_, v_arg_496_, v_offset_490_, v_snd_501_, v_a_492_, v_a_493_, v_a_499_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_528_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_a_504_ = lean_ctor_get(v___x_502_, 1);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_528_ == 0)
{
v___x_506_ = v___x_502_;
v_isShared_507_ = v_isSharedCheck_528_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_528_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v_fst_508_; lean_object* v_snd_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_527_; 
v_fst_508_ = lean_ctor_get(v_a_503_, 0);
v_snd_509_ = lean_ctor_get(v_a_503_, 1);
v_isSharedCheck_527_ = !lean_is_exclusive(v_a_503_);
if (v_isSharedCheck_527_ == 0)
{
v___x_511_ = v_a_503_;
v_isShared_512_ = v_isSharedCheck_527_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_snd_509_);
lean_inc(v_fst_508_);
lean_dec(v_a_503_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_527_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
size_t v___x_513_; size_t v___x_514_; uint8_t v___x_515_; 
v___x_513_ = lean_ptr_addr(v_fn_495_);
v___x_514_ = lean_ptr_addr(v_fst_500_);
v___x_515_ = lean_usize_dec_eq(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
lean_del_object(v___x_511_);
lean_del_object(v___x_506_);
lean_dec_ref_known(v_e_489_, 2);
v___x_516_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_500_, v_fst_508_, v_snd_509_, v_a_492_, v_a_493_, v_a_504_);
return v___x_516_;
}
else
{
size_t v___x_517_; size_t v___x_518_; uint8_t v___x_519_; 
v___x_517_ = lean_ptr_addr(v_arg_496_);
v___x_518_ = lean_ptr_addr(v_fst_508_);
v___x_519_ = lean_usize_dec_eq(v___x_517_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
lean_del_object(v___x_511_);
lean_del_object(v___x_506_);
lean_dec_ref_known(v_e_489_, 2);
v___x_520_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_500_, v_fst_508_, v_snd_509_, v_a_492_, v_a_493_, v_a_504_);
return v___x_520_;
}
else
{
lean_object* v___x_522_; 
lean_dec(v_fst_508_);
lean_dec(v_fst_500_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v_e_489_);
v___x_522_ = v___x_511_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_e_489_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_snd_509_);
v___x_522_ = v_reuseFailAlloc_526_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_524_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_522_);
v___x_524_ = v___x_506_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_a_504_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_500_);
lean_dec_ref_known(v_e_489_, 2);
return v___x_502_;
}
}
else
{
lean_dec_ref_known(v_e_489_, 2);
lean_dec(v_offset_490_);
return v___x_497_;
}
}
case 6:
{
lean_object* v_binderName_529_; lean_object* v_binderType_530_; lean_object* v_body_531_; uint8_t v_binderInfo_532_; lean_object* v___x_533_; 
v_binderName_529_ = lean_ctor_get(v_e_489_, 0);
v_binderType_530_ = lean_ctor_get(v_e_489_, 1);
v_body_531_ = lean_ctor_get(v_e_489_, 2);
v_binderInfo_532_ = lean_ctor_get_uint8(v_e_489_, sizeof(void*)*3 + 8);
lean_inc(v_offset_490_);
lean_inc_ref(v_binderType_530_);
v___x_533_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_487_, v_d_488_, v_binderType_530_, v_offset_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v_a_535_; lean_object* v_fst_536_; lean_object* v_snd_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
v_a_535_ = lean_ctor_get(v___x_533_, 1);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_533_, 2);
v_fst_536_ = lean_ctor_get(v_a_534_, 0);
lean_inc(v_fst_536_);
v_snd_537_ = lean_ctor_get(v_a_534_, 1);
lean_inc(v_snd_537_);
lean_dec(v_a_534_);
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_nat_add(v_offset_490_, v___x_538_);
lean_dec(v_offset_490_);
lean_inc_ref(v_body_531_);
v___x_540_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_487_, v_d_488_, v_body_531_, v___x_539_, v_snd_537_, v_a_492_, v_a_493_, v_a_535_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_566_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_a_542_ = lean_ctor_get(v___x_540_, 1);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_566_ == 0)
{
v___x_544_ = v___x_540_;
v_isShared_545_ = v_isSharedCheck_566_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_566_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v_fst_546_; lean_object* v_snd_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_565_; 
v_fst_546_ = lean_ctor_get(v_a_541_, 0);
v_snd_547_ = lean_ctor_get(v_a_541_, 1);
v_isSharedCheck_565_ = !lean_is_exclusive(v_a_541_);
if (v_isSharedCheck_565_ == 0)
{
v___x_549_ = v_a_541_;
v_isShared_550_ = v_isSharedCheck_565_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_snd_547_);
lean_inc(v_fst_546_);
lean_dec(v_a_541_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_565_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
size_t v___x_551_; size_t v___x_552_; uint8_t v___x_553_; 
v___x_551_ = lean_ptr_addr(v_binderType_530_);
v___x_552_ = lean_ptr_addr(v_fst_536_);
v___x_553_ = lean_usize_dec_eq(v___x_551_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
lean_inc(v_binderName_529_);
lean_del_object(v___x_549_);
lean_del_object(v___x_544_);
lean_dec_ref_known(v_e_489_, 3);
v___x_554_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_529_, v_binderInfo_532_, v_fst_536_, v_fst_546_, v_snd_547_, v_a_492_, v_a_493_, v_a_542_);
return v___x_554_;
}
else
{
size_t v___x_555_; size_t v___x_556_; uint8_t v___x_557_; 
v___x_555_ = lean_ptr_addr(v_body_531_);
v___x_556_ = lean_ptr_addr(v_fst_546_);
v___x_557_ = lean_usize_dec_eq(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
lean_inc(v_binderName_529_);
lean_del_object(v___x_549_);
lean_del_object(v___x_544_);
lean_dec_ref_known(v_e_489_, 3);
v___x_558_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_529_, v_binderInfo_532_, v_fst_536_, v_fst_546_, v_snd_547_, v_a_492_, v_a_493_, v_a_542_);
return v___x_558_;
}
else
{
lean_object* v___x_560_; 
lean_dec(v_fst_546_);
lean_dec(v_fst_536_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v_e_489_);
v___x_560_ = v___x_549_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_e_489_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_snd_547_);
v___x_560_ = v_reuseFailAlloc_564_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_562_; 
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_560_);
v___x_562_ = v___x_544_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_a_542_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_536_);
lean_dec_ref_known(v_e_489_, 3);
return v___x_540_;
}
}
else
{
lean_dec_ref_known(v_e_489_, 3);
lean_dec(v_offset_490_);
return v___x_533_;
}
}
case 7:
{
lean_object* v_binderName_567_; lean_object* v_binderType_568_; lean_object* v_body_569_; uint8_t v_binderInfo_570_; lean_object* v___x_571_; 
v_binderName_567_ = lean_ctor_get(v_e_489_, 0);
v_binderType_568_ = lean_ctor_get(v_e_489_, 1);
v_body_569_ = lean_ctor_get(v_e_489_, 2);
v_binderInfo_570_ = lean_ctor_get_uint8(v_e_489_, sizeof(void*)*3 + 8);
lean_inc(v_offset_490_);
lean_inc_ref(v_binderType_568_);
v___x_571_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_487_, v_d_488_, v_binderType_568_, v_offset_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v_a_573_; lean_object* v_fst_574_; lean_object* v_snd_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
v_a_573_ = lean_ctor_get(v___x_571_, 1);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_571_, 2);
v_fst_574_ = lean_ctor_get(v_a_572_, 0);
lean_inc(v_fst_574_);
v_snd_575_ = lean_ctor_get(v_a_572_, 1);
lean_inc(v_snd_575_);
lean_dec(v_a_572_);
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_add(v_offset_490_, v___x_576_);
lean_dec(v_offset_490_);
lean_inc_ref(v_body_569_);
v___x_578_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_487_, v_d_488_, v_body_569_, v___x_577_, v_snd_575_, v_a_492_, v_a_493_, v_a_573_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_604_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_a_580_ = lean_ctor_get(v___x_578_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_604_ == 0)
{
v___x_582_ = v___x_578_;
v_isShared_583_ = v_isSharedCheck_604_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_604_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_fst_584_; lean_object* v_snd_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_603_; 
v_fst_584_ = lean_ctor_get(v_a_579_, 0);
v_snd_585_ = lean_ctor_get(v_a_579_, 1);
v_isSharedCheck_603_ = !lean_is_exclusive(v_a_579_);
if (v_isSharedCheck_603_ == 0)
{
v___x_587_ = v_a_579_;
v_isShared_588_ = v_isSharedCheck_603_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_snd_585_);
lean_inc(v_fst_584_);
lean_dec(v_a_579_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_603_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
size_t v___x_589_; size_t v___x_590_; uint8_t v___x_591_; 
v___x_589_ = lean_ptr_addr(v_binderType_568_);
v___x_590_ = lean_ptr_addr(v_fst_574_);
v___x_591_ = lean_usize_dec_eq(v___x_589_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
lean_inc(v_binderName_567_);
lean_del_object(v___x_587_);
lean_del_object(v___x_582_);
lean_dec_ref_known(v_e_489_, 3);
v___x_592_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_567_, v_binderInfo_570_, v_fst_574_, v_fst_584_, v_snd_585_, v_a_492_, v_a_493_, v_a_580_);
return v___x_592_;
}
else
{
size_t v___x_593_; size_t v___x_594_; uint8_t v___x_595_; 
v___x_593_ = lean_ptr_addr(v_body_569_);
v___x_594_ = lean_ptr_addr(v_fst_584_);
v___x_595_ = lean_usize_dec_eq(v___x_593_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
lean_inc(v_binderName_567_);
lean_del_object(v___x_587_);
lean_del_object(v___x_582_);
lean_dec_ref_known(v_e_489_, 3);
v___x_596_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_567_, v_binderInfo_570_, v_fst_574_, v_fst_584_, v_snd_585_, v_a_492_, v_a_493_, v_a_580_);
return v___x_596_;
}
else
{
lean_object* v___x_598_; 
lean_dec(v_fst_584_);
lean_dec(v_fst_574_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v_e_489_);
v___x_598_ = v___x_587_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_e_489_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_snd_585_);
v___x_598_ = v_reuseFailAlloc_602_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_600_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_598_);
v___x_600_ = v___x_582_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_a_580_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_574_);
lean_dec_ref_known(v_e_489_, 3);
return v___x_578_;
}
}
else
{
lean_dec_ref_known(v_e_489_, 3);
lean_dec(v_offset_490_);
return v___x_571_;
}
}
case 8:
{
lean_object* v_declName_605_; lean_object* v_type_606_; lean_object* v_value_607_; lean_object* v_body_608_; uint8_t v_nondep_609_; lean_object* v___x_610_; 
v_declName_605_ = lean_ctor_get(v_e_489_, 0);
v_type_606_ = lean_ctor_get(v_e_489_, 1);
v_value_607_ = lean_ctor_get(v_e_489_, 2);
v_body_608_ = lean_ctor_get(v_e_489_, 3);
v_nondep_609_ = lean_ctor_get_uint8(v_e_489_, sizeof(void*)*4 + 8);
lean_inc(v_offset_490_);
lean_inc_ref(v_type_606_);
v___x_610_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_487_, v_d_488_, v_type_606_, v_offset_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v_a_612_; lean_object* v_fst_613_; lean_object* v_snd_614_; lean_object* v___x_615_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
v_a_612_ = lean_ctor_get(v___x_610_, 1);
lean_inc(v_a_612_);
lean_dec_ref_known(v___x_610_, 2);
v_fst_613_ = lean_ctor_get(v_a_611_, 0);
lean_inc(v_fst_613_);
v_snd_614_ = lean_ctor_get(v_a_611_, 1);
lean_inc(v_snd_614_);
lean_dec(v_a_611_);
lean_inc(v_offset_490_);
lean_inc_ref(v_value_607_);
v___x_615_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_487_, v_d_488_, v_value_607_, v_offset_490_, v_snd_614_, v_a_492_, v_a_493_, v_a_612_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v_a_617_; lean_object* v_fst_618_; lean_object* v_snd_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
v_a_617_ = lean_ctor_get(v___x_615_, 1);
lean_inc(v_a_617_);
lean_dec_ref_known(v___x_615_, 2);
v_fst_618_ = lean_ctor_get(v_a_616_, 0);
lean_inc(v_fst_618_);
v_snd_619_ = lean_ctor_get(v_a_616_, 1);
lean_inc(v_snd_619_);
lean_dec(v_a_616_);
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_nat_add(v_offset_490_, v___x_620_);
lean_dec(v_offset_490_);
lean_inc_ref(v_body_608_);
v___x_622_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_487_, v_d_488_, v_body_608_, v___x_621_, v_snd_619_, v_a_492_, v_a_493_, v_a_617_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_652_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_a_624_ = lean_ctor_get(v___x_622_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_652_ == 0)
{
v___x_626_ = v___x_622_;
v_isShared_627_ = v_isSharedCheck_652_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_652_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v_fst_628_; lean_object* v_snd_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_651_; 
v_fst_628_ = lean_ctor_get(v_a_623_, 0);
v_snd_629_ = lean_ctor_get(v_a_623_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_a_623_);
if (v_isSharedCheck_651_ == 0)
{
v___x_631_ = v_a_623_;
v_isShared_632_ = v_isSharedCheck_651_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_snd_629_);
lean_inc(v_fst_628_);
lean_dec(v_a_623_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_651_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
size_t v___x_633_; size_t v___x_634_; uint8_t v___x_635_; 
v___x_633_ = lean_ptr_addr(v_type_606_);
v___x_634_ = lean_ptr_addr(v_fst_613_);
v___x_635_ = lean_usize_dec_eq(v___x_633_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
lean_inc(v_declName_605_);
lean_del_object(v___x_631_);
lean_del_object(v___x_626_);
lean_dec_ref_known(v_e_489_, 4);
v___x_636_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_605_, v_fst_613_, v_fst_618_, v_fst_628_, v_nondep_609_, v_snd_629_, v_a_492_, v_a_493_, v_a_624_);
return v___x_636_;
}
else
{
size_t v___x_637_; size_t v___x_638_; uint8_t v___x_639_; 
v___x_637_ = lean_ptr_addr(v_value_607_);
v___x_638_ = lean_ptr_addr(v_fst_618_);
v___x_639_ = lean_usize_dec_eq(v___x_637_, v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
lean_inc(v_declName_605_);
lean_del_object(v___x_631_);
lean_del_object(v___x_626_);
lean_dec_ref_known(v_e_489_, 4);
v___x_640_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_605_, v_fst_613_, v_fst_618_, v_fst_628_, v_nondep_609_, v_snd_629_, v_a_492_, v_a_493_, v_a_624_);
return v___x_640_;
}
else
{
size_t v___x_641_; size_t v___x_642_; uint8_t v___x_643_; 
v___x_641_ = lean_ptr_addr(v_body_608_);
v___x_642_ = lean_ptr_addr(v_fst_628_);
v___x_643_ = lean_usize_dec_eq(v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
lean_inc(v_declName_605_);
lean_del_object(v___x_631_);
lean_del_object(v___x_626_);
lean_dec_ref_known(v_e_489_, 4);
v___x_644_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_605_, v_fst_613_, v_fst_618_, v_fst_628_, v_nondep_609_, v_snd_629_, v_a_492_, v_a_493_, v_a_624_);
return v___x_644_;
}
else
{
lean_object* v___x_646_; 
lean_dec(v_fst_628_);
lean_dec(v_fst_618_);
lean_dec(v_fst_613_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v_e_489_);
v___x_646_ = v___x_631_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_e_489_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_snd_629_);
v___x_646_ = v_reuseFailAlloc_650_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_648_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_646_);
v___x_648_ = v___x_626_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_a_624_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
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
lean_dec(v_fst_618_);
lean_dec(v_fst_613_);
lean_dec_ref_known(v_e_489_, 4);
return v___x_622_;
}
}
else
{
lean_dec(v_fst_613_);
lean_dec_ref_known(v_e_489_, 4);
lean_dec(v_offset_490_);
return v___x_615_;
}
}
else
{
lean_dec_ref_known(v_e_489_, 4);
lean_dec(v_offset_490_);
return v___x_610_;
}
}
case 10:
{
lean_object* v_data_653_; lean_object* v_expr_654_; lean_object* v___x_655_; 
v_data_653_ = lean_ctor_get(v_e_489_, 0);
v_expr_654_ = lean_ctor_get(v_e_489_, 1);
lean_inc_ref(v_expr_654_);
v___x_655_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_487_, v_d_488_, v_expr_654_, v_offset_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_677_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_a_657_ = lean_ctor_get(v___x_655_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_677_ == 0)
{
v___x_659_ = v___x_655_;
v_isShared_660_ = v_isSharedCheck_677_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_677_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_fst_661_; lean_object* v_snd_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_676_; 
v_fst_661_ = lean_ctor_get(v_a_656_, 0);
v_snd_662_ = lean_ctor_get(v_a_656_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_a_656_);
if (v_isSharedCheck_676_ == 0)
{
v___x_664_ = v_a_656_;
v_isShared_665_ = v_isSharedCheck_676_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_snd_662_);
lean_inc(v_fst_661_);
lean_dec(v_a_656_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_676_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
size_t v___x_666_; size_t v___x_667_; uint8_t v___x_668_; 
v___x_666_ = lean_ptr_addr(v_expr_654_);
v___x_667_ = lean_ptr_addr(v_fst_661_);
v___x_668_ = lean_usize_dec_eq(v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
lean_inc(v_data_653_);
lean_del_object(v___x_664_);
lean_del_object(v___x_659_);
lean_dec_ref_known(v_e_489_, 2);
v___x_669_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_653_, v_fst_661_, v_snd_662_, v_a_492_, v_a_493_, v_a_657_);
return v___x_669_;
}
else
{
lean_object* v___x_671_; 
lean_dec(v_fst_661_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v_e_489_);
v___x_671_ = v___x_664_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_e_489_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_snd_662_);
v___x_671_ = v_reuseFailAlloc_675_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_673_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_671_);
v___x_673_ = v___x_659_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_a_657_);
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
else
{
lean_dec_ref_known(v_e_489_, 2);
return v___x_655_;
}
}
case 11:
{
lean_object* v_typeName_678_; lean_object* v_idx_679_; lean_object* v_struct_680_; lean_object* v___x_681_; 
v_typeName_678_ = lean_ctor_get(v_e_489_, 0);
v_idx_679_ = lean_ctor_get(v_e_489_, 1);
v_struct_680_ = lean_ctor_get(v_e_489_, 2);
lean_inc_ref(v_struct_680_);
v___x_681_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_487_, v_d_488_, v_struct_680_, v_offset_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_703_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
v_a_683_ = lean_ctor_get(v___x_681_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_703_ == 0)
{
v___x_685_ = v___x_681_;
v_isShared_686_ = v_isSharedCheck_703_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_inc(v_a_682_);
lean_dec(v___x_681_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_703_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v_fst_687_; lean_object* v_snd_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_702_; 
v_fst_687_ = lean_ctor_get(v_a_682_, 0);
v_snd_688_ = lean_ctor_get(v_a_682_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_a_682_);
if (v_isSharedCheck_702_ == 0)
{
v___x_690_ = v_a_682_;
v_isShared_691_ = v_isSharedCheck_702_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_snd_688_);
lean_inc(v_fst_687_);
lean_dec(v_a_682_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_702_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
size_t v___x_692_; size_t v___x_693_; uint8_t v___x_694_; 
v___x_692_ = lean_ptr_addr(v_struct_680_);
v___x_693_ = lean_ptr_addr(v_fst_687_);
v___x_694_ = lean_usize_dec_eq(v___x_692_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
lean_inc(v_idx_679_);
lean_inc(v_typeName_678_);
lean_del_object(v___x_690_);
lean_del_object(v___x_685_);
lean_dec_ref_known(v_e_489_, 3);
v___x_695_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_678_, v_idx_679_, v_fst_687_, v_snd_688_, v_a_492_, v_a_493_, v_a_683_);
return v___x_695_;
}
else
{
lean_object* v___x_697_; 
lean_dec(v_fst_687_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v_e_489_);
v___x_697_ = v___x_690_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_e_489_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_snd_688_);
v___x_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_697_);
v___x_699_ = v___x_685_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_a_683_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_489_, 3);
return v___x_681_;
}
}
default: 
{
lean_object* v___x_704_; lean_object* v___x_705_; 
lean_dec(v_offset_490_);
lean_dec_ref(v_e_489_);
v___x_704_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
v___x_705_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_704_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
return v___x_705_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(lean_object* v_s_706_, lean_object* v_d_707_, lean_object* v_e_708_, lean_object* v_offset_709_, lean_object* v_a_710_, uint8_t v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_key_714_; lean_object* v_a_716_; lean_object* v___x_729_; 
lean_inc(v_offset_709_);
lean_inc_ref(v_e_708_);
v_key_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_714_, 0, v_e_708_);
lean_ctor_set(v_key_714_, 1, v_offset_709_);
v___x_729_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_710_, v_key_714_);
if (lean_obj_tag(v___x_729_) == 1)
{
lean_object* v_val_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec_ref_known(v_key_714_, 2);
lean_dec(v_offset_709_);
lean_dec_ref(v_e_708_);
v_val_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v___x_729_, 1);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v_val_730_);
lean_ctor_set(v___x_731_, 1, v_a_710_);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v_a_713_);
return v___x_732_;
}
else
{
lean_object* v_s_u2081_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
lean_dec(v___x_729_);
v_s_u2081_733_ = lean_nat_add(v_s_706_, v_offset_709_);
v___x_734_ = l_Lean_Expr_looseBVarRange(v_e_708_);
v___x_735_ = lean_nat_dec_le(v___x_734_, v_s_u2081_733_);
lean_dec(v___x_734_);
if (v___x_735_ == 0)
{
if (lean_obj_tag(v_e_708_) == 0)
{
lean_object* v_deBruijnIndex_736_; uint8_t v___x_737_; 
v_deBruijnIndex_736_ = lean_ctor_get(v_e_708_, 0);
v___x_737_ = lean_nat_dec_le(v_s_u2081_733_, v_deBruijnIndex_736_);
lean_dec(v_s_u2081_733_);
if (v___x_737_ == 0)
{
v_a_716_ = v_a_713_;
goto v___jp_715_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_inc(v_deBruijnIndex_736_);
lean_dec_ref_known(v_e_708_, 1);
lean_dec(v_offset_709_);
v___x_738_ = lean_nat_sub(v_deBruijnIndex_736_, v_d_707_);
lean_dec(v_deBruijnIndex_736_);
v___x_739_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_738_, v_a_713_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v_a_741_; lean_object* v___x_742_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
v_a_741_ = lean_ctor_get(v___x_739_, 1);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_739_, 2);
v___x_742_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_714_, v_a_740_, v_a_710_, v_a_711_, v_a_712_, v_a_741_);
return v___x_742_;
}
else
{
lean_object* v_a_743_; lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec_ref_known(v_key_714_, 2);
lean_dec_ref(v_a_710_);
v_a_743_ = lean_ctor_get(v___x_739_, 0);
v_a_744_ = lean_ctor_get(v___x_739_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_739_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_inc(v_a_743_);
lean_dec(v___x_739_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_743_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
else
{
lean_dec(v_s_u2081_733_);
v_a_716_ = v_a_713_;
goto v___jp_715_;
}
}
else
{
lean_object* v___x_752_; 
lean_dec(v_s_u2081_733_);
lean_dec(v_offset_709_);
v___x_752_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_714_, v_e_708_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
return v___x_752_;
}
}
v___jp_715_:
{
switch(lean_obj_tag(v_e_708_))
{
case 9:
{
lean_object* v___x_717_; 
lean_dec(v_offset_709_);
v___x_717_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_714_, v_e_708_, v_a_710_, v_a_711_, v_a_712_, v_a_716_);
return v___x_717_;
}
case 2:
{
lean_object* v___x_718_; 
lean_dec(v_offset_709_);
v___x_718_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_714_, v_e_708_, v_a_710_, v_a_711_, v_a_712_, v_a_716_);
return v___x_718_;
}
case 0:
{
lean_object* v___x_719_; 
lean_dec(v_offset_709_);
v___x_719_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_714_, v_e_708_, v_a_710_, v_a_711_, v_a_712_, v_a_716_);
return v___x_719_;
}
case 1:
{
lean_object* v___x_720_; 
lean_dec(v_offset_709_);
v___x_720_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_714_, v_e_708_, v_a_710_, v_a_711_, v_a_712_, v_a_716_);
return v___x_720_;
}
case 4:
{
lean_object* v___x_721_; 
lean_dec(v_offset_709_);
v___x_721_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_714_, v_e_708_, v_a_710_, v_a_711_, v_a_712_, v_a_716_);
return v___x_721_;
}
case 3:
{
lean_object* v___x_722_; 
lean_dec(v_offset_709_);
v___x_722_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_714_, v_e_708_, v_a_710_, v_a_711_, v_a_712_, v_a_716_);
return v___x_722_;
}
default: 
{
lean_object* v___x_723_; 
v___x_723_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_706_, v_d_707_, v_e_708_, v_offset_709_, v_a_710_, v_a_711_, v_a_712_, v_a_716_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v_a_725_; lean_object* v_fst_726_; lean_object* v_snd_727_; lean_object* v___x_728_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
v_a_725_ = lean_ctor_get(v___x_723_, 1);
lean_inc(v_a_725_);
lean_dec_ref_known(v___x_723_, 2);
v_fst_726_ = lean_ctor_get(v_a_724_, 0);
lean_inc(v_fst_726_);
v_snd_727_ = lean_ctor_get(v_a_724_, 1);
lean_inc(v_snd_727_);
lean_dec(v_a_724_);
v___x_728_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_714_, v_fst_726_, v_snd_727_, v_a_711_, v_a_712_, v_a_725_);
return v___x_728_;
}
else
{
lean_dec_ref_known(v_key_714_, 2);
return v___x_723_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1___boxed(lean_object* v_s_753_, lean_object* v_d_754_, lean_object* v_e_755_, lean_object* v_offset_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
uint8_t v_a_boxed_761_; lean_object* v_res_762_; 
v_a_boxed_761_ = lean_unbox(v_a_758_);
v_res_762_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_753_, v_d_754_, v_e_755_, v_offset_756_, v_a_757_, v_a_boxed_761_, v_a_759_, v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_d_754_);
lean_dec(v_s_753_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___boxed(lean_object* v_s_763_, lean_object* v_d_764_, lean_object* v_e_765_, lean_object* v_offset_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
uint8_t v_a_boxed_771_; lean_object* v_res_772_; 
v_a_boxed_771_ = lean_unbox(v_a_768_);
v_res_772_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_763_, v_d_764_, v_e_765_, v_offset_766_, v_a_767_, v_a_boxed_771_, v_a_769_, v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_d_764_);
lean_dec(v_s_763_);
return v_res_772_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = lean_box(0);
v___x_774_ = lean_unsigned_to_nat(16u);
v___x_775_ = lean_mk_array(v___x_774_, v___x_773_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0);
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___x_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27(lean_object* v_e_779_, lean_object* v_s_780_, lean_object* v_d_781_, uint8_t v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_785_ = l_Lean_Expr_looseBVarRange(v_e_779_);
v___x_786_ = lean_nat_dec_le(v___x_785_, v_s_780_);
lean_dec(v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; lean_object* v_a_789_; 
v___x_787_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_e_779_) == 0)
{
lean_object* v_deBruijnIndex_817_; uint8_t v___x_818_; 
v_deBruijnIndex_817_ = lean_ctor_get(v_e_779_, 0);
v___x_818_ = lean_nat_dec_le(v_s_780_, v_deBruijnIndex_817_);
if (v___x_818_ == 0)
{
v_a_789_ = v_a_784_;
goto v___jp_788_;
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; 
lean_inc(v_deBruijnIndex_817_);
lean_dec_ref_known(v_e_779_, 1);
v___x_819_ = lean_nat_sub(v_deBruijnIndex_817_, v_d_781_);
lean_dec(v_deBruijnIndex_817_);
v___x_820_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_819_, v_a_784_);
return v___x_820_;
}
}
else
{
v_a_789_ = v_a_784_;
goto v___jp_788_;
}
v___jp_788_:
{
switch(lean_obj_tag(v_e_779_))
{
case 9:
{
lean_object* v___x_790_; 
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_e_779_);
lean_ctor_set(v___x_790_, 1, v_a_789_);
return v___x_790_;
}
case 2:
{
lean_object* v___x_791_; 
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v_e_779_);
lean_ctor_set(v___x_791_, 1, v_a_789_);
return v___x_791_;
}
case 0:
{
lean_object* v___x_792_; 
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v_e_779_);
lean_ctor_set(v___x_792_, 1, v_a_789_);
return v___x_792_;
}
case 1:
{
lean_object* v___x_793_; 
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v_e_779_);
lean_ctor_set(v___x_793_, 1, v_a_789_);
return v___x_793_;
}
case 4:
{
lean_object* v___x_794_; 
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v_e_779_);
lean_ctor_set(v___x_794_, 1, v_a_789_);
return v___x_794_;
}
case 3:
{
lean_object* v___x_795_; 
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v_e_779_);
lean_ctor_set(v___x_795_, 1, v_a_789_);
return v___x_795_;
}
default: 
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1);
v___x_797_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_780_, v_d_781_, v_e_779_, v___x_787_, v___x_796_, v_a_782_, v_a_783_, v_a_789_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_807_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
v_a_799_ = lean_ctor_get(v___x_797_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_807_ == 0)
{
v___x_801_ = v___x_797_;
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_inc(v_a_798_);
lean_dec(v___x_797_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v_fst_803_; lean_object* v___x_805_; 
v_fst_803_ = lean_ctor_get(v_a_798_, 0);
lean_inc(v_fst_803_);
lean_dec(v_a_798_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v_fst_803_);
v___x_805_ = v___x_801_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_fst_803_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_a_799_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
else
{
lean_object* v_a_808_; lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
v_a_808_ = lean_ctor_get(v___x_797_, 0);
v_a_809_ = lean_ctor_get(v___x_797_, 1);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_797_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_inc(v_a_808_);
lean_dec(v___x_797_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_808_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_821_; 
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_e_779_);
lean_ctor_set(v___x_821_, 1, v_a_784_);
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed(lean_object* v_e_822_, lean_object* v_s_823_, lean_object* v_d_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
uint8_t v_a_boxed_828_; lean_object* v_res_829_; 
v_a_boxed_828_ = lean_unbox(v_a_825_);
v_res_829_ = l_Lean_Meta_Sym_lowerLooseBVarsS_x27(v_e_822_, v_s_823_, v_d_824_, v_a_boxed_828_, v_a_826_, v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_d_824_);
lean_dec(v_s_823_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_830_, lean_object* v_m_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_831_, v_a_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_834_, lean_object* v_m_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(v_00_u03b2_834_, v_m_835_, v_a_836_);
lean_dec_ref(v_a_836_);
lean_dec_ref(v_m_835_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(lean_object* v_00_u03b2_838_, lean_object* v_a_839_, lean_object* v_x_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_839_, v_x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___boxed(lean_object* v_00_u03b2_842_, lean_object* v_a_843_, lean_object* v_x_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(v_00_u03b2_842_, v_a_843_, v_x_844_);
lean_dec(v_x_844_);
lean_dec_ref(v_a_843_);
return v_res_845_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0(void){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(lean_object* v_msg_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___x_855_; lean_object* v___x_44__overap_856_; lean_object* v___x_857_; 
v___x_855_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0);
v___x_44__overap_856_ = lean_panic_fn_borrowed(v___x_855_, v_msg_847_);
lean_inc(v___y_853_);
lean_inc_ref(v___y_852_);
lean_inc(v___y_851_);
lean_inc_ref(v___y_850_);
lean_inc(v___y_849_);
lean_inc_ref(v___y_848_);
v___x_857_ = lean_apply_7(v___x_44__overap_856_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, lean_box(0));
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___boxed(lean_object* v_msg_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(v_msg_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
return v_res_866_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_869_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2));
v___x_870_ = lean_unsigned_to_nat(16u);
v___x_871_ = lean_unsigned_to_nat(62u);
v___x_872_ = ((lean_object*)(l_Lean_Meta_Sym_lowerLooseBVarsS___closed__1));
v___x_873_ = ((lean_object*)(l_Lean_Meta_Sym_lowerLooseBVarsS___closed__0));
v___x_874_ = l_mkPanicMessageWithDecl(v___x_873_, v___x_872_, v___x_871_, v___x_870_, v___x_869_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS(lean_object* v_e_875_, lean_object* v_s_876_, lean_object* v_d_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v_debug_887_; lean_object* v_env_888_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_885_ = lean_st_ref_get(v_a_879_);
v___x_886_ = lean_st_ref_get(v_a_883_);
v_debug_887_ = lean_ctor_get_uint8(v___x_885_, sizeof(void*)*11);
lean_dec(v___x_885_);
v_env_888_ = lean_ctor_get(v___x_886_, 0);
lean_inc_ref(v_env_888_);
lean_dec(v___x_886_);
v___x_889_ = lean_box(v_debug_887_);
v___x_890_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed), 6, 4);
lean_closure_set(v___x_890_, 0, v_e_875_);
lean_closure_set(v___x_890_, 1, v_s_876_);
lean_closure_set(v___x_890_, 2, v_d_877_);
lean_closure_set(v___x_890_, 3, v___x_889_);
v___x_891_ = 0;
v___x_892_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_892_, 0, v_env_888_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*1, v___x_891_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*1 + 1, v___x_891_);
v___x_893_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_890_, v___x_892_, v_a_879_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_904_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_904_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_904_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_904_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
if (lean_obj_tag(v_a_894_) == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec_ref_known(v_a_894_, 1);
lean_del_object(v___x_896_);
v___x_898_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2, &l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2);
v___x_899_ = l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(v___x_898_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
return v___x_899_;
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; 
v_a_900_ = lean_ctor_get(v_a_894_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v_a_894_, 1);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v_a_900_);
v___x_902_ = v___x_896_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
v_a_905_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_893_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_893_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___boxed(lean_object* v_e_913_, lean_object* v_s_914_, lean_object* v_d_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Meta_Sym_lowerLooseBVarsS(v_e_913_, v_s_914_, v_d_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(lean_object* v_s_924_, lean_object* v_d_925_, lean_object* v_e_926_, lean_object* v_offset_927_, lean_object* v_a_928_, uint8_t v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
switch(lean_obj_tag(v_e_926_))
{
case 5:
{
lean_object* v_fn_932_; lean_object* v_arg_933_; lean_object* v___x_934_; 
v_fn_932_ = lean_ctor_get(v_e_926_, 0);
v_arg_933_ = lean_ctor_get(v_e_926_, 1);
lean_inc(v_offset_927_);
lean_inc_ref(v_fn_932_);
v___x_934_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_924_, v_d_925_, v_fn_932_, v_offset_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v_a_936_; lean_object* v_fst_937_; lean_object* v_snd_938_; lean_object* v___x_939_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
v_a_936_ = lean_ctor_get(v___x_934_, 1);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_934_, 2);
v_fst_937_ = lean_ctor_get(v_a_935_, 0);
lean_inc(v_fst_937_);
v_snd_938_ = lean_ctor_get(v_a_935_, 1);
lean_inc(v_snd_938_);
lean_dec(v_a_935_);
lean_inc_ref(v_arg_933_);
v___x_939_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_924_, v_d_925_, v_arg_933_, v_offset_927_, v_snd_938_, v_a_929_, v_a_930_, v_a_936_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_965_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_a_941_ = lean_ctor_get(v___x_939_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_965_ == 0)
{
v___x_943_ = v___x_939_;
v_isShared_944_ = v_isSharedCheck_965_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_965_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_fst_945_; lean_object* v_snd_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_964_; 
v_fst_945_ = lean_ctor_get(v_a_940_, 0);
v_snd_946_ = lean_ctor_get(v_a_940_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v_a_940_);
if (v_isSharedCheck_964_ == 0)
{
v___x_948_ = v_a_940_;
v_isShared_949_ = v_isSharedCheck_964_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_snd_946_);
lean_inc(v_fst_945_);
lean_dec(v_a_940_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_964_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
size_t v___x_950_; size_t v___x_951_; uint8_t v___x_952_; 
v___x_950_ = lean_ptr_addr(v_fn_932_);
v___x_951_ = lean_ptr_addr(v_fst_937_);
v___x_952_ = lean_usize_dec_eq(v___x_950_, v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_del_object(v___x_948_);
lean_del_object(v___x_943_);
lean_dec_ref_known(v_e_926_, 2);
v___x_953_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_937_, v_fst_945_, v_snd_946_, v_a_929_, v_a_930_, v_a_941_);
return v___x_953_;
}
else
{
size_t v___x_954_; size_t v___x_955_; uint8_t v___x_956_; 
v___x_954_ = lean_ptr_addr(v_arg_933_);
v___x_955_ = lean_ptr_addr(v_fst_945_);
v___x_956_ = lean_usize_dec_eq(v___x_954_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; 
lean_del_object(v___x_948_);
lean_del_object(v___x_943_);
lean_dec_ref_known(v_e_926_, 2);
v___x_957_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_937_, v_fst_945_, v_snd_946_, v_a_929_, v_a_930_, v_a_941_);
return v___x_957_;
}
else
{
lean_object* v___x_959_; 
lean_dec(v_fst_945_);
lean_dec(v_fst_937_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v_e_926_);
v___x_959_ = v___x_948_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_e_926_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_snd_946_);
v___x_959_ = v_reuseFailAlloc_963_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_961_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_959_);
v___x_961_ = v___x_943_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_a_941_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_937_);
lean_dec_ref_known(v_e_926_, 2);
return v___x_939_;
}
}
else
{
lean_dec_ref_known(v_e_926_, 2);
lean_dec(v_offset_927_);
return v___x_934_;
}
}
case 6:
{
lean_object* v_binderName_966_; lean_object* v_binderType_967_; lean_object* v_body_968_; uint8_t v_binderInfo_969_; lean_object* v___x_970_; 
v_binderName_966_ = lean_ctor_get(v_e_926_, 0);
v_binderType_967_ = lean_ctor_get(v_e_926_, 1);
v_body_968_ = lean_ctor_get(v_e_926_, 2);
v_binderInfo_969_ = lean_ctor_get_uint8(v_e_926_, sizeof(void*)*3 + 8);
lean_inc(v_offset_927_);
lean_inc_ref(v_binderType_967_);
v___x_970_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_924_, v_d_925_, v_binderType_967_, v_offset_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v_a_972_; lean_object* v_fst_973_; lean_object* v_snd_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
v_a_972_ = lean_ctor_get(v___x_970_, 1);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_970_, 2);
v_fst_973_ = lean_ctor_get(v_a_971_, 0);
lean_inc(v_fst_973_);
v_snd_974_ = lean_ctor_get(v_a_971_, 1);
lean_inc(v_snd_974_);
lean_dec(v_a_971_);
v___x_975_ = lean_unsigned_to_nat(1u);
v___x_976_ = lean_nat_add(v_offset_927_, v___x_975_);
lean_dec(v_offset_927_);
lean_inc_ref(v_body_968_);
v___x_977_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_924_, v_d_925_, v_body_968_, v___x_976_, v_snd_974_, v_a_929_, v_a_930_, v_a_972_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1003_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_a_979_ = lean_ctor_get(v___x_977_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_981_ = v___x_977_;
v_isShared_982_ = v_isSharedCheck_1003_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1003_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v_fst_983_; lean_object* v_snd_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1002_; 
v_fst_983_ = lean_ctor_get(v_a_978_, 0);
v_snd_984_ = lean_ctor_get(v_a_978_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_a_978_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_986_ = v_a_978_;
v_isShared_987_ = v_isSharedCheck_1002_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_snd_984_);
lean_inc(v_fst_983_);
lean_dec(v_a_978_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1002_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
size_t v___x_988_; size_t v___x_989_; uint8_t v___x_990_; 
v___x_988_ = lean_ptr_addr(v_binderType_967_);
v___x_989_ = lean_ptr_addr(v_fst_973_);
v___x_990_ = lean_usize_dec_eq(v___x_988_, v___x_989_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; 
lean_inc(v_binderName_966_);
lean_del_object(v___x_986_);
lean_del_object(v___x_981_);
lean_dec_ref_known(v_e_926_, 3);
v___x_991_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_966_, v_binderInfo_969_, v_fst_973_, v_fst_983_, v_snd_984_, v_a_929_, v_a_930_, v_a_979_);
return v___x_991_;
}
else
{
size_t v___x_992_; size_t v___x_993_; uint8_t v___x_994_; 
v___x_992_ = lean_ptr_addr(v_body_968_);
v___x_993_ = lean_ptr_addr(v_fst_983_);
v___x_994_ = lean_usize_dec_eq(v___x_992_, v___x_993_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; 
lean_inc(v_binderName_966_);
lean_del_object(v___x_986_);
lean_del_object(v___x_981_);
lean_dec_ref_known(v_e_926_, 3);
v___x_995_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_966_, v_binderInfo_969_, v_fst_973_, v_fst_983_, v_snd_984_, v_a_929_, v_a_930_, v_a_979_);
return v___x_995_;
}
else
{
lean_object* v___x_997_; 
lean_dec(v_fst_983_);
lean_dec(v_fst_973_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v_e_926_);
v___x_997_ = v___x_986_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_e_926_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_snd_984_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_999_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_997_);
v___x_999_ = v___x_981_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_a_979_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_973_);
lean_dec_ref_known(v_e_926_, 3);
return v___x_977_;
}
}
else
{
lean_dec_ref_known(v_e_926_, 3);
lean_dec(v_offset_927_);
return v___x_970_;
}
}
case 7:
{
lean_object* v_binderName_1004_; lean_object* v_binderType_1005_; lean_object* v_body_1006_; uint8_t v_binderInfo_1007_; lean_object* v___x_1008_; 
v_binderName_1004_ = lean_ctor_get(v_e_926_, 0);
v_binderType_1005_ = lean_ctor_get(v_e_926_, 1);
v_body_1006_ = lean_ctor_get(v_e_926_, 2);
v_binderInfo_1007_ = lean_ctor_get_uint8(v_e_926_, sizeof(void*)*3 + 8);
lean_inc(v_offset_927_);
lean_inc_ref(v_binderType_1005_);
v___x_1008_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_924_, v_d_925_, v_binderType_1005_, v_offset_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v_a_1010_; lean_object* v_fst_1011_; lean_object* v_snd_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
v_a_1010_ = lean_ctor_get(v___x_1008_, 1);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1008_, 2);
v_fst_1011_ = lean_ctor_get(v_a_1009_, 0);
lean_inc(v_fst_1011_);
v_snd_1012_ = lean_ctor_get(v_a_1009_, 1);
lean_inc(v_snd_1012_);
lean_dec(v_a_1009_);
v___x_1013_ = lean_unsigned_to_nat(1u);
v___x_1014_ = lean_nat_add(v_offset_927_, v___x_1013_);
lean_dec(v_offset_927_);
lean_inc_ref(v_body_1006_);
v___x_1015_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_924_, v_d_925_, v_body_1006_, v___x_1014_, v_snd_1012_, v_a_929_, v_a_930_, v_a_1010_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1041_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
v_a_1017_ = lean_ctor_get(v___x_1015_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1019_ = v___x_1015_;
v_isShared_1020_ = v_isSharedCheck_1041_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_inc(v_a_1016_);
lean_dec(v___x_1015_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1041_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v_fst_1021_; lean_object* v_snd_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1040_; 
v_fst_1021_ = lean_ctor_get(v_a_1016_, 0);
v_snd_1022_ = lean_ctor_get(v_a_1016_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_a_1016_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1024_ = v_a_1016_;
v_isShared_1025_ = v_isSharedCheck_1040_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_snd_1022_);
lean_inc(v_fst_1021_);
lean_dec(v_a_1016_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1040_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
size_t v___x_1026_; size_t v___x_1027_; uint8_t v___x_1028_; 
v___x_1026_ = lean_ptr_addr(v_binderType_1005_);
v___x_1027_ = lean_ptr_addr(v_fst_1011_);
v___x_1028_ = lean_usize_dec_eq(v___x_1026_, v___x_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; 
lean_inc(v_binderName_1004_);
lean_del_object(v___x_1024_);
lean_del_object(v___x_1019_);
lean_dec_ref_known(v_e_926_, 3);
v___x_1029_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_1004_, v_binderInfo_1007_, v_fst_1011_, v_fst_1021_, v_snd_1022_, v_a_929_, v_a_930_, v_a_1017_);
return v___x_1029_;
}
else
{
size_t v___x_1030_; size_t v___x_1031_; uint8_t v___x_1032_; 
v___x_1030_ = lean_ptr_addr(v_body_1006_);
v___x_1031_ = lean_ptr_addr(v_fst_1021_);
v___x_1032_ = lean_usize_dec_eq(v___x_1030_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
lean_inc(v_binderName_1004_);
lean_del_object(v___x_1024_);
lean_del_object(v___x_1019_);
lean_dec_ref_known(v_e_926_, 3);
v___x_1033_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_1004_, v_binderInfo_1007_, v_fst_1011_, v_fst_1021_, v_snd_1022_, v_a_929_, v_a_930_, v_a_1017_);
return v___x_1033_;
}
else
{
lean_object* v___x_1035_; 
lean_dec(v_fst_1021_);
lean_dec(v_fst_1011_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v_e_926_);
v___x_1035_ = v___x_1024_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_e_926_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_snd_1022_);
v___x_1035_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1035_);
v___x_1037_ = v___x_1019_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_a_1017_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1011_);
lean_dec_ref_known(v_e_926_, 3);
return v___x_1015_;
}
}
else
{
lean_dec_ref_known(v_e_926_, 3);
lean_dec(v_offset_927_);
return v___x_1008_;
}
}
case 8:
{
lean_object* v_declName_1042_; lean_object* v_type_1043_; lean_object* v_value_1044_; lean_object* v_body_1045_; uint8_t v_nondep_1046_; lean_object* v___x_1047_; 
v_declName_1042_ = lean_ctor_get(v_e_926_, 0);
v_type_1043_ = lean_ctor_get(v_e_926_, 1);
v_value_1044_ = lean_ctor_get(v_e_926_, 2);
v_body_1045_ = lean_ctor_get(v_e_926_, 3);
v_nondep_1046_ = lean_ctor_get_uint8(v_e_926_, sizeof(void*)*4 + 8);
lean_inc(v_offset_927_);
lean_inc_ref(v_type_1043_);
v___x_1047_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_924_, v_d_925_, v_type_1043_, v_offset_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v_a_1049_; lean_object* v_fst_1050_; lean_object* v_snd_1051_; lean_object* v___x_1052_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
v_a_1049_ = lean_ctor_get(v___x_1047_, 1);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1047_, 2);
v_fst_1050_ = lean_ctor_get(v_a_1048_, 0);
lean_inc(v_fst_1050_);
v_snd_1051_ = lean_ctor_get(v_a_1048_, 1);
lean_inc(v_snd_1051_);
lean_dec(v_a_1048_);
lean_inc(v_offset_927_);
lean_inc_ref(v_value_1044_);
v___x_1052_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_924_, v_d_925_, v_value_1044_, v_offset_927_, v_snd_1051_, v_a_929_, v_a_930_, v_a_1049_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v_a_1054_; lean_object* v_fst_1055_; lean_object* v_snd_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
v_a_1054_ = lean_ctor_get(v___x_1052_, 1);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1052_, 2);
v_fst_1055_ = lean_ctor_get(v_a_1053_, 0);
lean_inc(v_fst_1055_);
v_snd_1056_ = lean_ctor_get(v_a_1053_, 1);
lean_inc(v_snd_1056_);
lean_dec(v_a_1053_);
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = lean_nat_add(v_offset_927_, v___x_1057_);
lean_dec(v_offset_927_);
lean_inc_ref(v_body_1045_);
v___x_1059_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_924_, v_d_925_, v_body_1045_, v___x_1058_, v_snd_1056_, v_a_929_, v_a_930_, v_a_1054_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1089_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_a_1061_ = lean_ctor_get(v___x_1059_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1063_ = v___x_1059_;
v_isShared_1064_ = v_isSharedCheck_1089_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1089_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v_fst_1065_; lean_object* v_snd_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1088_; 
v_fst_1065_ = lean_ctor_get(v_a_1060_, 0);
v_snd_1066_ = lean_ctor_get(v_a_1060_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_a_1060_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1068_ = v_a_1060_;
v_isShared_1069_ = v_isSharedCheck_1088_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_snd_1066_);
lean_inc(v_fst_1065_);
lean_dec(v_a_1060_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1088_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
size_t v___x_1070_; size_t v___x_1071_; uint8_t v___x_1072_; 
v___x_1070_ = lean_ptr_addr(v_type_1043_);
v___x_1071_ = lean_ptr_addr(v_fst_1050_);
v___x_1072_ = lean_usize_dec_eq(v___x_1070_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; 
lean_inc(v_declName_1042_);
lean_del_object(v___x_1068_);
lean_del_object(v___x_1063_);
lean_dec_ref_known(v_e_926_, 4);
v___x_1073_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1042_, v_fst_1050_, v_fst_1055_, v_fst_1065_, v_nondep_1046_, v_snd_1066_, v_a_929_, v_a_930_, v_a_1061_);
return v___x_1073_;
}
else
{
size_t v___x_1074_; size_t v___x_1075_; uint8_t v___x_1076_; 
v___x_1074_ = lean_ptr_addr(v_value_1044_);
v___x_1075_ = lean_ptr_addr(v_fst_1055_);
v___x_1076_ = lean_usize_dec_eq(v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
lean_inc(v_declName_1042_);
lean_del_object(v___x_1068_);
lean_del_object(v___x_1063_);
lean_dec_ref_known(v_e_926_, 4);
v___x_1077_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1042_, v_fst_1050_, v_fst_1055_, v_fst_1065_, v_nondep_1046_, v_snd_1066_, v_a_929_, v_a_930_, v_a_1061_);
return v___x_1077_;
}
else
{
size_t v___x_1078_; size_t v___x_1079_; uint8_t v___x_1080_; 
v___x_1078_ = lean_ptr_addr(v_body_1045_);
v___x_1079_ = lean_ptr_addr(v_fst_1065_);
v___x_1080_ = lean_usize_dec_eq(v___x_1078_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; 
lean_inc(v_declName_1042_);
lean_del_object(v___x_1068_);
lean_del_object(v___x_1063_);
lean_dec_ref_known(v_e_926_, 4);
v___x_1081_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1042_, v_fst_1050_, v_fst_1055_, v_fst_1065_, v_nondep_1046_, v_snd_1066_, v_a_929_, v_a_930_, v_a_1061_);
return v___x_1081_;
}
else
{
lean_object* v___x_1083_; 
lean_dec(v_fst_1065_);
lean_dec(v_fst_1055_);
lean_dec(v_fst_1050_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v_e_926_);
v___x_1083_ = v___x_1068_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_e_926_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_snd_1066_);
v___x_1083_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1085_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1083_);
v___x_1085_ = v___x_1063_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_a_1061_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
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
lean_dec(v_fst_1055_);
lean_dec(v_fst_1050_);
lean_dec_ref_known(v_e_926_, 4);
return v___x_1059_;
}
}
else
{
lean_dec(v_fst_1050_);
lean_dec_ref_known(v_e_926_, 4);
lean_dec(v_offset_927_);
return v___x_1052_;
}
}
else
{
lean_dec_ref_known(v_e_926_, 4);
lean_dec(v_offset_927_);
return v___x_1047_;
}
}
case 10:
{
lean_object* v_data_1090_; lean_object* v_expr_1091_; lean_object* v___x_1092_; 
v_data_1090_ = lean_ctor_get(v_e_926_, 0);
v_expr_1091_ = lean_ctor_get(v_e_926_, 1);
lean_inc_ref(v_expr_1091_);
v___x_1092_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_924_, v_d_925_, v_expr_1091_, v_offset_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1114_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_a_1094_ = lean_ctor_get(v___x_1092_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1096_ = v___x_1092_;
v_isShared_1097_ = v_isSharedCheck_1114_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1114_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v_fst_1098_; lean_object* v_snd_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1113_; 
v_fst_1098_ = lean_ctor_get(v_a_1093_, 0);
v_snd_1099_ = lean_ctor_get(v_a_1093_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_a_1093_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1101_ = v_a_1093_;
v_isShared_1102_ = v_isSharedCheck_1113_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_snd_1099_);
lean_inc(v_fst_1098_);
lean_dec(v_a_1093_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1113_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
size_t v___x_1103_; size_t v___x_1104_; uint8_t v___x_1105_; 
v___x_1103_ = lean_ptr_addr(v_expr_1091_);
v___x_1104_ = lean_ptr_addr(v_fst_1098_);
v___x_1105_ = lean_usize_dec_eq(v___x_1103_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; 
lean_inc(v_data_1090_);
lean_del_object(v___x_1101_);
lean_del_object(v___x_1096_);
lean_dec_ref_known(v_e_926_, 2);
v___x_1106_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_1090_, v_fst_1098_, v_snd_1099_, v_a_929_, v_a_930_, v_a_1094_);
return v___x_1106_;
}
else
{
lean_object* v___x_1108_; 
lean_dec(v_fst_1098_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v_e_926_);
v___x_1108_ = v___x_1101_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_e_926_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_snd_1099_);
v___x_1108_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1110_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v___x_1108_);
v___x_1110_ = v___x_1096_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_a_1094_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_926_, 2);
return v___x_1092_;
}
}
case 11:
{
lean_object* v_typeName_1115_; lean_object* v_idx_1116_; lean_object* v_struct_1117_; lean_object* v___x_1118_; 
v_typeName_1115_ = lean_ctor_get(v_e_926_, 0);
v_idx_1116_ = lean_ctor_get(v_e_926_, 1);
v_struct_1117_ = lean_ctor_get(v_e_926_, 2);
lean_inc_ref(v_struct_1117_);
v___x_1118_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_924_, v_d_925_, v_struct_1117_, v_offset_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1140_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_a_1120_ = lean_ctor_get(v___x_1118_, 1);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1122_ = v___x_1118_;
v_isShared_1123_ = v_isSharedCheck_1140_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1140_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v_fst_1124_; lean_object* v_snd_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1139_; 
v_fst_1124_ = lean_ctor_get(v_a_1119_, 0);
v_snd_1125_ = lean_ctor_get(v_a_1119_, 1);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_a_1119_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1127_ = v_a_1119_;
v_isShared_1128_ = v_isSharedCheck_1139_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_snd_1125_);
lean_inc(v_fst_1124_);
lean_dec(v_a_1119_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1139_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
size_t v___x_1129_; size_t v___x_1130_; uint8_t v___x_1131_; 
v___x_1129_ = lean_ptr_addr(v_struct_1117_);
v___x_1130_ = lean_ptr_addr(v_fst_1124_);
v___x_1131_ = lean_usize_dec_eq(v___x_1129_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
lean_inc(v_idx_1116_);
lean_inc(v_typeName_1115_);
lean_del_object(v___x_1127_);
lean_del_object(v___x_1122_);
lean_dec_ref_known(v_e_926_, 3);
v___x_1132_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_1115_, v_idx_1116_, v_fst_1124_, v_snd_1125_, v_a_929_, v_a_930_, v_a_1120_);
return v___x_1132_;
}
else
{
lean_object* v___x_1134_; 
lean_dec(v_fst_1124_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v_e_926_);
v___x_1134_ = v___x_1127_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_e_926_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_snd_1125_);
v___x_1134_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1136_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1134_);
v___x_1136_ = v___x_1122_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_a_1120_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_926_, 3);
return v___x_1118_;
}
}
default: 
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec(v_offset_927_);
lean_dec_ref(v_e_926_);
v___x_1141_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
v___x_1142_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_1141_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
return v___x_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(lean_object* v_s_1143_, lean_object* v_d_1144_, lean_object* v_e_1145_, lean_object* v_offset_1146_, lean_object* v_a_1147_, uint8_t v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v_key_1151_; lean_object* v_a_1153_; lean_object* v___x_1166_; 
lean_inc(v_offset_1146_);
lean_inc_ref(v_e_1145_);
v_key_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1151_, 0, v_e_1145_);
lean_ctor_set(v_key_1151_, 1, v_offset_1146_);
v___x_1166_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_1147_, v_key_1151_);
if (lean_obj_tag(v___x_1166_) == 1)
{
lean_object* v_val_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_dec_ref_known(v_key_1151_, 2);
lean_dec(v_offset_1146_);
lean_dec_ref(v_e_1145_);
v_val_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_val_1167_);
lean_dec_ref_known(v___x_1166_, 1);
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v_val_1167_);
lean_ctor_set(v___x_1168_, 1, v_a_1147_);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v_a_1150_);
return v___x_1169_;
}
else
{
lean_object* v_s_u2081_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
lean_dec(v___x_1166_);
v_s_u2081_1170_ = lean_nat_add(v_s_1143_, v_offset_1146_);
v___x_1171_ = l_Lean_Expr_looseBVarRange(v_e_1145_);
v___x_1172_ = lean_nat_dec_le(v___x_1171_, v_s_u2081_1170_);
lean_dec(v___x_1171_);
if (v___x_1172_ == 0)
{
if (lean_obj_tag(v_e_1145_) == 0)
{
lean_object* v_deBruijnIndex_1173_; uint8_t v___x_1174_; 
v_deBruijnIndex_1173_ = lean_ctor_get(v_e_1145_, 0);
v___x_1174_ = lean_nat_dec_le(v_s_u2081_1170_, v_deBruijnIndex_1173_);
lean_dec(v_s_u2081_1170_);
if (v___x_1174_ == 0)
{
v_a_1153_ = v_a_1150_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_inc(v_deBruijnIndex_1173_);
lean_dec_ref_known(v_e_1145_, 1);
lean_dec(v_offset_1146_);
v___x_1175_ = lean_nat_add(v_deBruijnIndex_1173_, v_d_1144_);
lean_dec(v_deBruijnIndex_1173_);
v___x_1176_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_1175_, v_a_1150_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v_a_1178_; lean_object* v___x_1179_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
v_a_1178_ = lean_ctor_get(v___x_1176_, 1);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1176_, 2);
v___x_1179_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1151_, v_a_1177_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1178_);
return v___x_1179_;
}
else
{
lean_object* v_a_1180_; lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec_ref_known(v_key_1151_, 2);
lean_dec_ref(v_a_1147_);
v_a_1180_ = lean_ctor_get(v___x_1176_, 0);
v_a_1181_ = lean_ctor_get(v___x_1176_, 1);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1176_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_inc(v_a_1180_);
lean_dec(v___x_1176_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1180_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
else
{
lean_dec(v_s_u2081_1170_);
v_a_1153_ = v_a_1150_;
goto v___jp_1152_;
}
}
else
{
lean_object* v___x_1189_; 
lean_dec(v_s_u2081_1170_);
lean_dec(v_offset_1146_);
v___x_1189_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1151_, v_e_1145_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
return v___x_1189_;
}
}
v___jp_1152_:
{
switch(lean_obj_tag(v_e_1145_))
{
case 9:
{
lean_object* v___x_1154_; 
lean_dec(v_offset_1146_);
v___x_1154_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1151_, v_e_1145_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1153_);
return v___x_1154_;
}
case 2:
{
lean_object* v___x_1155_; 
lean_dec(v_offset_1146_);
v___x_1155_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1151_, v_e_1145_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1153_);
return v___x_1155_;
}
case 0:
{
lean_object* v___x_1156_; 
lean_dec(v_offset_1146_);
v___x_1156_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1151_, v_e_1145_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1153_);
return v___x_1156_;
}
case 1:
{
lean_object* v___x_1157_; 
lean_dec(v_offset_1146_);
v___x_1157_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1151_, v_e_1145_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1153_);
return v___x_1157_;
}
case 4:
{
lean_object* v___x_1158_; 
lean_dec(v_offset_1146_);
v___x_1158_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1151_, v_e_1145_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1153_);
return v___x_1158_;
}
case 3:
{
lean_object* v___x_1159_; 
lean_dec(v_offset_1146_);
v___x_1159_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1151_, v_e_1145_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1153_);
return v___x_1159_;
}
default: 
{
lean_object* v___x_1160_; 
v___x_1160_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_1143_, v_d_1144_, v_e_1145_, v_offset_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1153_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v_a_1162_; lean_object* v_fst_1163_; lean_object* v_snd_1164_; lean_object* v___x_1165_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
v_a_1162_ = lean_ctor_get(v___x_1160_, 1);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1160_, 2);
v_fst_1163_ = lean_ctor_get(v_a_1161_, 0);
lean_inc(v_fst_1163_);
v_snd_1164_ = lean_ctor_get(v_a_1161_, 1);
lean_inc(v_snd_1164_);
lean_dec(v_a_1161_);
v___x_1165_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1151_, v_fst_1163_, v_snd_1164_, v_a_1148_, v_a_1149_, v_a_1162_);
return v___x_1165_;
}
else
{
lean_dec_ref_known(v_key_1151_, 2);
return v___x_1160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0___boxed(lean_object* v_s_1190_, lean_object* v_d_1191_, lean_object* v_e_1192_, lean_object* v_offset_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
uint8_t v_a_boxed_1198_; lean_object* v_res_1199_; 
v_a_boxed_1198_ = lean_unbox(v_a_1195_);
v_res_1199_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1190_, v_d_1191_, v_e_1192_, v_offset_1193_, v_a_1194_, v_a_boxed_1198_, v_a_1196_, v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_d_1191_);
lean_dec(v_s_1190_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0___boxed(lean_object* v_s_1200_, lean_object* v_d_1201_, lean_object* v_e_1202_, lean_object* v_offset_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
uint8_t v_a_boxed_1208_; lean_object* v_res_1209_; 
v_a_boxed_1208_ = lean_unbox(v_a_1205_);
v_res_1209_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_1200_, v_d_1201_, v_e_1202_, v_offset_1203_, v_a_1204_, v_a_boxed_1208_, v_a_1206_, v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_d_1201_);
lean_dec(v_s_1200_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27(lean_object* v_e_1210_, lean_object* v_s_1211_, lean_object* v_d_1212_, uint8_t v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = l_Lean_Expr_looseBVarRange(v_e_1210_);
v___x_1217_ = lean_nat_dec_le(v___x_1216_, v_s_1211_);
lean_dec(v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v_a_1220_; 
v___x_1218_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_e_1210_) == 0)
{
lean_object* v_deBruijnIndex_1248_; uint8_t v___x_1249_; 
v_deBruijnIndex_1248_ = lean_ctor_get(v_e_1210_, 0);
v___x_1249_ = lean_nat_dec_le(v_s_1211_, v_deBruijnIndex_1248_);
if (v___x_1249_ == 0)
{
v_a_1220_ = v_a_1215_;
goto v___jp_1219_;
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_inc(v_deBruijnIndex_1248_);
lean_dec_ref_known(v_e_1210_, 1);
v___x_1250_ = lean_nat_add(v_deBruijnIndex_1248_, v_d_1212_);
lean_dec(v_deBruijnIndex_1248_);
v___x_1251_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_1250_, v_a_1215_);
return v___x_1251_;
}
}
else
{
v_a_1220_ = v_a_1215_;
goto v___jp_1219_;
}
v___jp_1219_:
{
switch(lean_obj_tag(v_e_1210_))
{
case 9:
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v_e_1210_);
lean_ctor_set(v___x_1221_, 1, v_a_1220_);
return v___x_1221_;
}
case 2:
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_e_1210_);
lean_ctor_set(v___x_1222_, 1, v_a_1220_);
return v___x_1222_;
}
case 0:
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v_e_1210_);
lean_ctor_set(v___x_1223_, 1, v_a_1220_);
return v___x_1223_;
}
case 1:
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v_e_1210_);
lean_ctor_set(v___x_1224_, 1, v_a_1220_);
return v___x_1224_;
}
case 4:
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v_e_1210_);
lean_ctor_set(v___x_1225_, 1, v_a_1220_);
return v___x_1225_;
}
case 3:
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v_e_1210_);
lean_ctor_set(v___x_1226_, 1, v_a_1220_);
return v___x_1226_;
}
default: 
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1);
v___x_1228_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_1211_, v_d_1212_, v_e_1210_, v___x_1218_, v___x_1227_, v_a_1213_, v_a_1214_, v_a_1220_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1238_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_a_1230_ = lean_ctor_get(v___x_1228_, 1);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1232_ = v___x_1228_;
v_isShared_1233_ = v_isSharedCheck_1238_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1238_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v_fst_1234_; lean_object* v___x_1236_; 
v_fst_1234_ = lean_ctor_get(v_a_1229_, 0);
lean_inc(v_fst_1234_);
lean_dec(v_a_1229_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v_fst_1234_);
v___x_1236_ = v___x_1232_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_fst_1234_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_a_1230_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
v_a_1239_ = lean_ctor_get(v___x_1228_, 0);
v_a_1240_ = lean_ctor_get(v___x_1228_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1228_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_inc(v_a_1239_);
lean_dec(v___x_1228_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1239_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_e_1210_);
lean_ctor_set(v___x_1252_, 1, v_a_1215_);
return v___x_1252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27___boxed(lean_object* v_e_1253_, lean_object* v_s_1254_, lean_object* v_d_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
uint8_t v_a_boxed_1259_; lean_object* v_res_1260_; 
v_a_boxed_1259_ = lean_unbox(v_a_1256_);
v_res_1260_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_e_1253_, v_s_1254_, v_d_1255_, v_a_boxed_1259_, v_a_1257_, v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_d_1255_);
lean_dec(v_s_1254_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS(lean_object* v_e_1261_, lean_object* v_s_1262_, lean_object* v_d_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v_debug_1273_; lean_object* v_env_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1271_ = lean_st_ref_get(v_a_1265_);
v___x_1272_ = lean_st_ref_get(v_a_1269_);
v_debug_1273_ = lean_ctor_get_uint8(v___x_1271_, sizeof(void*)*11);
lean_dec(v___x_1271_);
v_env_1274_ = lean_ctor_get(v___x_1272_, 0);
lean_inc_ref(v_env_1274_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(v_debug_1273_);
v___x_1276_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_liftLooseBVarsS_x27___boxed), 6, 4);
lean_closure_set(v___x_1276_, 0, v_e_1261_);
lean_closure_set(v___x_1276_, 1, v_s_1262_);
lean_closure_set(v___x_1276_, 2, v_d_1263_);
lean_closure_set(v___x_1276_, 3, v___x_1275_);
v___x_1277_ = 0;
v___x_1278_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1278_, 0, v_env_1274_);
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*1, v___x_1277_);
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*1 + 1, v___x_1277_);
v___x_1279_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_1276_, v___x_1278_, v_a_1265_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1290_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1290_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1290_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
if (lean_obj_tag(v_a_1280_) == 0)
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec_ref_known(v_a_1280_, 1);
lean_del_object(v___x_1282_);
v___x_1284_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2, &l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2);
v___x_1285_ = l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(v___x_1284_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1285_;
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; 
v_a_1286_ = lean_ctor_get(v_a_1280_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v_a_1280_, 1);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v_a_1286_);
v___x_1288_ = v___x_1282_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_a_1291_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1279_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1279_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___boxed(lean_object* v_e_1299_, lean_object* v_s_1300_, lean_object* v_d_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_Meta_Sym_liftLooseBVarsS(v_e_1299_, v_s_1300_, v_d_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
return v_res_1309_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_LooseBVarsS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
