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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
uint8_t v___y_24131__boxed_14_; lean_object* v_res_15_; 
v___y_24131__boxed_14_ = lean_unbox(v___y_11_);
v_res_15_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(v_idx_10_, v___y_24131__boxed_14_, v___y_12_, v___y_13_);
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
uint8_t v_bi_boxed_78_; uint8_t v___y_24143__boxed_79_; lean_object* v_res_80_; 
v_bi_boxed_78_ = lean_unbox(v_bi_71_);
v___y_24143__boxed_79_ = lean_unbox(v___y_75_);
v_res_80_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_x_70_, v_bi_boxed_78_, v_t_72_, v_b_73_, v___y_74_, v___y_24143__boxed_79_, v___y_76_, v___y_77_);
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
uint8_t v___y_24249__boxed_130_; lean_object* v_res_131_; 
v___y_24249__boxed_130_ = lean_unbox(v___y_127_);
v_res_131_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_structName_123_, v_idx_124_, v_struct_125_, v___y_126_, v___y_24249__boxed_130_, v___y_128_, v___y_129_);
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
uint8_t v_bi_boxed_194_; uint8_t v___y_24332__boxed_195_; lean_object* v_res_196_; 
v_bi_boxed_194_ = lean_unbox(v_bi_187_);
v___y_24332__boxed_195_ = lean_unbox(v___y_191_);
v_res_196_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_x_186_, v_bi_boxed_194_, v_t_188_, v_b_189_, v___y_190_, v___y_24332__boxed_195_, v___y_192_, v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(lean_object* v_msg_204_, lean_object* v___y_205_, uint8_t v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___f_209_; lean_object* v___f_210_; lean_object* v___f_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_23836__overap_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
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
v___x_23836__overap_233_ = lean_panic_fn_borrowed(v___x_232_, v_msg_204_);
lean_dec(v___x_232_);
v___x_234_ = lean_box(v___y_206_);
lean_inc_ref(v___y_207_);
v___x_235_ = lean_apply_4(v___x_23836__overap_233_, v___y_205_, v___x_234_, v___y_207_, v___y_208_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___boxed(lean_object* v_msg_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
uint8_t v___y_24452__boxed_241_; lean_object* v_res_242_; 
v___y_24452__boxed_241_ = lean_unbox(v___y_238_);
v_res_242_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v_msg_236_, v___y_237_, v___y_24452__boxed_241_, v___y_239_, v___y_240_);
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
uint8_t v___y_24523__boxed_301_; lean_object* v_res_302_; 
v___y_24523__boxed_301_ = lean_unbox(v___y_298_);
v_res_302_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_f_295_, v_a_296_, v___y_297_, v___y_24523__boxed_301_, v___y_299_, v___y_300_);
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
lean_object* v_key_306_; lean_object* v_value_307_; lean_object* v_tail_308_; uint8_t v___y_310_; lean_object* v_fst_313_; lean_object* v_snd_314_; lean_object* v_fst_315_; lean_object* v_snd_316_; size_t v___x_317_; size_t v___x_318_; uint8_t v___x_319_; 
v_key_306_ = lean_ctor_get(v_x_304_, 0);
v_value_307_ = lean_ctor_get(v_x_304_, 1);
v_tail_308_ = lean_ctor_get(v_x_304_, 2);
v_fst_313_ = lean_ctor_get(v_key_306_, 0);
v_snd_314_ = lean_ctor_get(v_key_306_, 1);
v_fst_315_ = lean_ctor_get(v_a_303_, 0);
v_snd_316_ = lean_ctor_get(v_a_303_, 1);
v___x_317_ = lean_ptr_addr(v_fst_313_);
v___x_318_ = lean_ptr_addr(v_fst_315_);
v___x_319_ = lean_usize_dec_eq(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
v___y_310_ = v___x_319_;
goto v___jp_309_;
}
else
{
uint8_t v___x_320_; 
v___x_320_ = lean_nat_dec_eq(v_snd_314_, v_snd_316_);
v___y_310_ = v___x_320_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg___boxed(lean_object* v_a_321_, lean_object* v_x_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_321_, v_x_322_);
lean_dec(v_x_322_);
lean_dec_ref(v_a_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(lean_object* v_m_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_buckets_326_; lean_object* v_fst_327_; lean_object* v_snd_328_; lean_object* v___x_329_; size_t v___x_330_; size_t v___x_331_; size_t v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v_fold_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_buckets_326_ = lean_ctor_get(v_m_324_, 1);
v_fst_327_ = lean_ctor_get(v_a_325_, 0);
v_snd_328_ = lean_ctor_get(v_a_325_, 1);
v___x_329_ = lean_array_get_size(v_buckets_326_);
v___x_330_ = lean_ptr_addr(v_fst_327_);
v___x_331_ = ((size_t)3ULL);
v___x_332_ = lean_usize_shift_right(v___x_330_, v___x_331_);
v___x_333_ = lean_usize_to_uint64(v___x_332_);
v___x_334_ = lean_uint64_of_nat(v_snd_328_);
v___x_335_ = lean_uint64_mix_hash(v___x_333_, v___x_334_);
v___x_336_ = 32ULL;
v___x_337_ = lean_uint64_shift_right(v___x_335_, v___x_336_);
v_fold_338_ = lean_uint64_xor(v___x_335_, v___x_337_);
v___x_339_ = 16ULL;
v___x_340_ = lean_uint64_shift_right(v_fold_338_, v___x_339_);
v___x_341_ = lean_uint64_xor(v_fold_338_, v___x_340_);
v___x_342_ = lean_uint64_to_usize(v___x_341_);
v___x_343_ = lean_usize_of_nat(v___x_329_);
v___x_344_ = ((size_t)1ULL);
v___x_345_ = lean_usize_sub(v___x_343_, v___x_344_);
v___x_346_ = lean_usize_land(v___x_342_, v___x_345_);
v___x_347_ = lean_array_uget_borrowed(v_buckets_326_, v___x_346_);
v___x_348_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_325_, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_m_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_349_, v_a_350_);
lean_dec_ref(v_a_350_);
lean_dec_ref(v_m_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(lean_object* v_x_352_, lean_object* v_t_353_, lean_object* v_v_354_, lean_object* v_b_355_, uint8_t v_nondep_356_, lean_object* v___y_357_, uint8_t v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___y_362_; lean_object* v___y_363_; 
if (v___y_358_ == 0)
{
v___y_362_ = v___y_357_;
v___y_363_ = v___y_360_;
goto v___jp_361_;
}
else
{
lean_object* v___x_385_; 
lean_inc_ref(v_t_353_);
v___x_385_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_353_, v___y_358_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; 
v_a_386_ = lean_ctor_get(v___x_385_, 1);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 2);
lean_inc_ref(v_v_354_);
v___x_387_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_354_, v___y_358_, v___y_359_, v_a_386_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_389_; 
v_a_388_ = lean_ctor_get(v___x_387_, 1);
lean_inc(v_a_388_);
lean_dec_ref_known(v___x_387_, 2);
lean_inc_ref(v_b_355_);
v___x_389_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_355_, v___y_358_, v___y_359_, v_a_388_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; 
v_a_390_ = lean_ctor_get(v___x_389_, 1);
lean_inc(v_a_390_);
lean_dec_ref_known(v___x_389_, 2);
v___y_362_ = v___y_357_;
v___y_363_ = v_a_390_;
goto v___jp_361_;
}
else
{
lean_object* v_a_391_; lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec_ref(v___y_357_);
lean_dec_ref(v_b_355_);
lean_dec_ref(v_v_354_);
lean_dec_ref(v_t_353_);
lean_dec(v_x_352_);
v_a_391_ = lean_ctor_get(v___x_389_, 0);
v_a_392_ = lean_ctor_get(v___x_389_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_389_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_inc(v_a_391_);
lean_dec(v___x_389_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_391_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec_ref(v___y_357_);
lean_dec_ref(v_b_355_);
lean_dec_ref(v_v_354_);
lean_dec_ref(v_t_353_);
lean_dec(v_x_352_);
v_a_400_ = lean_ctor_get(v___x_387_, 0);
v_a_401_ = lean_ctor_get(v___x_387_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_387_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_inc(v_a_400_);
lean_dec(v___x_387_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_400_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
else
{
lean_object* v_a_409_; lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec_ref(v___y_357_);
lean_dec_ref(v_b_355_);
lean_dec_ref(v_v_354_);
lean_dec_ref(v_t_353_);
lean_dec(v_x_352_);
v_a_409_ = lean_ctor_get(v___x_385_, 0);
v_a_410_ = lean_ctor_get(v___x_385_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_385_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_inc(v_a_409_);
lean_dec(v___x_385_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_409_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
v___jp_361_:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = l_Lean_Expr_letE___override(v_x_352_, v_t_353_, v_v_354_, v_b_355_, v_nondep_356_);
v___x_365_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_364_, v___y_363_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_375_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_a_367_ = lean_ctor_get(v___x_365_, 1);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_375_ == 0)
{
v___x_369_ = v___x_365_;
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v_a_366_);
lean_ctor_set(v___x_371_, 1, v___y_362_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_371_);
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_a_367_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
else
{
lean_object* v_a_376_; lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec_ref(v___y_362_);
v_a_376_ = lean_ctor_get(v___x_365_, 0);
v_a_377_ = lean_ctor_get(v___x_365_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_365_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_inc(v_a_376_);
lean_dec(v___x_365_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_376_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5___boxed(lean_object* v_x_418_, lean_object* v_t_419_, lean_object* v_v_420_, lean_object* v_b_421_, lean_object* v_nondep_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
uint8_t v_nondep_boxed_427_; uint8_t v___y_24708__boxed_428_; lean_object* v_res_429_; 
v_nondep_boxed_427_ = lean_unbox(v_nondep_422_);
v___y_24708__boxed_428_ = lean_unbox(v___y_424_);
v_res_429_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_x_418_, v_t_419_, v_v_420_, v_b_421_, v_nondep_boxed_427_, v___y_423_, v___y_24708__boxed_428_, v___y_425_, v___y_426_);
lean_dec_ref(v___y_425_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(lean_object* v_d_430_, lean_object* v_e_431_, lean_object* v___y_432_, uint8_t v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___y_437_; lean_object* v___y_438_; 
if (v___y_433_ == 0)
{
v___y_437_ = v___y_432_;
v___y_438_ = v___y_435_;
goto v___jp_436_;
}
else
{
lean_object* v___x_460_; 
lean_inc_ref(v_e_431_);
v___x_460_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_431_, v___y_433_, v___y_434_, v___y_435_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; 
v_a_461_ = lean_ctor_get(v___x_460_, 1);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_460_, 2);
v___y_437_ = v___y_432_;
v___y_438_ = v_a_461_;
goto v___jp_436_;
}
else
{
lean_object* v_a_462_; lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec_ref(v___y_432_);
lean_dec_ref(v_e_431_);
lean_dec(v_d_430_);
v_a_462_ = lean_ctor_get(v___x_460_, 0);
v_a_463_ = lean_ctor_get(v___x_460_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_460_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_inc(v_a_462_);
lean_dec(v___x_460_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_462_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
v___jp_436_:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = l_Lean_Expr_mdata___override(v_d_430_, v_e_431_);
v___x_440_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_439_, v___y_438_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_450_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_a_442_ = lean_ctor_get(v___x_440_, 1);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_450_ == 0)
{
v___x_444_ = v___x_440_;
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_a_441_);
lean_ctor_set(v___x_446_, 1, v___y_437_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_446_);
v___x_448_ = v___x_444_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_a_442_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
else
{
lean_object* v_a_451_; lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec_ref(v___y_437_);
v_a_451_ = lean_ctor_get(v___x_440_, 0);
v_a_452_ = lean_ctor_get(v___x_440_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_440_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_inc(v_a_451_);
lean_dec(v___x_440_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_451_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6___boxed(lean_object* v_d_471_, lean_object* v_e_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
uint8_t v___y_24837__boxed_477_; lean_object* v_res_478_; 
v___y_24837__boxed_477_ = lean_unbox(v___y_474_);
v_res_478_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_d_471_, v_e_472_, v___y_473_, v___y_24837__boxed_477_, v___y_475_, v___y_476_);
lean_dec_ref(v___y_475_);
return v_res_478_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_482_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2));
v___x_483_ = lean_unsigned_to_nat(67u);
v___x_484_ = lean_unsigned_to_nat(35u);
v___x_485_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1));
v___x_486_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0));
v___x_487_ = l_mkPanicMessageWithDecl(v___x_486_, v___x_485_, v___x_484_, v___x_483_, v___x_482_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(lean_object* v_s_488_, lean_object* v_d_489_, lean_object* v_e_490_, lean_object* v_offset_491_, lean_object* v_a_492_, uint8_t v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
switch(lean_obj_tag(v_e_490_))
{
case 5:
{
lean_object* v_fn_496_; lean_object* v_arg_497_; lean_object* v___x_498_; 
v_fn_496_ = lean_ctor_get(v_e_490_, 0);
v_arg_497_ = lean_ctor_get(v_e_490_, 1);
lean_inc(v_offset_491_);
lean_inc_ref(v_fn_496_);
v___x_498_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_488_, v_d_489_, v_fn_496_, v_offset_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v_a_500_; lean_object* v_fst_501_; lean_object* v_snd_502_; lean_object* v___x_503_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
v_a_500_ = lean_ctor_get(v___x_498_, 1);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_498_, 2);
v_fst_501_ = lean_ctor_get(v_a_499_, 0);
lean_inc(v_fst_501_);
v_snd_502_ = lean_ctor_get(v_a_499_, 1);
lean_inc(v_snd_502_);
lean_dec(v_a_499_);
lean_inc_ref(v_arg_497_);
v___x_503_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_488_, v_d_489_, v_arg_497_, v_offset_491_, v_snd_502_, v_a_493_, v_a_494_, v_a_500_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_530_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_a_505_ = lean_ctor_get(v___x_503_, 1);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_530_ == 0)
{
v___x_507_ = v___x_503_;
v_isShared_508_ = v_isSharedCheck_530_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_530_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v_fst_509_; lean_object* v_snd_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_529_; 
v_fst_509_ = lean_ctor_get(v_a_504_, 0);
v_snd_510_ = lean_ctor_get(v_a_504_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v_a_504_);
if (v_isSharedCheck_529_ == 0)
{
v___x_512_ = v_a_504_;
v_isShared_513_ = v_isSharedCheck_529_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_snd_510_);
lean_inc(v_fst_509_);
lean_dec(v_a_504_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_529_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
uint8_t v___y_515_; size_t v___x_523_; size_t v___x_524_; uint8_t v___x_525_; 
v___x_523_ = lean_ptr_addr(v_fn_496_);
v___x_524_ = lean_ptr_addr(v_fst_501_);
v___x_525_ = lean_usize_dec_eq(v___x_523_, v___x_524_);
if (v___x_525_ == 0)
{
v___y_515_ = v___x_525_;
goto v___jp_514_;
}
else
{
size_t v___x_526_; size_t v___x_527_; uint8_t v___x_528_; 
v___x_526_ = lean_ptr_addr(v_arg_497_);
v___x_527_ = lean_ptr_addr(v_fst_509_);
v___x_528_ = lean_usize_dec_eq(v___x_526_, v___x_527_);
v___y_515_ = v___x_528_;
goto v___jp_514_;
}
v___jp_514_:
{
if (v___y_515_ == 0)
{
lean_object* v___x_516_; 
lean_del_object(v___x_512_);
lean_del_object(v___x_507_);
lean_dec_ref_known(v_e_490_, 2);
v___x_516_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_501_, v_fst_509_, v_snd_510_, v_a_493_, v_a_494_, v_a_505_);
return v___x_516_;
}
else
{
lean_object* v___x_518_; 
lean_dec(v_fst_509_);
lean_dec(v_fst_501_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v_e_490_);
v___x_518_ = v___x_512_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_e_490_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_snd_510_);
v___x_518_ = v_reuseFailAlloc_522_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_520_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_518_);
v___x_520_ = v___x_507_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_a_505_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_501_);
lean_dec_ref_known(v_e_490_, 2);
return v___x_503_;
}
}
else
{
lean_dec_ref_known(v_e_490_, 2);
lean_dec(v_offset_491_);
return v___x_498_;
}
}
case 6:
{
lean_object* v_binderName_531_; lean_object* v_binderType_532_; lean_object* v_body_533_; uint8_t v_binderInfo_534_; lean_object* v___x_535_; 
v_binderName_531_ = lean_ctor_get(v_e_490_, 0);
v_binderType_532_ = lean_ctor_get(v_e_490_, 1);
v_body_533_ = lean_ctor_get(v_e_490_, 2);
v_binderInfo_534_ = lean_ctor_get_uint8(v_e_490_, sizeof(void*)*3 + 8);
lean_inc(v_offset_491_);
lean_inc_ref(v_binderType_532_);
v___x_535_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_488_, v_d_489_, v_binderType_532_, v_offset_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v_a_537_; lean_object* v_fst_538_; lean_object* v_snd_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
v_a_537_ = lean_ctor_get(v___x_535_, 1);
lean_inc(v_a_537_);
lean_dec_ref_known(v___x_535_, 2);
v_fst_538_ = lean_ctor_get(v_a_536_, 0);
lean_inc(v_fst_538_);
v_snd_539_ = lean_ctor_get(v_a_536_, 1);
lean_inc(v_snd_539_);
lean_dec(v_a_536_);
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_nat_add(v_offset_491_, v___x_540_);
lean_dec(v_offset_491_);
lean_inc_ref(v_body_533_);
v___x_542_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_488_, v_d_489_, v_body_533_, v___x_541_, v_snd_539_, v_a_493_, v_a_494_, v_a_537_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_569_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_a_544_ = lean_ctor_get(v___x_542_, 1);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_569_ == 0)
{
v___x_546_ = v___x_542_;
v_isShared_547_ = v_isSharedCheck_569_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_569_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v_fst_548_; lean_object* v_snd_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_568_; 
v_fst_548_ = lean_ctor_get(v_a_543_, 0);
v_snd_549_ = lean_ctor_get(v_a_543_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_a_543_);
if (v_isSharedCheck_568_ == 0)
{
v___x_551_ = v_a_543_;
v_isShared_552_ = v_isSharedCheck_568_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_snd_549_);
lean_inc(v_fst_548_);
lean_dec(v_a_543_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_568_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
uint8_t v___y_554_; size_t v___x_562_; size_t v___x_563_; uint8_t v___x_564_; 
v___x_562_ = lean_ptr_addr(v_binderType_532_);
v___x_563_ = lean_ptr_addr(v_fst_538_);
v___x_564_ = lean_usize_dec_eq(v___x_562_, v___x_563_);
if (v___x_564_ == 0)
{
v___y_554_ = v___x_564_;
goto v___jp_553_;
}
else
{
size_t v___x_565_; size_t v___x_566_; uint8_t v___x_567_; 
v___x_565_ = lean_ptr_addr(v_body_533_);
v___x_566_ = lean_ptr_addr(v_fst_548_);
v___x_567_ = lean_usize_dec_eq(v___x_565_, v___x_566_);
v___y_554_ = v___x_567_;
goto v___jp_553_;
}
v___jp_553_:
{
if (v___y_554_ == 0)
{
lean_object* v___x_555_; 
lean_inc(v_binderName_531_);
lean_del_object(v___x_551_);
lean_del_object(v___x_546_);
lean_dec_ref_known(v_e_490_, 3);
v___x_555_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_531_, v_binderInfo_534_, v_fst_538_, v_fst_548_, v_snd_549_, v_a_493_, v_a_494_, v_a_544_);
return v___x_555_;
}
else
{
lean_object* v___x_557_; 
lean_dec(v_fst_548_);
lean_dec(v_fst_538_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v_e_490_);
v___x_557_ = v___x_551_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_e_490_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_snd_549_);
v___x_557_ = v_reuseFailAlloc_561_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_557_);
v___x_559_ = v___x_546_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_a_544_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_538_);
lean_dec_ref_known(v_e_490_, 3);
return v___x_542_;
}
}
else
{
lean_dec_ref_known(v_e_490_, 3);
lean_dec(v_offset_491_);
return v___x_535_;
}
}
case 7:
{
lean_object* v_binderName_570_; lean_object* v_binderType_571_; lean_object* v_body_572_; uint8_t v_binderInfo_573_; lean_object* v___x_574_; 
v_binderName_570_ = lean_ctor_get(v_e_490_, 0);
v_binderType_571_ = lean_ctor_get(v_e_490_, 1);
v_body_572_ = lean_ctor_get(v_e_490_, 2);
v_binderInfo_573_ = lean_ctor_get_uint8(v_e_490_, sizeof(void*)*3 + 8);
lean_inc(v_offset_491_);
lean_inc_ref(v_binderType_571_);
v___x_574_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_488_, v_d_489_, v_binderType_571_, v_offset_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v_a_576_; lean_object* v_fst_577_; lean_object* v_snd_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
v_a_576_ = lean_ctor_get(v___x_574_, 1);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_574_, 2);
v_fst_577_ = lean_ctor_get(v_a_575_, 0);
lean_inc(v_fst_577_);
v_snd_578_ = lean_ctor_get(v_a_575_, 1);
lean_inc(v_snd_578_);
lean_dec(v_a_575_);
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = lean_nat_add(v_offset_491_, v___x_579_);
lean_dec(v_offset_491_);
lean_inc_ref(v_body_572_);
v___x_581_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_488_, v_d_489_, v_body_572_, v___x_580_, v_snd_578_, v_a_493_, v_a_494_, v_a_576_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_608_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_a_583_ = lean_ctor_get(v___x_581_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_608_ == 0)
{
v___x_585_ = v___x_581_;
v_isShared_586_ = v_isSharedCheck_608_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_608_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v_fst_587_; lean_object* v_snd_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_607_; 
v_fst_587_ = lean_ctor_get(v_a_582_, 0);
v_snd_588_ = lean_ctor_get(v_a_582_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v_a_582_);
if (v_isSharedCheck_607_ == 0)
{
v___x_590_ = v_a_582_;
v_isShared_591_ = v_isSharedCheck_607_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_snd_588_);
lean_inc(v_fst_587_);
lean_dec(v_a_582_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_607_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
uint8_t v___y_593_; size_t v___x_601_; size_t v___x_602_; uint8_t v___x_603_; 
v___x_601_ = lean_ptr_addr(v_binderType_571_);
v___x_602_ = lean_ptr_addr(v_fst_577_);
v___x_603_ = lean_usize_dec_eq(v___x_601_, v___x_602_);
if (v___x_603_ == 0)
{
v___y_593_ = v___x_603_;
goto v___jp_592_;
}
else
{
size_t v___x_604_; size_t v___x_605_; uint8_t v___x_606_; 
v___x_604_ = lean_ptr_addr(v_body_572_);
v___x_605_ = lean_ptr_addr(v_fst_587_);
v___x_606_ = lean_usize_dec_eq(v___x_604_, v___x_605_);
v___y_593_ = v___x_606_;
goto v___jp_592_;
}
v___jp_592_:
{
if (v___y_593_ == 0)
{
lean_object* v___x_594_; 
lean_inc(v_binderName_570_);
lean_del_object(v___x_590_);
lean_del_object(v___x_585_);
lean_dec_ref_known(v_e_490_, 3);
v___x_594_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_570_, v_binderInfo_573_, v_fst_577_, v_fst_587_, v_snd_588_, v_a_493_, v_a_494_, v_a_583_);
return v___x_594_;
}
else
{
lean_object* v___x_596_; 
lean_dec(v_fst_587_);
lean_dec(v_fst_577_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v_e_490_);
v___x_596_ = v___x_590_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_e_490_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_snd_588_);
v___x_596_ = v_reuseFailAlloc_600_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_598_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_596_);
v___x_598_ = v___x_585_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_a_583_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_577_);
lean_dec_ref_known(v_e_490_, 3);
return v___x_581_;
}
}
else
{
lean_dec_ref_known(v_e_490_, 3);
lean_dec(v_offset_491_);
return v___x_574_;
}
}
case 8:
{
lean_object* v_declName_609_; lean_object* v_type_610_; lean_object* v_value_611_; lean_object* v_body_612_; uint8_t v_nondep_613_; lean_object* v___x_614_; 
v_declName_609_ = lean_ctor_get(v_e_490_, 0);
v_type_610_ = lean_ctor_get(v_e_490_, 1);
v_value_611_ = lean_ctor_get(v_e_490_, 2);
v_body_612_ = lean_ctor_get(v_e_490_, 3);
v_nondep_613_ = lean_ctor_get_uint8(v_e_490_, sizeof(void*)*4 + 8);
lean_inc(v_offset_491_);
lean_inc_ref(v_type_610_);
v___x_614_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_488_, v_d_489_, v_type_610_, v_offset_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v_a_616_; lean_object* v_fst_617_; lean_object* v_snd_618_; lean_object* v___x_619_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
v_a_616_ = lean_ctor_get(v___x_614_, 1);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_614_, 2);
v_fst_617_ = lean_ctor_get(v_a_615_, 0);
lean_inc(v_fst_617_);
v_snd_618_ = lean_ctor_get(v_a_615_, 1);
lean_inc(v_snd_618_);
lean_dec(v_a_615_);
lean_inc(v_offset_491_);
lean_inc_ref(v_value_611_);
v___x_619_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_488_, v_d_489_, v_value_611_, v_offset_491_, v_snd_618_, v_a_493_, v_a_494_, v_a_616_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v_a_621_; lean_object* v_fst_622_; lean_object* v_snd_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
v_a_621_ = lean_ctor_get(v___x_619_, 1);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_619_, 2);
v_fst_622_ = lean_ctor_get(v_a_620_, 0);
lean_inc(v_fst_622_);
v_snd_623_ = lean_ctor_get(v_a_620_, 1);
lean_inc(v_snd_623_);
lean_dec(v_a_620_);
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_nat_add(v_offset_491_, v___x_624_);
lean_dec(v_offset_491_);
lean_inc_ref(v_body_612_);
v___x_626_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_488_, v_d_489_, v_body_612_, v___x_625_, v_snd_623_, v_a_493_, v_a_494_, v_a_621_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_657_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_a_628_ = lean_ctor_get(v___x_626_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_657_ == 0)
{
v___x_630_ = v___x_626_;
v_isShared_631_ = v_isSharedCheck_657_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_657_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_fst_632_; lean_object* v_snd_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_656_; 
v_fst_632_ = lean_ctor_get(v_a_627_, 0);
v_snd_633_ = lean_ctor_get(v_a_627_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_a_627_);
if (v_isSharedCheck_656_ == 0)
{
v___x_635_ = v_a_627_;
v_isShared_636_ = v_isSharedCheck_656_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_snd_633_);
lean_inc(v_fst_632_);
lean_dec(v_a_627_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_656_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
uint8_t v___y_638_; size_t v___x_650_; size_t v___x_651_; uint8_t v___x_652_; 
v___x_650_ = lean_ptr_addr(v_type_610_);
v___x_651_ = lean_ptr_addr(v_fst_617_);
v___x_652_ = lean_usize_dec_eq(v___x_650_, v___x_651_);
if (v___x_652_ == 0)
{
v___y_638_ = v___x_652_;
goto v___jp_637_;
}
else
{
size_t v___x_653_; size_t v___x_654_; uint8_t v___x_655_; 
v___x_653_ = lean_ptr_addr(v_value_611_);
v___x_654_ = lean_ptr_addr(v_fst_622_);
v___x_655_ = lean_usize_dec_eq(v___x_653_, v___x_654_);
v___y_638_ = v___x_655_;
goto v___jp_637_;
}
v___jp_637_:
{
if (v___y_638_ == 0)
{
lean_object* v___x_639_; 
lean_inc(v_declName_609_);
lean_del_object(v___x_635_);
lean_del_object(v___x_630_);
lean_dec_ref_known(v_e_490_, 4);
v___x_639_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_609_, v_fst_617_, v_fst_622_, v_fst_632_, v_nondep_613_, v_snd_633_, v_a_493_, v_a_494_, v_a_628_);
return v___x_639_;
}
else
{
size_t v___x_640_; size_t v___x_641_; uint8_t v___x_642_; 
v___x_640_ = lean_ptr_addr(v_body_612_);
v___x_641_ = lean_ptr_addr(v_fst_632_);
v___x_642_ = lean_usize_dec_eq(v___x_640_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
lean_inc(v_declName_609_);
lean_del_object(v___x_635_);
lean_del_object(v___x_630_);
lean_dec_ref_known(v_e_490_, 4);
v___x_643_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_609_, v_fst_617_, v_fst_622_, v_fst_632_, v_nondep_613_, v_snd_633_, v_a_493_, v_a_494_, v_a_628_);
return v___x_643_;
}
else
{
lean_object* v___x_645_; 
lean_dec(v_fst_632_);
lean_dec(v_fst_622_);
lean_dec(v_fst_617_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v_e_490_);
v___x_645_ = v___x_635_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_e_490_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_snd_633_);
v___x_645_ = v_reuseFailAlloc_649_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_647_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_645_);
v___x_647_ = v___x_630_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_a_628_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
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
lean_dec(v_fst_622_);
lean_dec(v_fst_617_);
lean_dec_ref_known(v_e_490_, 4);
return v___x_626_;
}
}
else
{
lean_dec(v_fst_617_);
lean_dec_ref_known(v_e_490_, 4);
lean_dec(v_offset_491_);
return v___x_619_;
}
}
else
{
lean_dec_ref_known(v_e_490_, 4);
lean_dec(v_offset_491_);
return v___x_614_;
}
}
case 10:
{
lean_object* v_data_658_; lean_object* v_expr_659_; lean_object* v___x_660_; 
v_data_658_ = lean_ctor_get(v_e_490_, 0);
v_expr_659_ = lean_ctor_get(v_e_490_, 1);
lean_inc_ref(v_expr_659_);
v___x_660_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_488_, v_d_489_, v_expr_659_, v_offset_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_682_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_a_662_ = lean_ctor_get(v___x_660_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_682_ == 0)
{
v___x_664_ = v___x_660_;
v_isShared_665_ = v_isSharedCheck_682_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_682_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v_fst_666_; lean_object* v_snd_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_681_; 
v_fst_666_ = lean_ctor_get(v_a_661_, 0);
v_snd_667_ = lean_ctor_get(v_a_661_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_a_661_);
if (v_isSharedCheck_681_ == 0)
{
v___x_669_ = v_a_661_;
v_isShared_670_ = v_isSharedCheck_681_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_snd_667_);
lean_inc(v_fst_666_);
lean_dec(v_a_661_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_681_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
size_t v___x_671_; size_t v___x_672_; uint8_t v___x_673_; 
v___x_671_ = lean_ptr_addr(v_expr_659_);
v___x_672_ = lean_ptr_addr(v_fst_666_);
v___x_673_ = lean_usize_dec_eq(v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
lean_inc(v_data_658_);
lean_del_object(v___x_669_);
lean_del_object(v___x_664_);
lean_dec_ref_known(v_e_490_, 2);
v___x_674_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_658_, v_fst_666_, v_snd_667_, v_a_493_, v_a_494_, v_a_662_);
return v___x_674_;
}
else
{
lean_object* v___x_676_; 
lean_dec(v_fst_666_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v_e_490_);
v___x_676_ = v___x_669_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_e_490_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_snd_667_);
v___x_676_ = v_reuseFailAlloc_680_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_678_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_676_);
v___x_678_ = v___x_664_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_a_662_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_490_, 2);
return v___x_660_;
}
}
case 11:
{
lean_object* v_typeName_683_; lean_object* v_idx_684_; lean_object* v_struct_685_; lean_object* v___x_686_; 
v_typeName_683_ = lean_ctor_get(v_e_490_, 0);
v_idx_684_ = lean_ctor_get(v_e_490_, 1);
v_struct_685_ = lean_ctor_get(v_e_490_, 2);
lean_inc_ref(v_struct_685_);
v___x_686_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_488_, v_d_489_, v_struct_685_, v_offset_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_708_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
v_a_688_ = lean_ctor_get(v___x_686_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_708_ == 0)
{
v___x_690_ = v___x_686_;
v_isShared_691_ = v_isSharedCheck_708_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_inc(v_a_687_);
lean_dec(v___x_686_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_708_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_fst_692_; lean_object* v_snd_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_707_; 
v_fst_692_ = lean_ctor_get(v_a_687_, 0);
v_snd_693_ = lean_ctor_get(v_a_687_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_a_687_);
if (v_isSharedCheck_707_ == 0)
{
v___x_695_ = v_a_687_;
v_isShared_696_ = v_isSharedCheck_707_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_snd_693_);
lean_inc(v_fst_692_);
lean_dec(v_a_687_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_707_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
size_t v___x_697_; size_t v___x_698_; uint8_t v___x_699_; 
v___x_697_ = lean_ptr_addr(v_struct_685_);
v___x_698_ = lean_ptr_addr(v_fst_692_);
v___x_699_ = lean_usize_dec_eq(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
lean_inc(v_idx_684_);
lean_inc(v_typeName_683_);
lean_del_object(v___x_695_);
lean_del_object(v___x_690_);
lean_dec_ref_known(v_e_490_, 3);
v___x_700_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_683_, v_idx_684_, v_fst_692_, v_snd_693_, v_a_493_, v_a_494_, v_a_688_);
return v___x_700_;
}
else
{
lean_object* v___x_702_; 
lean_dec(v_fst_692_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v_e_490_);
v___x_702_ = v___x_695_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_e_490_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_snd_693_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_702_);
v___x_704_ = v___x_690_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_a_688_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_490_, 3);
return v___x_686_;
}
}
default: 
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec(v_offset_491_);
lean_dec_ref(v_e_490_);
v___x_709_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
v___x_710_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_709_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
return v___x_710_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(lean_object* v_s_711_, lean_object* v_d_712_, lean_object* v_e_713_, lean_object* v_offset_714_, lean_object* v_a_715_, uint8_t v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_key_719_; lean_object* v_a_721_; lean_object* v___x_734_; 
lean_inc(v_offset_714_);
lean_inc_ref(v_e_713_);
v_key_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_719_, 0, v_e_713_);
lean_ctor_set(v_key_719_, 1, v_offset_714_);
v___x_734_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_715_, v_key_719_);
if (lean_obj_tag(v___x_734_) == 1)
{
lean_object* v_val_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec_ref_known(v_key_719_, 2);
lean_dec(v_offset_714_);
lean_dec_ref(v_e_713_);
v_val_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_val_735_);
lean_dec_ref_known(v___x_734_, 1);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v_val_735_);
lean_ctor_set(v___x_736_, 1, v_a_715_);
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v_a_718_);
return v___x_737_;
}
else
{
lean_object* v_s_u2081_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
lean_dec(v___x_734_);
v_s_u2081_738_ = lean_nat_add(v_s_711_, v_offset_714_);
v___x_739_ = l_Lean_Expr_looseBVarRange(v_e_713_);
v___x_740_ = lean_nat_dec_le(v___x_739_, v_s_u2081_738_);
lean_dec(v___x_739_);
if (v___x_740_ == 0)
{
if (lean_obj_tag(v_e_713_) == 0)
{
lean_object* v_deBruijnIndex_741_; uint8_t v___x_742_; 
v_deBruijnIndex_741_ = lean_ctor_get(v_e_713_, 0);
v___x_742_ = lean_nat_dec_le(v_s_u2081_738_, v_deBruijnIndex_741_);
lean_dec(v_s_u2081_738_);
if (v___x_742_ == 0)
{
v_a_721_ = v_a_718_;
goto v___jp_720_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; 
lean_inc(v_deBruijnIndex_741_);
lean_dec_ref_known(v_e_713_, 1);
lean_dec(v_offset_714_);
v___x_743_ = lean_nat_sub(v_deBruijnIndex_741_, v_d_712_);
lean_dec(v_deBruijnIndex_741_);
v___x_744_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_743_, v_a_718_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v_a_746_; lean_object* v___x_747_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
v_a_746_ = lean_ctor_get(v___x_744_, 1);
lean_inc(v_a_746_);
lean_dec_ref_known(v___x_744_, 2);
v___x_747_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_719_, v_a_745_, v_a_715_, v_a_716_, v_a_717_, v_a_746_);
return v___x_747_;
}
else
{
lean_object* v_a_748_; lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec_ref_known(v_key_719_, 2);
lean_dec_ref(v_a_715_);
v_a_748_ = lean_ctor_get(v___x_744_, 0);
v_a_749_ = lean_ctor_get(v___x_744_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_744_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_inc(v_a_748_);
lean_dec(v___x_744_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_748_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
else
{
lean_dec(v_s_u2081_738_);
v_a_721_ = v_a_718_;
goto v___jp_720_;
}
}
else
{
lean_object* v___x_757_; 
lean_dec(v_s_u2081_738_);
lean_dec(v_offset_714_);
v___x_757_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_719_, v_e_713_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
return v___x_757_;
}
}
v___jp_720_:
{
switch(lean_obj_tag(v_e_713_))
{
case 9:
{
lean_object* v___x_722_; 
lean_dec(v_offset_714_);
v___x_722_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_719_, v_e_713_, v_a_715_, v_a_716_, v_a_717_, v_a_721_);
return v___x_722_;
}
case 2:
{
lean_object* v___x_723_; 
lean_dec(v_offset_714_);
v___x_723_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_719_, v_e_713_, v_a_715_, v_a_716_, v_a_717_, v_a_721_);
return v___x_723_;
}
case 0:
{
lean_object* v___x_724_; 
lean_dec(v_offset_714_);
v___x_724_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_719_, v_e_713_, v_a_715_, v_a_716_, v_a_717_, v_a_721_);
return v___x_724_;
}
case 1:
{
lean_object* v___x_725_; 
lean_dec(v_offset_714_);
v___x_725_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_719_, v_e_713_, v_a_715_, v_a_716_, v_a_717_, v_a_721_);
return v___x_725_;
}
case 4:
{
lean_object* v___x_726_; 
lean_dec(v_offset_714_);
v___x_726_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_719_, v_e_713_, v_a_715_, v_a_716_, v_a_717_, v_a_721_);
return v___x_726_;
}
case 3:
{
lean_object* v___x_727_; 
lean_dec(v_offset_714_);
v___x_727_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_719_, v_e_713_, v_a_715_, v_a_716_, v_a_717_, v_a_721_);
return v___x_727_;
}
default: 
{
lean_object* v___x_728_; 
v___x_728_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_711_, v_d_712_, v_e_713_, v_offset_714_, v_a_715_, v_a_716_, v_a_717_, v_a_721_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v_a_730_; lean_object* v_fst_731_; lean_object* v_snd_732_; lean_object* v___x_733_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
v_a_730_ = lean_ctor_get(v___x_728_, 1);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_728_, 2);
v_fst_731_ = lean_ctor_get(v_a_729_, 0);
lean_inc(v_fst_731_);
v_snd_732_ = lean_ctor_get(v_a_729_, 1);
lean_inc(v_snd_732_);
lean_dec(v_a_729_);
v___x_733_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_719_, v_fst_731_, v_snd_732_, v_a_716_, v_a_717_, v_a_730_);
return v___x_733_;
}
else
{
lean_dec_ref_known(v_key_719_, 2);
return v___x_728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1___boxed(lean_object* v_s_758_, lean_object* v_d_759_, lean_object* v_e_760_, lean_object* v_offset_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
uint8_t v_a_boxed_766_; lean_object* v_res_767_; 
v_a_boxed_766_ = lean_unbox(v_a_763_);
v_res_767_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_758_, v_d_759_, v_e_760_, v_offset_761_, v_a_762_, v_a_boxed_766_, v_a_764_, v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_d_759_);
lean_dec(v_s_758_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___boxed(lean_object* v_s_768_, lean_object* v_d_769_, lean_object* v_e_770_, lean_object* v_offset_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
uint8_t v_a_boxed_776_; lean_object* v_res_777_; 
v_a_boxed_776_ = lean_unbox(v_a_773_);
v_res_777_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_768_, v_d_769_, v_e_770_, v_offset_771_, v_a_772_, v_a_boxed_776_, v_a_774_, v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_d_769_);
lean_dec(v_s_768_);
return v_res_777_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_778_ = lean_box(0);
v___x_779_ = lean_unsigned_to_nat(16u);
v___x_780_ = lean_mk_array(v___x_779_, v___x_778_);
return v___x_780_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0);
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v___x_781_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27(lean_object* v_e_784_, lean_object* v_s_785_, lean_object* v_d_786_, uint8_t v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_790_ = l_Lean_Expr_looseBVarRange(v_e_784_);
v___x_791_ = lean_nat_dec_le(v___x_790_, v_s_785_);
lean_dec(v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v_a_794_; 
v___x_792_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_e_784_) == 0)
{
lean_object* v_deBruijnIndex_822_; uint8_t v___x_823_; 
v_deBruijnIndex_822_ = lean_ctor_get(v_e_784_, 0);
v___x_823_ = lean_nat_dec_le(v_s_785_, v_deBruijnIndex_822_);
if (v___x_823_ == 0)
{
v_a_794_ = v_a_789_;
goto v___jp_793_;
}
else
{
lean_object* v___x_824_; lean_object* v___x_825_; 
lean_inc(v_deBruijnIndex_822_);
lean_dec_ref_known(v_e_784_, 1);
v___x_824_ = lean_nat_sub(v_deBruijnIndex_822_, v_d_786_);
lean_dec(v_deBruijnIndex_822_);
v___x_825_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_824_, v_a_789_);
return v___x_825_;
}
}
else
{
v_a_794_ = v_a_789_;
goto v___jp_793_;
}
v___jp_793_:
{
switch(lean_obj_tag(v_e_784_))
{
case 9:
{
lean_object* v___x_795_; 
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v_e_784_);
lean_ctor_set(v___x_795_, 1, v_a_794_);
return v___x_795_;
}
case 2:
{
lean_object* v___x_796_; 
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v_e_784_);
lean_ctor_set(v___x_796_, 1, v_a_794_);
return v___x_796_;
}
case 0:
{
lean_object* v___x_797_; 
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_e_784_);
lean_ctor_set(v___x_797_, 1, v_a_794_);
return v___x_797_;
}
case 1:
{
lean_object* v___x_798_; 
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v_e_784_);
lean_ctor_set(v___x_798_, 1, v_a_794_);
return v___x_798_;
}
case 4:
{
lean_object* v___x_799_; 
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v_e_784_);
lean_ctor_set(v___x_799_, 1, v_a_794_);
return v___x_799_;
}
case 3:
{
lean_object* v___x_800_; 
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_e_784_);
lean_ctor_set(v___x_800_, 1, v_a_794_);
return v___x_800_;
}
default: 
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1);
v___x_802_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_785_, v_d_786_, v_e_784_, v___x_792_, v___x_801_, v_a_787_, v_a_788_, v_a_794_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_812_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_a_804_ = lean_ctor_get(v___x_802_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_812_ == 0)
{
v___x_806_ = v___x_802_;
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v_fst_808_; lean_object* v___x_810_; 
v_fst_808_ = lean_ctor_get(v_a_803_, 0);
lean_inc(v_fst_808_);
lean_dec(v_a_803_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v_fst_808_);
v___x_810_ = v___x_806_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_fst_808_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_a_804_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
else
{
lean_object* v_a_813_; lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
v_a_813_ = lean_ctor_get(v___x_802_, 0);
v_a_814_ = lean_ctor_get(v___x_802_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_802_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_inc(v_a_813_);
lean_dec(v___x_802_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_813_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_826_; 
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v_e_784_);
lean_ctor_set(v___x_826_, 1, v_a_789_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed(lean_object* v_e_827_, lean_object* v_s_828_, lean_object* v_d_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
uint8_t v_a_boxed_833_; lean_object* v_res_834_; 
v_a_boxed_833_ = lean_unbox(v_a_830_);
v_res_834_ = l_Lean_Meta_Sym_lowerLooseBVarsS_x27(v_e_827_, v_s_828_, v_d_829_, v_a_boxed_833_, v_a_831_, v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_d_829_);
lean_dec(v_s_828_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_835_, lean_object* v_m_836_, lean_object* v_a_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_836_, v_a_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_839_, lean_object* v_m_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(v_00_u03b2_839_, v_m_840_, v_a_841_);
lean_dec_ref(v_a_841_);
lean_dec_ref(v_m_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(lean_object* v_00_u03b2_843_, lean_object* v_a_844_, lean_object* v_x_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_844_, v_x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___boxed(lean_object* v_00_u03b2_847_, lean_object* v_a_848_, lean_object* v_x_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(v_00_u03b2_847_, v_a_848_, v_x_849_);
lean_dec(v_x_849_);
lean_dec_ref(v_a_848_);
return v_res_850_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0(void){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(lean_object* v_msg_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_44__overap_861_; lean_object* v___x_862_; 
v___x_860_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0);
v___x_44__overap_861_ = lean_panic_fn_borrowed(v___x_860_, v_msg_852_);
lean_inc(v___y_858_);
lean_inc_ref(v___y_857_);
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
lean_inc(v___y_854_);
lean_inc_ref(v___y_853_);
v___x_862_ = lean_apply_7(v___x_44__overap_861_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, lean_box(0));
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___boxed(lean_object* v_msg_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(v_msg_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
return v_res_871_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_874_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2));
v___x_875_ = lean_unsigned_to_nat(16u);
v___x_876_ = lean_unsigned_to_nat(62u);
v___x_877_ = ((lean_object*)(l_Lean_Meta_Sym_lowerLooseBVarsS___closed__1));
v___x_878_ = ((lean_object*)(l_Lean_Meta_Sym_lowerLooseBVarsS___closed__0));
v___x_879_ = l_mkPanicMessageWithDecl(v___x_878_, v___x_877_, v___x_876_, v___x_875_, v___x_874_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS(lean_object* v_e_880_, lean_object* v_s_881_, lean_object* v_d_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v_debug_892_; lean_object* v_env_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_890_ = lean_st_ref_get(v_a_884_);
v___x_891_ = lean_st_ref_get(v_a_888_);
v_debug_892_ = lean_ctor_get_uint8(v___x_890_, sizeof(void*)*11);
lean_dec(v___x_890_);
v_env_893_ = lean_ctor_get(v___x_891_, 0);
lean_inc_ref(v_env_893_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(v_debug_892_);
v___x_895_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed), 6, 4);
lean_closure_set(v___x_895_, 0, v_e_880_);
lean_closure_set(v___x_895_, 1, v_s_881_);
lean_closure_set(v___x_895_, 2, v_d_882_);
lean_closure_set(v___x_895_, 3, v___x_894_);
v___x_896_ = 0;
v___x_897_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_897_, 0, v_env_893_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*1, v___x_896_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*1 + 1, v___x_896_);
v___x_898_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_895_, v___x_897_, v_a_884_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_909_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_909_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_909_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_909_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
if (lean_obj_tag(v_a_899_) == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
lean_dec_ref_known(v_a_899_, 1);
lean_del_object(v___x_901_);
v___x_903_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2, &l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2);
v___x_904_ = l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(v___x_903_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
return v___x_904_;
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; 
v_a_905_ = lean_ctor_get(v_a_899_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v_a_899_, 1);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v_a_905_);
v___x_907_ = v___x_901_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
v_a_910_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_898_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_898_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___boxed(lean_object* v_e_918_, lean_object* v_s_919_, lean_object* v_d_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Meta_Sym_lowerLooseBVarsS(v_e_918_, v_s_919_, v_d_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(lean_object* v_s_929_, lean_object* v_d_930_, lean_object* v_e_931_, lean_object* v_offset_932_, lean_object* v_a_933_, uint8_t v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
switch(lean_obj_tag(v_e_931_))
{
case 5:
{
lean_object* v_fn_937_; lean_object* v_arg_938_; lean_object* v___x_939_; 
v_fn_937_ = lean_ctor_get(v_e_931_, 0);
v_arg_938_ = lean_ctor_get(v_e_931_, 1);
lean_inc(v_offset_932_);
lean_inc_ref(v_fn_937_);
v___x_939_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_929_, v_d_930_, v_fn_937_, v_offset_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v_a_941_; lean_object* v_fst_942_; lean_object* v_snd_943_; lean_object* v___x_944_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_a_940_);
v_a_941_ = lean_ctor_get(v___x_939_, 1);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_939_, 2);
v_fst_942_ = lean_ctor_get(v_a_940_, 0);
lean_inc(v_fst_942_);
v_snd_943_ = lean_ctor_get(v_a_940_, 1);
lean_inc(v_snd_943_);
lean_dec(v_a_940_);
lean_inc_ref(v_arg_938_);
v___x_944_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_929_, v_d_930_, v_arg_938_, v_offset_932_, v_snd_943_, v_a_934_, v_a_935_, v_a_941_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_971_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_a_946_ = lean_ctor_get(v___x_944_, 1);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_971_ == 0)
{
v___x_948_ = v___x_944_;
v_isShared_949_ = v_isSharedCheck_971_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_971_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_fst_950_; lean_object* v_snd_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_970_; 
v_fst_950_ = lean_ctor_get(v_a_945_, 0);
v_snd_951_ = lean_ctor_get(v_a_945_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v_a_945_);
if (v_isSharedCheck_970_ == 0)
{
v___x_953_ = v_a_945_;
v_isShared_954_ = v_isSharedCheck_970_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_snd_951_);
lean_inc(v_fst_950_);
lean_dec(v_a_945_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_970_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
uint8_t v___y_956_; size_t v___x_964_; size_t v___x_965_; uint8_t v___x_966_; 
v___x_964_ = lean_ptr_addr(v_fn_937_);
v___x_965_ = lean_ptr_addr(v_fst_942_);
v___x_966_ = lean_usize_dec_eq(v___x_964_, v___x_965_);
if (v___x_966_ == 0)
{
v___y_956_ = v___x_966_;
goto v___jp_955_;
}
else
{
size_t v___x_967_; size_t v___x_968_; uint8_t v___x_969_; 
v___x_967_ = lean_ptr_addr(v_arg_938_);
v___x_968_ = lean_ptr_addr(v_fst_950_);
v___x_969_ = lean_usize_dec_eq(v___x_967_, v___x_968_);
v___y_956_ = v___x_969_;
goto v___jp_955_;
}
v___jp_955_:
{
if (v___y_956_ == 0)
{
lean_object* v___x_957_; 
lean_del_object(v___x_953_);
lean_del_object(v___x_948_);
lean_dec_ref_known(v_e_931_, 2);
v___x_957_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_942_, v_fst_950_, v_snd_951_, v_a_934_, v_a_935_, v_a_946_);
return v___x_957_;
}
else
{
lean_object* v___x_959_; 
lean_dec(v_fst_950_);
lean_dec(v_fst_942_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v_e_931_);
v___x_959_ = v___x_953_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_e_931_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_snd_951_);
v___x_959_ = v_reuseFailAlloc_963_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_961_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_959_);
v___x_961_ = v___x_948_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_a_946_);
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
lean_dec(v_fst_942_);
lean_dec_ref_known(v_e_931_, 2);
return v___x_944_;
}
}
else
{
lean_dec_ref_known(v_e_931_, 2);
lean_dec(v_offset_932_);
return v___x_939_;
}
}
case 6:
{
lean_object* v_binderName_972_; lean_object* v_binderType_973_; lean_object* v_body_974_; uint8_t v_binderInfo_975_; lean_object* v___x_976_; 
v_binderName_972_ = lean_ctor_get(v_e_931_, 0);
v_binderType_973_ = lean_ctor_get(v_e_931_, 1);
v_body_974_ = lean_ctor_get(v_e_931_, 2);
v_binderInfo_975_ = lean_ctor_get_uint8(v_e_931_, sizeof(void*)*3 + 8);
lean_inc(v_offset_932_);
lean_inc_ref(v_binderType_973_);
v___x_976_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_929_, v_d_930_, v_binderType_973_, v_offset_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v_a_978_; lean_object* v_fst_979_; lean_object* v_snd_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
v_a_978_ = lean_ctor_get(v___x_976_, 1);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_976_, 2);
v_fst_979_ = lean_ctor_get(v_a_977_, 0);
lean_inc(v_fst_979_);
v_snd_980_ = lean_ctor_get(v_a_977_, 1);
lean_inc(v_snd_980_);
lean_dec(v_a_977_);
v___x_981_ = lean_unsigned_to_nat(1u);
v___x_982_ = lean_nat_add(v_offset_932_, v___x_981_);
lean_dec(v_offset_932_);
lean_inc_ref(v_body_974_);
v___x_983_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_929_, v_d_930_, v_body_974_, v___x_982_, v_snd_980_, v_a_934_, v_a_935_, v_a_978_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1010_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
v_a_985_ = lean_ctor_get(v___x_983_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_987_ = v___x_983_;
v_isShared_988_ = v_isSharedCheck_1010_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1010_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v_fst_989_; lean_object* v_snd_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1009_; 
v_fst_989_ = lean_ctor_get(v_a_984_, 0);
v_snd_990_ = lean_ctor_get(v_a_984_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_a_984_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_992_ = v_a_984_;
v_isShared_993_ = v_isSharedCheck_1009_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_snd_990_);
lean_inc(v_fst_989_);
lean_dec(v_a_984_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1009_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
uint8_t v___y_995_; size_t v___x_1003_; size_t v___x_1004_; uint8_t v___x_1005_; 
v___x_1003_ = lean_ptr_addr(v_binderType_973_);
v___x_1004_ = lean_ptr_addr(v_fst_979_);
v___x_1005_ = lean_usize_dec_eq(v___x_1003_, v___x_1004_);
if (v___x_1005_ == 0)
{
v___y_995_ = v___x_1005_;
goto v___jp_994_;
}
else
{
size_t v___x_1006_; size_t v___x_1007_; uint8_t v___x_1008_; 
v___x_1006_ = lean_ptr_addr(v_body_974_);
v___x_1007_ = lean_ptr_addr(v_fst_989_);
v___x_1008_ = lean_usize_dec_eq(v___x_1006_, v___x_1007_);
v___y_995_ = v___x_1008_;
goto v___jp_994_;
}
v___jp_994_:
{
if (v___y_995_ == 0)
{
lean_object* v___x_996_; 
lean_inc(v_binderName_972_);
lean_del_object(v___x_992_);
lean_del_object(v___x_987_);
lean_dec_ref_known(v_e_931_, 3);
v___x_996_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_972_, v_binderInfo_975_, v_fst_979_, v_fst_989_, v_snd_990_, v_a_934_, v_a_935_, v_a_985_);
return v___x_996_;
}
else
{
lean_object* v___x_998_; 
lean_dec(v_fst_989_);
lean_dec(v_fst_979_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v_e_931_);
v___x_998_ = v___x_992_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_e_931_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_snd_990_);
v___x_998_ = v_reuseFailAlloc_1002_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_1000_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_998_);
v___x_1000_ = v___x_987_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_a_985_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_979_);
lean_dec_ref_known(v_e_931_, 3);
return v___x_983_;
}
}
else
{
lean_dec_ref_known(v_e_931_, 3);
lean_dec(v_offset_932_);
return v___x_976_;
}
}
case 7:
{
lean_object* v_binderName_1011_; lean_object* v_binderType_1012_; lean_object* v_body_1013_; uint8_t v_binderInfo_1014_; lean_object* v___x_1015_; 
v_binderName_1011_ = lean_ctor_get(v_e_931_, 0);
v_binderType_1012_ = lean_ctor_get(v_e_931_, 1);
v_body_1013_ = lean_ctor_get(v_e_931_, 2);
v_binderInfo_1014_ = lean_ctor_get_uint8(v_e_931_, sizeof(void*)*3 + 8);
lean_inc(v_offset_932_);
lean_inc_ref(v_binderType_1012_);
v___x_1015_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_929_, v_d_930_, v_binderType_1012_, v_offset_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v_a_1017_; lean_object* v_fst_1018_; lean_object* v_snd_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
v_a_1017_ = lean_ctor_get(v___x_1015_, 1);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1015_, 2);
v_fst_1018_ = lean_ctor_get(v_a_1016_, 0);
lean_inc(v_fst_1018_);
v_snd_1019_ = lean_ctor_get(v_a_1016_, 1);
lean_inc(v_snd_1019_);
lean_dec(v_a_1016_);
v___x_1020_ = lean_unsigned_to_nat(1u);
v___x_1021_ = lean_nat_add(v_offset_932_, v___x_1020_);
lean_dec(v_offset_932_);
lean_inc_ref(v_body_1013_);
v___x_1022_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_929_, v_d_930_, v_body_1013_, v___x_1021_, v_snd_1019_, v_a_934_, v_a_935_, v_a_1017_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1049_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_a_1024_ = lean_ctor_get(v___x_1022_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1026_ = v___x_1022_;
v_isShared_1027_ = v_isSharedCheck_1049_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1049_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v_fst_1028_; lean_object* v_snd_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1048_; 
v_fst_1028_ = lean_ctor_get(v_a_1023_, 0);
v_snd_1029_ = lean_ctor_get(v_a_1023_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_a_1023_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1031_ = v_a_1023_;
v_isShared_1032_ = v_isSharedCheck_1048_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_snd_1029_);
lean_inc(v_fst_1028_);
lean_dec(v_a_1023_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1048_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
uint8_t v___y_1034_; size_t v___x_1042_; size_t v___x_1043_; uint8_t v___x_1044_; 
v___x_1042_ = lean_ptr_addr(v_binderType_1012_);
v___x_1043_ = lean_ptr_addr(v_fst_1018_);
v___x_1044_ = lean_usize_dec_eq(v___x_1042_, v___x_1043_);
if (v___x_1044_ == 0)
{
v___y_1034_ = v___x_1044_;
goto v___jp_1033_;
}
else
{
size_t v___x_1045_; size_t v___x_1046_; uint8_t v___x_1047_; 
v___x_1045_ = lean_ptr_addr(v_body_1013_);
v___x_1046_ = lean_ptr_addr(v_fst_1028_);
v___x_1047_ = lean_usize_dec_eq(v___x_1045_, v___x_1046_);
v___y_1034_ = v___x_1047_;
goto v___jp_1033_;
}
v___jp_1033_:
{
if (v___y_1034_ == 0)
{
lean_object* v___x_1035_; 
lean_inc(v_binderName_1011_);
lean_del_object(v___x_1031_);
lean_del_object(v___x_1026_);
lean_dec_ref_known(v_e_931_, 3);
v___x_1035_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_1011_, v_binderInfo_1014_, v_fst_1018_, v_fst_1028_, v_snd_1029_, v_a_934_, v_a_935_, v_a_1024_);
return v___x_1035_;
}
else
{
lean_object* v___x_1037_; 
lean_dec(v_fst_1028_);
lean_dec(v_fst_1018_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v_e_931_);
v___x_1037_ = v___x_1031_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_e_931_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_snd_1029_);
v___x_1037_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1039_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1037_);
v___x_1039_ = v___x_1026_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_a_1024_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1018_);
lean_dec_ref_known(v_e_931_, 3);
return v___x_1022_;
}
}
else
{
lean_dec_ref_known(v_e_931_, 3);
lean_dec(v_offset_932_);
return v___x_1015_;
}
}
case 8:
{
lean_object* v_declName_1050_; lean_object* v_type_1051_; lean_object* v_value_1052_; lean_object* v_body_1053_; uint8_t v_nondep_1054_; lean_object* v___x_1055_; 
v_declName_1050_ = lean_ctor_get(v_e_931_, 0);
v_type_1051_ = lean_ctor_get(v_e_931_, 1);
v_value_1052_ = lean_ctor_get(v_e_931_, 2);
v_body_1053_ = lean_ctor_get(v_e_931_, 3);
v_nondep_1054_ = lean_ctor_get_uint8(v_e_931_, sizeof(void*)*4 + 8);
lean_inc(v_offset_932_);
lean_inc_ref(v_type_1051_);
v___x_1055_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_929_, v_d_930_, v_type_1051_, v_offset_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v_a_1057_; lean_object* v_fst_1058_; lean_object* v_snd_1059_; lean_object* v___x_1060_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
v_a_1057_ = lean_ctor_get(v___x_1055_, 1);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1055_, 2);
v_fst_1058_ = lean_ctor_get(v_a_1056_, 0);
lean_inc(v_fst_1058_);
v_snd_1059_ = lean_ctor_get(v_a_1056_, 1);
lean_inc(v_snd_1059_);
lean_dec(v_a_1056_);
lean_inc(v_offset_932_);
lean_inc_ref(v_value_1052_);
v___x_1060_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_929_, v_d_930_, v_value_1052_, v_offset_932_, v_snd_1059_, v_a_934_, v_a_935_, v_a_1057_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v_a_1062_; lean_object* v_fst_1063_; lean_object* v_snd_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
v_a_1062_ = lean_ctor_get(v___x_1060_, 1);
lean_inc(v_a_1062_);
lean_dec_ref_known(v___x_1060_, 2);
v_fst_1063_ = lean_ctor_get(v_a_1061_, 0);
lean_inc(v_fst_1063_);
v_snd_1064_ = lean_ctor_get(v_a_1061_, 1);
lean_inc(v_snd_1064_);
lean_dec(v_a_1061_);
v___x_1065_ = lean_unsigned_to_nat(1u);
v___x_1066_ = lean_nat_add(v_offset_932_, v___x_1065_);
lean_dec(v_offset_932_);
lean_inc_ref(v_body_1053_);
v___x_1067_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_929_, v_d_930_, v_body_1053_, v___x_1066_, v_snd_1064_, v_a_934_, v_a_935_, v_a_1062_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1098_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
v_a_1069_ = lean_ctor_get(v___x_1067_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1071_ = v___x_1067_;
v_isShared_1072_ = v_isSharedCheck_1098_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_inc(v_a_1068_);
lean_dec(v___x_1067_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1098_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v_fst_1073_; lean_object* v_snd_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1097_; 
v_fst_1073_ = lean_ctor_get(v_a_1068_, 0);
v_snd_1074_ = lean_ctor_get(v_a_1068_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_a_1068_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1076_ = v_a_1068_;
v_isShared_1077_ = v_isSharedCheck_1097_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_snd_1074_);
lean_inc(v_fst_1073_);
lean_dec(v_a_1068_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1097_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
uint8_t v___y_1079_; size_t v___x_1091_; size_t v___x_1092_; uint8_t v___x_1093_; 
v___x_1091_ = lean_ptr_addr(v_type_1051_);
v___x_1092_ = lean_ptr_addr(v_fst_1058_);
v___x_1093_ = lean_usize_dec_eq(v___x_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
v___y_1079_ = v___x_1093_;
goto v___jp_1078_;
}
else
{
size_t v___x_1094_; size_t v___x_1095_; uint8_t v___x_1096_; 
v___x_1094_ = lean_ptr_addr(v_value_1052_);
v___x_1095_ = lean_ptr_addr(v_fst_1063_);
v___x_1096_ = lean_usize_dec_eq(v___x_1094_, v___x_1095_);
v___y_1079_ = v___x_1096_;
goto v___jp_1078_;
}
v___jp_1078_:
{
if (v___y_1079_ == 0)
{
lean_object* v___x_1080_; 
lean_inc(v_declName_1050_);
lean_del_object(v___x_1076_);
lean_del_object(v___x_1071_);
lean_dec_ref_known(v_e_931_, 4);
v___x_1080_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1050_, v_fst_1058_, v_fst_1063_, v_fst_1073_, v_nondep_1054_, v_snd_1074_, v_a_934_, v_a_935_, v_a_1069_);
return v___x_1080_;
}
else
{
size_t v___x_1081_; size_t v___x_1082_; uint8_t v___x_1083_; 
v___x_1081_ = lean_ptr_addr(v_body_1053_);
v___x_1082_ = lean_ptr_addr(v_fst_1073_);
v___x_1083_ = lean_usize_dec_eq(v___x_1081_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_inc(v_declName_1050_);
lean_del_object(v___x_1076_);
lean_del_object(v___x_1071_);
lean_dec_ref_known(v_e_931_, 4);
v___x_1084_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1050_, v_fst_1058_, v_fst_1063_, v_fst_1073_, v_nondep_1054_, v_snd_1074_, v_a_934_, v_a_935_, v_a_1069_);
return v___x_1084_;
}
else
{
lean_object* v___x_1086_; 
lean_dec(v_fst_1073_);
lean_dec(v_fst_1063_);
lean_dec(v_fst_1058_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v_e_931_);
v___x_1086_ = v___x_1076_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_e_931_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_snd_1074_);
v___x_1086_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1088_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1086_);
v___x_1088_ = v___x_1071_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_a_1069_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
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
lean_dec(v_fst_1063_);
lean_dec(v_fst_1058_);
lean_dec_ref_known(v_e_931_, 4);
return v___x_1067_;
}
}
else
{
lean_dec(v_fst_1058_);
lean_dec_ref_known(v_e_931_, 4);
lean_dec(v_offset_932_);
return v___x_1060_;
}
}
else
{
lean_dec_ref_known(v_e_931_, 4);
lean_dec(v_offset_932_);
return v___x_1055_;
}
}
case 10:
{
lean_object* v_data_1099_; lean_object* v_expr_1100_; lean_object* v___x_1101_; 
v_data_1099_ = lean_ctor_get(v_e_931_, 0);
v_expr_1100_ = lean_ctor_get(v_e_931_, 1);
lean_inc_ref(v_expr_1100_);
v___x_1101_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_929_, v_d_930_, v_expr_1100_, v_offset_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1123_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_a_1103_ = lean_ctor_get(v___x_1101_, 1);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1105_ = v___x_1101_;
v_isShared_1106_ = v_isSharedCheck_1123_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1123_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v_fst_1107_; lean_object* v_snd_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1122_; 
v_fst_1107_ = lean_ctor_get(v_a_1102_, 0);
v_snd_1108_ = lean_ctor_get(v_a_1102_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_a_1102_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1110_ = v_a_1102_;
v_isShared_1111_ = v_isSharedCheck_1122_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_snd_1108_);
lean_inc(v_fst_1107_);
lean_dec(v_a_1102_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1122_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
size_t v___x_1112_; size_t v___x_1113_; uint8_t v___x_1114_; 
v___x_1112_ = lean_ptr_addr(v_expr_1100_);
v___x_1113_ = lean_ptr_addr(v_fst_1107_);
v___x_1114_ = lean_usize_dec_eq(v___x_1112_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
lean_inc(v_data_1099_);
lean_del_object(v___x_1110_);
lean_del_object(v___x_1105_);
lean_dec_ref_known(v_e_931_, 2);
v___x_1115_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_1099_, v_fst_1107_, v_snd_1108_, v_a_934_, v_a_935_, v_a_1103_);
return v___x_1115_;
}
else
{
lean_object* v___x_1117_; 
lean_dec(v_fst_1107_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v_e_931_);
v___x_1117_ = v___x_1110_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_e_931_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_snd_1108_);
v___x_1117_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1119_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1117_);
v___x_1119_ = v___x_1105_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_a_1103_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_931_, 2);
return v___x_1101_;
}
}
case 11:
{
lean_object* v_typeName_1124_; lean_object* v_idx_1125_; lean_object* v_struct_1126_; lean_object* v___x_1127_; 
v_typeName_1124_ = lean_ctor_get(v_e_931_, 0);
v_idx_1125_ = lean_ctor_get(v_e_931_, 1);
v_struct_1126_ = lean_ctor_get(v_e_931_, 2);
lean_inc_ref(v_struct_1126_);
v___x_1127_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_929_, v_d_930_, v_struct_1126_, v_offset_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1149_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_a_1129_ = lean_ctor_get(v___x_1127_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1131_ = v___x_1127_;
v_isShared_1132_ = v_isSharedCheck_1149_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1149_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v_fst_1133_; lean_object* v_snd_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1148_; 
v_fst_1133_ = lean_ctor_get(v_a_1128_, 0);
v_snd_1134_ = lean_ctor_get(v_a_1128_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_a_1128_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1136_ = v_a_1128_;
v_isShared_1137_ = v_isSharedCheck_1148_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_snd_1134_);
lean_inc(v_fst_1133_);
lean_dec(v_a_1128_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1148_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
size_t v___x_1138_; size_t v___x_1139_; uint8_t v___x_1140_; 
v___x_1138_ = lean_ptr_addr(v_struct_1126_);
v___x_1139_ = lean_ptr_addr(v_fst_1133_);
v___x_1140_ = lean_usize_dec_eq(v___x_1138_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
lean_inc(v_idx_1125_);
lean_inc(v_typeName_1124_);
lean_del_object(v___x_1136_);
lean_del_object(v___x_1131_);
lean_dec_ref_known(v_e_931_, 3);
v___x_1141_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_1124_, v_idx_1125_, v_fst_1133_, v_snd_1134_, v_a_934_, v_a_935_, v_a_1129_);
return v___x_1141_;
}
else
{
lean_object* v___x_1143_; 
lean_dec(v_fst_1133_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v_e_931_);
v___x_1143_ = v___x_1136_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_e_931_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_snd_1134_);
v___x_1143_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1145_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1143_);
v___x_1145_ = v___x_1131_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_a_1129_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_931_, 3);
return v___x_1127_;
}
}
default: 
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec(v_offset_932_);
lean_dec_ref(v_e_931_);
v___x_1150_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
v___x_1151_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_1150_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
return v___x_1151_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(lean_object* v_s_1152_, lean_object* v_d_1153_, lean_object* v_e_1154_, lean_object* v_offset_1155_, lean_object* v_a_1156_, uint8_t v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_key_1160_; lean_object* v_a_1162_; lean_object* v___x_1175_; 
lean_inc(v_offset_1155_);
lean_inc_ref(v_e_1154_);
v_key_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1160_, 0, v_e_1154_);
lean_ctor_set(v_key_1160_, 1, v_offset_1155_);
v___x_1175_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_1156_, v_key_1160_);
if (lean_obj_tag(v___x_1175_) == 1)
{
lean_object* v_val_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec_ref_known(v_key_1160_, 2);
lean_dec(v_offset_1155_);
lean_dec_ref(v_e_1154_);
v_val_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_val_1176_);
lean_dec_ref_known(v___x_1175_, 1);
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v_val_1176_);
lean_ctor_set(v___x_1177_, 1, v_a_1156_);
v___x_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v_a_1159_);
return v___x_1178_;
}
else
{
lean_object* v_s_u2081_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
lean_dec(v___x_1175_);
v_s_u2081_1179_ = lean_nat_add(v_s_1152_, v_offset_1155_);
v___x_1180_ = l_Lean_Expr_looseBVarRange(v_e_1154_);
v___x_1181_ = lean_nat_dec_le(v___x_1180_, v_s_u2081_1179_);
lean_dec(v___x_1180_);
if (v___x_1181_ == 0)
{
if (lean_obj_tag(v_e_1154_) == 0)
{
lean_object* v_deBruijnIndex_1182_; uint8_t v___x_1183_; 
v_deBruijnIndex_1182_ = lean_ctor_get(v_e_1154_, 0);
v___x_1183_ = lean_nat_dec_le(v_s_u2081_1179_, v_deBruijnIndex_1182_);
lean_dec(v_s_u2081_1179_);
if (v___x_1183_ == 0)
{
v_a_1162_ = v_a_1159_;
goto v___jp_1161_;
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_inc(v_deBruijnIndex_1182_);
lean_dec_ref_known(v_e_1154_, 1);
lean_dec(v_offset_1155_);
v___x_1184_ = lean_nat_add(v_deBruijnIndex_1182_, v_d_1153_);
lean_dec(v_deBruijnIndex_1182_);
v___x_1185_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_1184_, v_a_1159_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v_a_1187_; lean_object* v___x_1188_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
v_a_1187_ = lean_ctor_get(v___x_1185_, 1);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1185_, 2);
v___x_1188_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1160_, v_a_1186_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1187_);
return v___x_1188_;
}
else
{
lean_object* v_a_1189_; lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec_ref_known(v_key_1160_, 2);
lean_dec_ref(v_a_1156_);
v_a_1189_ = lean_ctor_get(v___x_1185_, 0);
v_a_1190_ = lean_ctor_get(v___x_1185_, 1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1185_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_inc(v_a_1189_);
lean_dec(v___x_1185_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1189_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
else
{
lean_dec(v_s_u2081_1179_);
v_a_1162_ = v_a_1159_;
goto v___jp_1161_;
}
}
else
{
lean_object* v___x_1198_; 
lean_dec(v_s_u2081_1179_);
lean_dec(v_offset_1155_);
v___x_1198_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1160_, v_e_1154_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
return v___x_1198_;
}
}
v___jp_1161_:
{
switch(lean_obj_tag(v_e_1154_))
{
case 9:
{
lean_object* v___x_1163_; 
lean_dec(v_offset_1155_);
v___x_1163_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1160_, v_e_1154_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1162_);
return v___x_1163_;
}
case 2:
{
lean_object* v___x_1164_; 
lean_dec(v_offset_1155_);
v___x_1164_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1160_, v_e_1154_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1162_);
return v___x_1164_;
}
case 0:
{
lean_object* v___x_1165_; 
lean_dec(v_offset_1155_);
v___x_1165_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1160_, v_e_1154_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1162_);
return v___x_1165_;
}
case 1:
{
lean_object* v___x_1166_; 
lean_dec(v_offset_1155_);
v___x_1166_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1160_, v_e_1154_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1162_);
return v___x_1166_;
}
case 4:
{
lean_object* v___x_1167_; 
lean_dec(v_offset_1155_);
v___x_1167_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1160_, v_e_1154_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1162_);
return v___x_1167_;
}
case 3:
{
lean_object* v___x_1168_; 
lean_dec(v_offset_1155_);
v___x_1168_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1160_, v_e_1154_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1162_);
return v___x_1168_;
}
default: 
{
lean_object* v___x_1169_; 
v___x_1169_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_1152_, v_d_1153_, v_e_1154_, v_offset_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1162_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v_a_1171_; lean_object* v_fst_1172_; lean_object* v_snd_1173_; lean_object* v___x_1174_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
v_a_1171_ = lean_ctor_get(v___x_1169_, 1);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1169_, 2);
v_fst_1172_ = lean_ctor_get(v_a_1170_, 0);
lean_inc(v_fst_1172_);
v_snd_1173_ = lean_ctor_get(v_a_1170_, 1);
lean_inc(v_snd_1173_);
lean_dec(v_a_1170_);
v___x_1174_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1160_, v_fst_1172_, v_snd_1173_, v_a_1157_, v_a_1158_, v_a_1171_);
return v___x_1174_;
}
else
{
lean_dec_ref_known(v_key_1160_, 2);
return v___x_1169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0___boxed(lean_object* v_s_1199_, lean_object* v_d_1200_, lean_object* v_e_1201_, lean_object* v_offset_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
uint8_t v_a_boxed_1207_; lean_object* v_res_1208_; 
v_a_boxed_1207_ = lean_unbox(v_a_1204_);
v_res_1208_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1199_, v_d_1200_, v_e_1201_, v_offset_1202_, v_a_1203_, v_a_boxed_1207_, v_a_1205_, v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_d_1200_);
lean_dec(v_s_1199_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0___boxed(lean_object* v_s_1209_, lean_object* v_d_1210_, lean_object* v_e_1211_, lean_object* v_offset_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
uint8_t v_a_boxed_1217_; lean_object* v_res_1218_; 
v_a_boxed_1217_ = lean_unbox(v_a_1214_);
v_res_1218_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_1209_, v_d_1210_, v_e_1211_, v_offset_1212_, v_a_1213_, v_a_boxed_1217_, v_a_1215_, v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_d_1210_);
lean_dec(v_s_1209_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27(lean_object* v_e_1219_, lean_object* v_s_1220_, lean_object* v_d_1221_, uint8_t v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = l_Lean_Expr_looseBVarRange(v_e_1219_);
v___x_1226_ = lean_nat_dec_le(v___x_1225_, v_s_1220_);
lean_dec(v___x_1225_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v_a_1229_; 
v___x_1227_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_e_1219_) == 0)
{
lean_object* v_deBruijnIndex_1257_; uint8_t v___x_1258_; 
v_deBruijnIndex_1257_ = lean_ctor_get(v_e_1219_, 0);
v___x_1258_ = lean_nat_dec_le(v_s_1220_, v_deBruijnIndex_1257_);
if (v___x_1258_ == 0)
{
v_a_1229_ = v_a_1224_;
goto v___jp_1228_;
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_inc(v_deBruijnIndex_1257_);
lean_dec_ref_known(v_e_1219_, 1);
v___x_1259_ = lean_nat_add(v_deBruijnIndex_1257_, v_d_1221_);
lean_dec(v_deBruijnIndex_1257_);
v___x_1260_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_1259_, v_a_1224_);
return v___x_1260_;
}
}
else
{
v_a_1229_ = v_a_1224_;
goto v___jp_1228_;
}
v___jp_1228_:
{
switch(lean_obj_tag(v_e_1219_))
{
case 9:
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v_e_1219_);
lean_ctor_set(v___x_1230_, 1, v_a_1229_);
return v___x_1230_;
}
case 2:
{
lean_object* v___x_1231_; 
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v_e_1219_);
lean_ctor_set(v___x_1231_, 1, v_a_1229_);
return v___x_1231_;
}
case 0:
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v_e_1219_);
lean_ctor_set(v___x_1232_, 1, v_a_1229_);
return v___x_1232_;
}
case 1:
{
lean_object* v___x_1233_; 
v___x_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1233_, 0, v_e_1219_);
lean_ctor_set(v___x_1233_, 1, v_a_1229_);
return v___x_1233_;
}
case 4:
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v_e_1219_);
lean_ctor_set(v___x_1234_, 1, v_a_1229_);
return v___x_1234_;
}
case 3:
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v_e_1219_);
lean_ctor_set(v___x_1235_, 1, v_a_1229_);
return v___x_1235_;
}
default: 
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1);
v___x_1237_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_1220_, v_d_1221_, v_e_1219_, v___x_1227_, v___x_1236_, v_a_1222_, v_a_1223_, v_a_1229_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1247_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
v_a_1239_ = lean_ctor_get(v___x_1237_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1241_ = v___x_1237_;
v_isShared_1242_ = v_isSharedCheck_1247_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_inc(v_a_1238_);
lean_dec(v___x_1237_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1247_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v_fst_1243_; lean_object* v___x_1245_; 
v_fst_1243_ = lean_ctor_get(v_a_1238_, 0);
lean_inc(v_fst_1243_);
lean_dec(v_a_1238_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v_fst_1243_);
v___x_1245_ = v___x_1241_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_fst_1243_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_a_1239_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
v_a_1248_ = lean_ctor_get(v___x_1237_, 0);
v_a_1249_ = lean_ctor_get(v___x_1237_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1237_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_inc(v_a_1248_);
lean_dec(v___x_1237_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1248_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v_e_1219_);
lean_ctor_set(v___x_1261_, 1, v_a_1224_);
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27___boxed(lean_object* v_e_1262_, lean_object* v_s_1263_, lean_object* v_d_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
uint8_t v_a_boxed_1268_; lean_object* v_res_1269_; 
v_a_boxed_1268_ = lean_unbox(v_a_1265_);
v_res_1269_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_e_1262_, v_s_1263_, v_d_1264_, v_a_boxed_1268_, v_a_1266_, v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_d_1264_);
lean_dec(v_s_1263_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS(lean_object* v_e_1270_, lean_object* v_s_1271_, lean_object* v_d_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v_debug_1282_; lean_object* v_env_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1280_ = lean_st_ref_get(v_a_1274_);
v___x_1281_ = lean_st_ref_get(v_a_1278_);
v_debug_1282_ = lean_ctor_get_uint8(v___x_1280_, sizeof(void*)*11);
lean_dec(v___x_1280_);
v_env_1283_ = lean_ctor_get(v___x_1281_, 0);
lean_inc_ref(v_env_1283_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(v_debug_1282_);
v___x_1285_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_liftLooseBVarsS_x27___boxed), 6, 4);
lean_closure_set(v___x_1285_, 0, v_e_1270_);
lean_closure_set(v___x_1285_, 1, v_s_1271_);
lean_closure_set(v___x_1285_, 2, v_d_1272_);
lean_closure_set(v___x_1285_, 3, v___x_1284_);
v___x_1286_ = 0;
v___x_1287_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1287_, 0, v_env_1283_);
lean_ctor_set_uint8(v___x_1287_, sizeof(void*)*1, v___x_1286_);
lean_ctor_set_uint8(v___x_1287_, sizeof(void*)*1 + 1, v___x_1286_);
v___x_1288_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_1285_, v___x_1287_, v_a_1274_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1299_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1299_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1299_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
if (lean_obj_tag(v_a_1289_) == 0)
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec_ref_known(v_a_1289_, 1);
lean_del_object(v___x_1291_);
v___x_1293_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2, &l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2);
v___x_1294_ = l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(v___x_1293_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
return v___x_1294_;
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; 
v_a_1295_ = lean_ctor_get(v_a_1289_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v_a_1289_, 1);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v_a_1295_);
v___x_1297_ = v___x_1291_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
v_a_1300_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1288_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1288_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___boxed(lean_object* v_e_1308_, lean_object* v_s_1309_, lean_object* v_d_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_Meta_Sym_liftLooseBVarsS(v_e_1308_, v_s_1309_, v_d_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
return v_res_1318_;
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
