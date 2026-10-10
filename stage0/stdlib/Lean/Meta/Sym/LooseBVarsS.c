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
lean_object* l_EStateM_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(lean_object* v_idx_5_, uint8_t v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v_idx_5_, v___y_8_);
return v___x_9_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_idx_5_ = stack[0].m_obj;
uint8_t v___y_6_ = stack[1].m_num;
lean_object* v___y_7_ = stack[2].m_obj;
lean_object* v___y_8_ = stack[3].m_obj;
lean_object* v_res_10_;
v_res_10_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(v_idx_5_, v___y_6_, v___y_7_, v___y_8_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___boxed(lean_object* v_idx_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_){
_start:
{
uint8_t v___y_24192__boxed_15_; lean_object* v_res_16_; 
v___y_24192__boxed_15_ = lean_unbox(v___y_12_);
v_res_16_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(v_idx_11_, v___y_24192__boxed_15_, v___y_13_, v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_16_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(lean_object* v_x_17_, uint8_t v_bi_18_, lean_object* v_t_19_, lean_object* v_b_20_, lean_object* v___y_21_, uint8_t v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___y_26_; lean_object* v___y_27_; 
if (v___y_22_ == 0)
{
v___y_26_ = v___y_21_;
v___y_27_ = v___y_24_;
goto v___jp_25_;
}
else
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_19_, v___y_22_, v___y_23_, v___y_24_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; lean_object* v___x_51_; 
v_a_50_ = lean_ctor_get(v___x_49_, 1);
lean_inc(v_a_50_);
lean_dec_ref_known(v___x_49_, 2);
v___x_51_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_20_, v___y_22_, v___y_23_, v_a_50_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; 
v_a_52_ = lean_ctor_get(v___x_51_, 1);
lean_inc(v_a_52_);
lean_dec_ref_known(v___x_51_, 2);
v___y_26_ = v___y_21_;
v___y_27_ = v_a_52_;
goto v___jp_25_;
}
else
{
lean_object* v_a_53_; lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
lean_dec_ref(v___y_21_);
lean_dec_ref(v_b_20_);
lean_dec_ref(v_t_19_);
lean_dec(v_x_17_);
v_a_53_ = lean_ctor_get(v___x_51_, 0);
v_a_54_ = lean_ctor_get(v___x_51_, 1);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v___x_51_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_inc(v_a_53_);
lean_dec(v___x_51_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_53_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_a_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
else
{
lean_object* v_a_62_; lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
lean_dec_ref(v___y_21_);
lean_dec_ref(v_b_20_);
lean_dec_ref(v_t_19_);
lean_dec(v_x_17_);
v_a_62_ = lean_ctor_get(v___x_49_, 0);
v_a_63_ = lean_ctor_get(v___x_49_, 1);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_70_ == 0)
{
v___x_65_ = v___x_49_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_inc(v_a_62_);
lean_dec(v___x_49_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_a_62_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_a_63_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
v___jp_25_:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = l_Lean_Expr_forallE___override(v_x_17_, v_t_19_, v_b_20_, v_bi_18_);
v___x_29_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_28_, v___y_27_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_a_31_ = lean_ctor_get(v___x_29_, 1);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_29_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_a_30_);
lean_ctor_set(v___x_35_, 1, v___y_26_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_a_31_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
else
{
lean_object* v_a_40_; lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
lean_dec_ref(v___y_26_);
v_a_40_ = lean_ctor_get(v___x_29_, 0);
v_a_41_ = lean_ctor_get(v___x_29_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v___x_29_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_inc(v_a_40_);
lean_dec(v___x_29_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_a_40_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_a_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_17_ = stack[0].m_obj;
uint8_t v_bi_18_ = stack[1].m_num;
lean_object* v_t_19_ = stack[2].m_obj;
lean_object* v_b_20_ = stack[3].m_obj;
lean_object* v___y_21_ = stack[4].m_obj;
uint8_t v___y_22_ = stack[5].m_num;
lean_object* v___y_23_ = stack[6].m_obj;
lean_object* v___y_24_ = stack[7].m_obj;
lean_object* v_res_71_;
v_res_71_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_x_17_, v_bi_18_, v_t_19_, v_b_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4___boxed(lean_object* v_x_72_, lean_object* v_bi_73_, lean_object* v_t_74_, lean_object* v_b_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
uint8_t v_bi_boxed_80_; uint8_t v___y_24211__boxed_81_; lean_object* v_res_82_; 
v_bi_boxed_80_ = lean_unbox(v_bi_73_);
v___y_24211__boxed_81_ = lean_unbox(v___y_77_);
v_res_82_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_x_72_, v_bi_boxed_80_, v_t_74_, v_b_75_, v___y_76_, v___y_24211__boxed_81_, v___y_78_, v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_82_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(lean_object* v_structName_83_, lean_object* v_idx_84_, lean_object* v_struct_85_, lean_object* v___y_86_, uint8_t v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___y_91_; lean_object* v___y_92_; 
if (v___y_87_ == 0)
{
v___y_91_ = v___y_86_;
v___y_92_ = v___y_89_;
goto v___jp_90_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_85_, v___y_87_, v___y_88_, v___y_89_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; 
v_a_115_ = lean_ctor_get(v___x_114_, 1);
lean_inc(v_a_115_);
lean_dec_ref_known(v___x_114_, 2);
v___y_91_ = v___y_86_;
v___y_92_ = v_a_115_;
goto v___jp_90_;
}
else
{
lean_object* v_a_116_; lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
lean_dec_ref(v___y_86_);
lean_dec_ref(v_struct_85_);
lean_dec(v_idx_84_);
lean_dec(v_structName_83_);
v_a_116_ = lean_ctor_get(v___x_114_, 0);
v_a_117_ = lean_ctor_get(v___x_114_, 1);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_124_ == 0)
{
v___x_119_ = v___x_114_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_inc(v_a_116_);
lean_dec(v___x_114_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_116_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_a_117_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
v___jp_90_:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = l_Lean_Expr_proj___override(v_structName_83_, v_idx_84_, v_struct_85_);
v___x_94_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_93_, v___y_92_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_104_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
v_a_96_ = lean_ctor_get(v___x_94_, 1);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_104_ == 0)
{
v___x_98_ = v___x_94_;
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_inc(v_a_95_);
lean_dec(v___x_94_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v_a_95_);
lean_ctor_set(v___x_100_, 1, v___y_91_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_100_);
v___x_102_ = v___x_98_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_a_96_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
else
{
lean_object* v_a_105_; lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
lean_dec_ref(v___y_91_);
v_a_105_ = lean_ctor_get(v___x_94_, 0);
v_a_106_ = lean_ctor_get(v___x_94_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_94_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_inc(v_a_105_);
lean_dec(v___x_94_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_105_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_structName_83_ = stack[0].m_obj;
lean_object* v_idx_84_ = stack[1].m_obj;
lean_object* v_struct_85_ = stack[2].m_obj;
lean_object* v___y_86_ = stack[3].m_obj;
uint8_t v___y_87_ = stack[4].m_num;
lean_object* v___y_88_ = stack[5].m_obj;
lean_object* v___y_89_ = stack[6].m_obj;
lean_object* v_res_125_;
v_res_125_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_structName_83_, v_idx_84_, v_struct_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
stack->m_obj
 = v_res_125_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7___boxed(lean_object* v_structName_126_, lean_object* v_idx_127_, lean_object* v_struct_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
uint8_t v___y_24371__boxed_133_; lean_object* v_res_134_; 
v___y_24371__boxed_133_ = lean_unbox(v___y_130_);
v_res_134_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_structName_126_, v_idx_127_, v_struct_128_, v___y_129_, v___y_24371__boxed_133_, v___y_131_, v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_134_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(lean_object* v_x_135_, uint8_t v_bi_136_, lean_object* v_t_137_, lean_object* v_b_138_, lean_object* v___y_139_, uint8_t v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v___y_144_; lean_object* v___y_145_; 
if (v___y_140_ == 0)
{
v___y_144_ = v___y_139_;
v___y_145_ = v___y_142_;
goto v___jp_143_;
}
else
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_137_, v___y_140_, v___y_141_, v___y_142_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_169_; 
v_a_168_ = lean_ctor_get(v___x_167_, 1);
lean_inc(v_a_168_);
lean_dec_ref_known(v___x_167_, 2);
v___x_169_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_138_, v___y_140_, v___y_141_, v_a_168_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; 
v_a_170_ = lean_ctor_get(v___x_169_, 1);
lean_inc(v_a_170_);
lean_dec_ref_known(v___x_169_, 2);
v___y_144_ = v___y_139_;
v___y_145_ = v_a_170_;
goto v___jp_143_;
}
else
{
lean_object* v_a_171_; lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
lean_dec_ref(v___y_139_);
lean_dec_ref(v_b_138_);
lean_dec_ref(v_t_137_);
lean_dec(v_x_135_);
v_a_171_ = lean_ctor_get(v___x_169_, 0);
v_a_172_ = lean_ctor_get(v___x_169_, 1);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_169_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_inc(v_a_171_);
lean_dec(v___x_169_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_171_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_a_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
else
{
lean_object* v_a_180_; lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
lean_dec_ref(v___y_139_);
lean_dec_ref(v_b_138_);
lean_dec_ref(v_t_137_);
lean_dec(v_x_135_);
v_a_180_ = lean_ctor_get(v___x_167_, 0);
v_a_181_ = lean_ctor_get(v___x_167_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_167_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_inc(v_a_180_);
lean_dec(v___x_167_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_180_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
v___jp_143_:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = l_Lean_Expr_lam___override(v_x_135_, v_t_137_, v_b_138_, v_bi_136_);
v___x_147_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_146_, v___y_145_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_157_; 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
v_a_149_ = lean_ctor_get(v___x_147_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_157_ == 0)
{
v___x_151_ = v___x_147_;
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_inc(v_a_148_);
lean_dec(v___x_147_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v_a_148_);
lean_ctor_set(v___x_153_, 1, v___y_144_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_153_);
v___x_155_ = v___x_151_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_a_149_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
else
{
lean_object* v_a_158_; lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
lean_dec_ref(v___y_144_);
v_a_158_ = lean_ctor_get(v___x_147_, 0);
v_a_159_ = lean_ctor_get(v___x_147_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_147_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_inc(v_a_158_);
lean_dec(v___x_147_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_158_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_135_ = stack[0].m_obj;
uint8_t v_bi_136_ = stack[1].m_num;
lean_object* v_t_137_ = stack[2].m_obj;
lean_object* v_b_138_ = stack[3].m_obj;
lean_object* v___y_139_ = stack[4].m_obj;
uint8_t v___y_140_ = stack[5].m_num;
lean_object* v___y_141_ = stack[6].m_obj;
lean_object* v___y_142_ = stack[7].m_obj;
lean_object* v_res_189_;
v_res_189_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_x_135_, v_bi_136_, v_t_137_, v_b_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3___boxed(lean_object* v_x_190_, lean_object* v_bi_191_, lean_object* v_t_192_, lean_object* v_b_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
uint8_t v_bi_boxed_198_; uint8_t v___y_24497__boxed_199_; lean_object* v_res_200_; 
v_bi_boxed_198_ = lean_unbox(v_bi_191_);
v___y_24497__boxed_199_ = lean_unbox(v___y_195_);
v_res_200_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_x_190_, v_bi_boxed_198_, v_t_192_, v_b_193_, v___y_194_, v___y_24497__boxed_199_, v___y_196_, v___y_197_);
lean_dec_ref(v___y_196_);
return v_res_200_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(lean_object* v_msg_208_, lean_object* v___y_209_, uint8_t v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___f_213_; lean_object* v___f_214_; lean_object* v___f_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___f_225_; lean_object* v___f_226_; lean_object* v___f_227_; lean_object* v___f_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_23834__overap_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___f_213_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0));
v___f_214_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1));
v___f_215_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2));
v___x_216_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3));
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___f_213_);
v___x_218_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4));
v___x_219_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5));
v___x_220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_220_, 0, v___x_217_);
lean_ctor_set(v___x_220_, 1, v___x_218_);
lean_ctor_set(v___x_220_, 2, v___f_214_);
lean_ctor_set(v___x_220_, 3, v___f_215_);
lean_ctor_set(v___x_220_, 4, v___x_219_);
v___x_221_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6));
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = l_ReaderT_instMonad___redArg(v___x_222_);
v___x_224_ = l_ReaderT_instMonad___redArg(v___x_223_);
lean_inc_ref_n(v___x_224_, 6);
v___f_225_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_225_, 0, v___x_224_);
v___f_226_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_226_, 0, v___x_224_);
v___f_227_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_227_, 0, v___x_224_);
v___f_228_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_228_, 0, v___x_224_);
v___x_229_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_229_, 0, lean_box(0));
lean_closure_set(v___x_229_, 1, lean_box(0));
lean_closure_set(v___x_229_, 2, v___x_224_);
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___f_225_);
v___x_231_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_231_, 0, lean_box(0));
lean_closure_set(v___x_231_, 1, lean_box(0));
lean_closure_set(v___x_231_, 2, v___x_224_);
v___x_232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
lean_ctor_set(v___x_232_, 2, v___f_226_);
lean_ctor_set(v___x_232_, 3, v___f_227_);
lean_ctor_set(v___x_232_, 4, v___f_228_);
v___x_233_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_233_, 0, lean_box(0));
lean_closure_set(v___x_233_, 1, lean_box(0));
lean_closure_set(v___x_233_, 2, v___x_224_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = l_Lean_instInhabitedExpr;
v___x_236_ = l_instInhabitedOfMonad___redArg(v___x_234_, v___x_235_);
v___x_23834__overap_237_ = lean_panic_fn_borrowed(v___x_236_, v_msg_208_);
lean_dec(v___x_236_);
v___x_238_ = lean_box(v___y_210_);
lean_inc_ref(v___y_211_);
v___x_239_ = lean_apply_4(v___x_23834__overap_237_, v___y_209_, v___x_238_, v___y_211_, v___y_212_);
return v___x_239_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_208_ = stack[0].m_obj;
lean_object* v___y_209_ = stack[1].m_obj;
uint8_t v___y_210_ = stack[2].m_num;
lean_object* v___y_211_ = stack[3].m_obj;
lean_object* v___y_212_ = stack[4].m_obj;
lean_object* v_res_240_;
v_res_240_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v_msg_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
stack->m_obj
 = v_res_240_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___boxed(lean_object* v_msg_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
uint8_t v___y_24671__boxed_246_; lean_object* v_res_247_; 
v___y_24671__boxed_246_ = lean_unbox(v___y_243_);
v_res_247_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v_msg_241_, v___y_242_, v___y_24671__boxed_246_, v___y_244_, v___y_245_);
lean_dec_ref(v___y_244_);
return v_res_247_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(lean_object* v_f_248_, lean_object* v_a_249_, lean_object* v___y_250_, uint8_t v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___y_255_; lean_object* v___y_256_; 
if (v___y_251_ == 0)
{
v___y_255_ = v___y_250_;
v___y_256_ = v___y_253_;
goto v___jp_254_;
}
else
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_248_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_280_; 
v_a_279_ = lean_ctor_get(v___x_278_, 1);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_278_, 2);
v___x_280_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_249_, v___y_251_, v___y_252_, v_a_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; 
v_a_281_ = lean_ctor_get(v___x_280_, 1);
lean_inc(v_a_281_);
lean_dec_ref_known(v___x_280_, 2);
v___y_255_ = v___y_250_;
v___y_256_ = v_a_281_;
goto v___jp_254_;
}
else
{
lean_object* v_a_282_; lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec_ref(v___y_250_);
lean_dec_ref(v_a_249_);
lean_dec_ref(v_f_248_);
v_a_282_ = lean_ctor_get(v___x_280_, 0);
v_a_283_ = lean_ctor_get(v___x_280_, 1);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_280_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_inc(v_a_282_);
lean_dec(v___x_280_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_282_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
lean_object* v_a_291_; lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec_ref(v___y_250_);
lean_dec_ref(v_a_249_);
lean_dec_ref(v_f_248_);
v_a_291_ = lean_ctor_get(v___x_278_, 0);
v_a_292_ = lean_ctor_get(v___x_278_, 1);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_278_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_inc(v_a_291_);
lean_dec(v___x_278_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_291_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
v___jp_254_:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = l_Lean_Expr_app___override(v_f_248_, v_a_249_);
v___x_258_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_257_, v___y_256_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_268_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_a_260_ = lean_ctor_get(v___x_258_, 1);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_268_ == 0)
{
v___x_262_ = v___x_258_;
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v_a_259_);
lean_ctor_set(v___x_264_, 1, v___y_255_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v___x_264_);
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v_a_260_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
else
{
lean_object* v_a_269_; lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec_ref(v___y_255_);
v_a_269_ = lean_ctor_get(v___x_258_, 0);
v_a_270_ = lean_ctor_get(v___x_258_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_258_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_inc(v_a_269_);
lean_dec(v___x_258_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_269_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_248_ = stack[0].m_obj;
lean_object* v_a_249_ = stack[1].m_obj;
lean_object* v___y_250_ = stack[2].m_obj;
uint8_t v___y_251_ = stack[3].m_num;
lean_object* v___y_252_ = stack[4].m_obj;
lean_object* v___y_253_ = stack[5].m_obj;
lean_object* v_res_300_;
v_res_300_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_f_248_, v_a_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
stack->m_obj
 = v_res_300_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2___boxed(lean_object* v_f_301_, lean_object* v_a_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
uint8_t v___y_24783__boxed_307_; lean_object* v_res_308_; 
v___y_24783__boxed_307_ = lean_unbox(v___y_304_);
v_res_308_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_f_301_, v_a_302_, v___y_303_, v___y_24783__boxed_307_, v___y_305_, v___y_306_);
lean_dec_ref(v___y_305_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(lean_object* v_a_309_, lean_object* v_x_310_){
_start:
{
if (lean_obj_tag(v_x_310_) == 0)
{
lean_object* v___x_311_; 
v___x_311_ = lean_box(0);
return v___x_311_;
}
else
{
lean_object* v_key_312_; lean_object* v_value_313_; lean_object* v_tail_314_; lean_object* v_fst_315_; lean_object* v_snd_316_; lean_object* v_fst_317_; lean_object* v_snd_318_; size_t v___x_319_; size_t v___x_320_; uint8_t v___x_321_; 
v_key_312_ = lean_ctor_get(v_x_310_, 0);
v_value_313_ = lean_ctor_get(v_x_310_, 1);
v_tail_314_ = lean_ctor_get(v_x_310_, 2);
v_fst_315_ = lean_ctor_get(v_key_312_, 0);
v_snd_316_ = lean_ctor_get(v_key_312_, 1);
v_fst_317_ = lean_ctor_get(v_a_309_, 0);
v_snd_318_ = lean_ctor_get(v_a_309_, 1);
v___x_319_ = lean_ptr_addr(v_fst_315_);
v___x_320_ = lean_ptr_addr(v_fst_317_);
v___x_321_ = lean_usize_dec_eq(v___x_319_, v___x_320_);
if (v___x_321_ == 0)
{
v_x_310_ = v_tail_314_;
goto _start;
}
else
{
uint8_t v___x_323_; 
v___x_323_ = lean_nat_dec_eq(v_snd_316_, v_snd_318_);
if (v___x_323_ == 0)
{
v_x_310_ = v_tail_314_;
goto _start;
}
else
{
lean_object* v___x_325_; 
lean_inc(v_value_313_);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v_value_313_);
return v___x_325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg___boxed(lean_object* v_a_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_326_, v_x_327_);
lean_dec(v_x_327_);
lean_dec_ref(v_a_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(lean_object* v_m_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_buckets_331_; lean_object* v_fst_332_; lean_object* v_snd_333_; lean_object* v___x_334_; size_t v___x_335_; size_t v___x_336_; size_t v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v___x_342_; uint64_t v_fold_343_; uint64_t v___x_344_; uint64_t v___x_345_; uint64_t v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; size_t v___x_350_; size_t v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_buckets_331_ = lean_ctor_get(v_m_329_, 1);
v_fst_332_ = lean_ctor_get(v_a_330_, 0);
v_snd_333_ = lean_ctor_get(v_a_330_, 1);
v___x_334_ = lean_array_get_size(v_buckets_331_);
v___x_335_ = lean_ptr_addr(v_fst_332_);
v___x_336_ = ((size_t)3ULL);
v___x_337_ = lean_usize_shift_right(v___x_335_, v___x_336_);
v___x_338_ = lean_usize_to_uint64(v___x_337_);
v___x_339_ = lean_uint64_of_nat(v_snd_333_);
v___x_340_ = lean_uint64_mix_hash(v___x_338_, v___x_339_);
v___x_341_ = 32ULL;
v___x_342_ = lean_uint64_shift_right(v___x_340_, v___x_341_);
v_fold_343_ = lean_uint64_xor(v___x_340_, v___x_342_);
v___x_344_ = 16ULL;
v___x_345_ = lean_uint64_shift_right(v_fold_343_, v___x_344_);
v___x_346_ = lean_uint64_xor(v_fold_343_, v___x_345_);
v___x_347_ = lean_uint64_to_usize(v___x_346_);
v___x_348_ = lean_usize_of_nat(v___x_334_);
v___x_349_ = ((size_t)1ULL);
v___x_350_ = lean_usize_sub(v___x_348_, v___x_349_);
v___x_351_ = lean_usize_land(v___x_347_, v___x_350_);
v___x_352_ = lean_array_uget_borrowed(v_buckets_331_, v___x_351_);
v___x_353_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_330_, v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_m_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_354_, v_a_355_);
lean_dec_ref(v_a_355_);
lean_dec_ref(v_m_354_);
return v_res_356_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(lean_object* v_x_357_, lean_object* v_t_358_, lean_object* v_v_359_, lean_object* v_b_360_, uint8_t v_nondep_361_, lean_object* v___y_362_, uint8_t v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v___y_367_; lean_object* v___y_368_; 
if (v___y_363_ == 0)
{
v___y_367_ = v___y_362_;
v___y_368_ = v___y_365_;
goto v___jp_366_;
}
else
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_358_, v___y_363_, v___y_364_, v___y_365_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_392_; 
v_a_391_ = lean_ctor_get(v___x_390_, 1);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_390_, 2);
v___x_392_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_359_, v___y_363_, v___y_364_, v_a_391_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_394_; 
v_a_393_ = lean_ctor_get(v___x_392_, 1);
lean_inc(v_a_393_);
lean_dec_ref_known(v___x_392_, 2);
v___x_394_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_360_, v___y_363_, v___y_364_, v_a_393_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; 
v_a_395_ = lean_ctor_get(v___x_394_, 1);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 2);
v___y_367_ = v___y_362_;
v___y_368_ = v_a_395_;
goto v___jp_366_;
}
else
{
lean_object* v_a_396_; lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec_ref(v___y_362_);
lean_dec_ref(v_b_360_);
lean_dec_ref(v_v_359_);
lean_dec_ref(v_t_358_);
lean_dec(v_x_357_);
v_a_396_ = lean_ctor_get(v___x_394_, 0);
v_a_397_ = lean_ctor_get(v___x_394_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_394_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_inc(v_a_396_);
lean_dec(v___x_394_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_396_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_dec_ref(v___y_362_);
lean_dec_ref(v_b_360_);
lean_dec_ref(v_v_359_);
lean_dec_ref(v_t_358_);
lean_dec(v_x_357_);
v_a_405_ = lean_ctor_get(v___x_392_, 0);
v_a_406_ = lean_ctor_get(v___x_392_, 1);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_392_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_inc(v_a_405_);
lean_dec(v___x_392_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_405_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec_ref(v___y_362_);
lean_dec_ref(v_b_360_);
lean_dec_ref(v_v_359_);
lean_dec_ref(v_t_358_);
lean_dec(v_x_357_);
v_a_414_ = lean_ctor_get(v___x_390_, 0);
v_a_415_ = lean_ctor_get(v___x_390_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_390_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_inc(v_a_414_);
lean_dec(v___x_390_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_414_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
v___jp_366_:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = l_Lean_Expr_letE___override(v_x_357_, v_t_358_, v_v_359_, v_b_360_, v_nondep_361_);
v___x_370_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_369_, v___y_368_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_380_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_a_372_ = lean_ctor_get(v___x_370_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_380_ == 0)
{
v___x_374_ = v___x_370_;
v_isShared_375_ = v_isSharedCheck_380_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_380_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v_a_371_);
lean_ctor_set(v___x_376_, 1, v___y_367_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_376_);
v___x_378_ = v___x_374_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_a_372_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
else
{
lean_object* v_a_381_; lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec_ref(v___y_367_);
v_a_381_ = lean_ctor_get(v___x_370_, 0);
v_a_382_ = lean_ctor_get(v___x_370_, 1);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_370_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_inc(v_a_381_);
lean_dec(v___x_370_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_381_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_357_ = stack[0].m_obj;
lean_object* v_t_358_ = stack[1].m_obj;
lean_object* v_v_359_ = stack[2].m_obj;
lean_object* v_b_360_ = stack[3].m_obj;
uint8_t v_nondep_361_ = stack[4].m_num;
lean_object* v___y_362_ = stack[5].m_obj;
uint8_t v___y_363_ = stack[6].m_num;
lean_object* v___y_364_ = stack[7].m_obj;
lean_object* v___y_365_ = stack[8].m_obj;
lean_object* v_res_423_;
v_res_423_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_x_357_, v_t_358_, v_v_359_, v_b_360_, v_nondep_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
stack->m_obj
 = v_res_423_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5___boxed(lean_object* v_x_424_, lean_object* v_t_425_, lean_object* v_v_426_, lean_object* v_b_427_, lean_object* v_nondep_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
uint8_t v_nondep_boxed_433_; uint8_t v___y_25059__boxed_434_; lean_object* v_res_435_; 
v_nondep_boxed_433_ = lean_unbox(v_nondep_428_);
v___y_25059__boxed_434_ = lean_unbox(v___y_430_);
v_res_435_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_x_424_, v_t_425_, v_v_426_, v_b_427_, v_nondep_boxed_433_, v___y_429_, v___y_25059__boxed_434_, v___y_431_, v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_435_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(lean_object* v_d_436_, lean_object* v_e_437_, lean_object* v___y_438_, uint8_t v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___y_443_; lean_object* v___y_444_; 
if (v___y_439_ == 0)
{
v___y_443_ = v___y_438_;
v___y_444_ = v___y_441_;
goto v___jp_442_;
}
else
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_437_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; 
v_a_467_ = lean_ctor_get(v___x_466_, 1);
lean_inc(v_a_467_);
lean_dec_ref_known(v___x_466_, 2);
v___y_443_ = v___y_438_;
v___y_444_ = v_a_467_;
goto v___jp_442_;
}
else
{
lean_object* v_a_468_; lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec_ref(v___y_438_);
lean_dec_ref(v_e_437_);
lean_dec(v_d_436_);
v_a_468_ = lean_ctor_get(v___x_466_, 0);
v_a_469_ = lean_ctor_get(v___x_466_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_466_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_inc(v_a_468_);
lean_dec(v___x_466_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_468_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
v___jp_442_:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = l_Lean_Expr_mdata___override(v_d_436_, v_e_437_);
v___x_446_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_445_, v___y_444_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_456_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_a_448_ = lean_ctor_get(v___x_446_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_456_ == 0)
{
v___x_450_ = v___x_446_;
v_isShared_451_ = v_isSharedCheck_456_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_456_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v_a_447_);
lean_ctor_set(v___x_452_, 1, v___y_443_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_452_);
v___x_454_ = v___x_450_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_a_448_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
else
{
lean_object* v_a_457_; lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec_ref(v___y_443_);
v_a_457_ = lean_ctor_get(v___x_446_, 0);
v_a_458_ = lean_ctor_get(v___x_446_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_446_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_inc(v_a_457_);
lean_dec(v___x_446_);
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
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_436_ = stack[0].m_obj;
lean_object* v_e_437_ = stack[1].m_obj;
lean_object* v___y_438_ = stack[2].m_obj;
uint8_t v___y_439_ = stack[3].m_num;
lean_object* v___y_440_ = stack[4].m_obj;
lean_object* v___y_441_ = stack[5].m_obj;
lean_object* v_res_477_;
v_res_477_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_d_436_, v_e_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
stack->m_obj
 = v_res_477_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6___boxed(lean_object* v_d_478_, lean_object* v_e_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
uint8_t v___y_25253__boxed_484_; lean_object* v_res_485_; 
v___y_25253__boxed_484_ = lean_unbox(v___y_481_);
v_res_485_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_d_478_, v_e_479_, v___y_480_, v___y_25253__boxed_484_, v___y_482_, v___y_483_);
lean_dec_ref(v___y_482_);
return v_res_485_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_489_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2));
v___x_490_ = lean_unsigned_to_nat(67u);
v___x_491_ = lean_unsigned_to_nat(35u);
v___x_492_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1));
v___x_493_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0));
v___x_494_ = l_mkPanicMessageWithDecl(v___x_493_, v___x_492_, v___x_491_, v___x_490_, v___x_489_);
return v___x_494_;
}
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(lean_object* v_s_495_, lean_object* v_d_496_, lean_object* v_e_497_, lean_object* v_offset_498_, lean_object* v_a_499_, uint8_t v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
switch(lean_obj_tag(v_e_497_))
{
case 5:
{
lean_object* v_fn_503_; lean_object* v_arg_504_; lean_object* v___x_505_; 
v_fn_503_ = lean_ctor_get(v_e_497_, 0);
v_arg_504_ = lean_ctor_get(v_e_497_, 1);
lean_inc(v_offset_498_);
lean_inc_ref(v_fn_503_);
v___x_505_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_495_, v_d_496_, v_fn_503_, v_offset_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v_a_507_; lean_object* v_fst_508_; lean_object* v_snd_509_; lean_object* v___x_510_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
v_a_507_ = lean_ctor_get(v___x_505_, 1);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_505_, 2);
v_fst_508_ = lean_ctor_get(v_a_506_, 0);
lean_inc(v_fst_508_);
v_snd_509_ = lean_ctor_get(v_a_506_, 1);
lean_inc(v_snd_509_);
lean_dec(v_a_506_);
lean_inc_ref(v_arg_504_);
v___x_510_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_495_, v_d_496_, v_arg_504_, v_offset_498_, v_snd_509_, v_a_500_, v_a_501_, v_a_507_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_536_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_a_512_ = lean_ctor_get(v___x_510_, 1);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_536_ == 0)
{
v___x_514_ = v___x_510_;
v_isShared_515_ = v_isSharedCheck_536_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_536_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v_fst_516_; lean_object* v_snd_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_535_; 
v_fst_516_ = lean_ctor_get(v_a_511_, 0);
v_snd_517_ = lean_ctor_get(v_a_511_, 1);
v_isSharedCheck_535_ = !lean_is_exclusive(v_a_511_);
if (v_isSharedCheck_535_ == 0)
{
v___x_519_ = v_a_511_;
v_isShared_520_ = v_isSharedCheck_535_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_snd_517_);
lean_inc(v_fst_516_);
lean_dec(v_a_511_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_535_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
size_t v___x_521_; size_t v___x_522_; uint8_t v___x_523_; 
v___x_521_ = lean_ptr_addr(v_fn_503_);
v___x_522_ = lean_ptr_addr(v_fst_508_);
v___x_523_ = lean_usize_dec_eq(v___x_521_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; 
lean_del_object(v___x_519_);
lean_del_object(v___x_514_);
lean_dec_ref_known(v_e_497_, 2);
v___x_524_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_508_, v_fst_516_, v_snd_517_, v_a_500_, v_a_501_, v_a_512_);
return v___x_524_;
}
else
{
size_t v___x_525_; size_t v___x_526_; uint8_t v___x_527_; 
v___x_525_ = lean_ptr_addr(v_arg_504_);
v___x_526_ = lean_ptr_addr(v_fst_516_);
v___x_527_ = lean_usize_dec_eq(v___x_525_, v___x_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
lean_del_object(v___x_519_);
lean_del_object(v___x_514_);
lean_dec_ref_known(v_e_497_, 2);
v___x_528_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_508_, v_fst_516_, v_snd_517_, v_a_500_, v_a_501_, v_a_512_);
return v___x_528_;
}
else
{
lean_object* v___x_530_; 
lean_dec(v_fst_516_);
lean_dec(v_fst_508_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v_e_497_);
v___x_530_ = v___x_519_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_e_497_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_snd_517_);
v___x_530_ = v_reuseFailAlloc_534_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_532_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_530_);
v___x_532_ = v___x_514_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_a_512_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_508_);
lean_dec_ref_known(v_e_497_, 2);
return v___x_510_;
}
}
else
{
lean_dec_ref_known(v_e_497_, 2);
lean_dec(v_offset_498_);
return v___x_505_;
}
}
case 6:
{
lean_object* v_binderName_537_; lean_object* v_binderType_538_; lean_object* v_body_539_; uint8_t v_binderInfo_540_; lean_object* v___x_541_; 
v_binderName_537_ = lean_ctor_get(v_e_497_, 0);
v_binderType_538_ = lean_ctor_get(v_e_497_, 1);
v_body_539_ = lean_ctor_get(v_e_497_, 2);
v_binderInfo_540_ = lean_ctor_get_uint8(v_e_497_, sizeof(void*)*3 + 8);
lean_inc(v_offset_498_);
lean_inc_ref(v_binderType_538_);
v___x_541_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_495_, v_d_496_, v_binderType_538_, v_offset_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v_a_543_; lean_object* v_fst_544_; lean_object* v_snd_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
v_a_543_ = lean_ctor_get(v___x_541_, 1);
lean_inc(v_a_543_);
lean_dec_ref_known(v___x_541_, 2);
v_fst_544_ = lean_ctor_get(v_a_542_, 0);
lean_inc(v_fst_544_);
v_snd_545_ = lean_ctor_get(v_a_542_, 1);
lean_inc(v_snd_545_);
lean_dec(v_a_542_);
v___x_546_ = lean_unsigned_to_nat(1u);
v___x_547_ = lean_nat_add(v_offset_498_, v___x_546_);
lean_dec(v_offset_498_);
lean_inc_ref(v_body_539_);
v___x_548_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_495_, v_d_496_, v_body_539_, v___x_547_, v_snd_545_, v_a_500_, v_a_501_, v_a_543_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_574_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
v_a_550_ = lean_ctor_get(v___x_548_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_574_ == 0)
{
v___x_552_ = v___x_548_;
v_isShared_553_ = v_isSharedCheck_574_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_inc(v_a_549_);
lean_dec(v___x_548_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_574_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v_fst_554_; lean_object* v_snd_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_573_; 
v_fst_554_ = lean_ctor_get(v_a_549_, 0);
v_snd_555_ = lean_ctor_get(v_a_549_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_a_549_);
if (v_isSharedCheck_573_ == 0)
{
v___x_557_ = v_a_549_;
v_isShared_558_ = v_isSharedCheck_573_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_snd_555_);
lean_inc(v_fst_554_);
lean_dec(v_a_549_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_573_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
size_t v___x_559_; size_t v___x_560_; uint8_t v___x_561_; 
v___x_559_ = lean_ptr_addr(v_binderType_538_);
v___x_560_ = lean_ptr_addr(v_fst_544_);
v___x_561_ = lean_usize_dec_eq(v___x_559_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; 
lean_inc(v_binderName_537_);
lean_del_object(v___x_557_);
lean_del_object(v___x_552_);
lean_dec_ref_known(v_e_497_, 3);
v___x_562_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_537_, v_binderInfo_540_, v_fst_544_, v_fst_554_, v_snd_555_, v_a_500_, v_a_501_, v_a_550_);
return v___x_562_;
}
else
{
size_t v___x_563_; size_t v___x_564_; uint8_t v___x_565_; 
v___x_563_ = lean_ptr_addr(v_body_539_);
v___x_564_ = lean_ptr_addr(v_fst_554_);
v___x_565_ = lean_usize_dec_eq(v___x_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; 
lean_inc(v_binderName_537_);
lean_del_object(v___x_557_);
lean_del_object(v___x_552_);
lean_dec_ref_known(v_e_497_, 3);
v___x_566_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_537_, v_binderInfo_540_, v_fst_544_, v_fst_554_, v_snd_555_, v_a_500_, v_a_501_, v_a_550_);
return v___x_566_;
}
else
{
lean_object* v___x_568_; 
lean_dec(v_fst_554_);
lean_dec(v_fst_544_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v_e_497_);
v___x_568_ = v___x_557_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_e_497_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_snd_555_);
v___x_568_ = v_reuseFailAlloc_572_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_570_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_568_);
v___x_570_ = v___x_552_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_a_550_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_544_);
lean_dec_ref_known(v_e_497_, 3);
return v___x_548_;
}
}
else
{
lean_dec_ref_known(v_e_497_, 3);
lean_dec(v_offset_498_);
return v___x_541_;
}
}
case 7:
{
lean_object* v_binderName_575_; lean_object* v_binderType_576_; lean_object* v_body_577_; uint8_t v_binderInfo_578_; lean_object* v___x_579_; 
v_binderName_575_ = lean_ctor_get(v_e_497_, 0);
v_binderType_576_ = lean_ctor_get(v_e_497_, 1);
v_body_577_ = lean_ctor_get(v_e_497_, 2);
v_binderInfo_578_ = lean_ctor_get_uint8(v_e_497_, sizeof(void*)*3 + 8);
lean_inc(v_offset_498_);
lean_inc_ref(v_binderType_576_);
v___x_579_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_495_, v_d_496_, v_binderType_576_, v_offset_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v_a_581_; lean_object* v_fst_582_; lean_object* v_snd_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_580_);
v_a_581_ = lean_ctor_get(v___x_579_, 1);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_579_, 2);
v_fst_582_ = lean_ctor_get(v_a_580_, 0);
lean_inc(v_fst_582_);
v_snd_583_ = lean_ctor_get(v_a_580_, 1);
lean_inc(v_snd_583_);
lean_dec(v_a_580_);
v___x_584_ = lean_unsigned_to_nat(1u);
v___x_585_ = lean_nat_add(v_offset_498_, v___x_584_);
lean_dec(v_offset_498_);
lean_inc_ref(v_body_577_);
v___x_586_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_495_, v_d_496_, v_body_577_, v___x_585_, v_snd_583_, v_a_500_, v_a_501_, v_a_581_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_612_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
v_a_588_ = lean_ctor_get(v___x_586_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_612_ == 0)
{
v___x_590_ = v___x_586_;
v_isShared_591_ = v_isSharedCheck_612_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_612_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v_fst_592_; lean_object* v_snd_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_611_; 
v_fst_592_ = lean_ctor_get(v_a_587_, 0);
v_snd_593_ = lean_ctor_get(v_a_587_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_a_587_);
if (v_isSharedCheck_611_ == 0)
{
v___x_595_ = v_a_587_;
v_isShared_596_ = v_isSharedCheck_611_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_snd_593_);
lean_inc(v_fst_592_);
lean_dec(v_a_587_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_611_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
size_t v___x_597_; size_t v___x_598_; uint8_t v___x_599_; 
v___x_597_ = lean_ptr_addr(v_binderType_576_);
v___x_598_ = lean_ptr_addr(v_fst_582_);
v___x_599_ = lean_usize_dec_eq(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
lean_inc(v_binderName_575_);
lean_del_object(v___x_595_);
lean_del_object(v___x_590_);
lean_dec_ref_known(v_e_497_, 3);
v___x_600_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_575_, v_binderInfo_578_, v_fst_582_, v_fst_592_, v_snd_593_, v_a_500_, v_a_501_, v_a_588_);
return v___x_600_;
}
else
{
size_t v___x_601_; size_t v___x_602_; uint8_t v___x_603_; 
v___x_601_ = lean_ptr_addr(v_body_577_);
v___x_602_ = lean_ptr_addr(v_fst_592_);
v___x_603_ = lean_usize_dec_eq(v___x_601_, v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
lean_inc(v_binderName_575_);
lean_del_object(v___x_595_);
lean_del_object(v___x_590_);
lean_dec_ref_known(v_e_497_, 3);
v___x_604_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_575_, v_binderInfo_578_, v_fst_582_, v_fst_592_, v_snd_593_, v_a_500_, v_a_501_, v_a_588_);
return v___x_604_;
}
else
{
lean_object* v___x_606_; 
lean_dec(v_fst_592_);
lean_dec(v_fst_582_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v_e_497_);
v___x_606_ = v___x_595_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_e_497_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_snd_593_);
v___x_606_ = v_reuseFailAlloc_610_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_608_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_606_);
v___x_608_ = v___x_590_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_a_588_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_582_);
lean_dec_ref_known(v_e_497_, 3);
return v___x_586_;
}
}
else
{
lean_dec_ref_known(v_e_497_, 3);
lean_dec(v_offset_498_);
return v___x_579_;
}
}
case 8:
{
lean_object* v_declName_613_; lean_object* v_type_614_; lean_object* v_value_615_; lean_object* v_body_616_; uint8_t v_nondep_617_; lean_object* v___x_618_; 
v_declName_613_ = lean_ctor_get(v_e_497_, 0);
v_type_614_ = lean_ctor_get(v_e_497_, 1);
v_value_615_ = lean_ctor_get(v_e_497_, 2);
v_body_616_ = lean_ctor_get(v_e_497_, 3);
v_nondep_617_ = lean_ctor_get_uint8(v_e_497_, sizeof(void*)*4 + 8);
lean_inc(v_offset_498_);
lean_inc_ref(v_type_614_);
v___x_618_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_495_, v_d_496_, v_type_614_, v_offset_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v_a_620_; lean_object* v_fst_621_; lean_object* v_snd_622_; lean_object* v___x_623_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
v_a_620_ = lean_ctor_get(v___x_618_, 1);
lean_inc(v_a_620_);
lean_dec_ref_known(v___x_618_, 2);
v_fst_621_ = lean_ctor_get(v_a_619_, 0);
lean_inc(v_fst_621_);
v_snd_622_ = lean_ctor_get(v_a_619_, 1);
lean_inc(v_snd_622_);
lean_dec(v_a_619_);
lean_inc(v_offset_498_);
lean_inc_ref(v_value_615_);
v___x_623_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_495_, v_d_496_, v_value_615_, v_offset_498_, v_snd_622_, v_a_500_, v_a_501_, v_a_620_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v_a_625_; lean_object* v_fst_626_; lean_object* v_snd_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
v_a_625_ = lean_ctor_get(v___x_623_, 1);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_623_, 2);
v_fst_626_ = lean_ctor_get(v_a_624_, 0);
lean_inc(v_fst_626_);
v_snd_627_ = lean_ctor_get(v_a_624_, 1);
lean_inc(v_snd_627_);
lean_dec(v_a_624_);
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = lean_nat_add(v_offset_498_, v___x_628_);
lean_dec(v_offset_498_);
lean_inc_ref(v_body_616_);
v___x_630_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_495_, v_d_496_, v_body_616_, v___x_629_, v_snd_627_, v_a_500_, v_a_501_, v_a_625_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_660_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
v_a_632_ = lean_ctor_get(v___x_630_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_660_ == 0)
{
v___x_634_ = v___x_630_;
v_isShared_635_ = v_isSharedCheck_660_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_inc(v_a_631_);
lean_dec(v___x_630_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_660_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v_fst_636_; lean_object* v_snd_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_659_; 
v_fst_636_ = lean_ctor_get(v_a_631_, 0);
v_snd_637_ = lean_ctor_get(v_a_631_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v_a_631_);
if (v_isSharedCheck_659_ == 0)
{
v___x_639_ = v_a_631_;
v_isShared_640_ = v_isSharedCheck_659_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_snd_637_);
lean_inc(v_fst_636_);
lean_dec(v_a_631_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_659_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
size_t v___x_641_; size_t v___x_642_; uint8_t v___x_643_; 
v___x_641_ = lean_ptr_addr(v_type_614_);
v___x_642_ = lean_ptr_addr(v_fst_621_);
v___x_643_ = lean_usize_dec_eq(v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
lean_inc(v_declName_613_);
lean_del_object(v___x_639_);
lean_del_object(v___x_634_);
lean_dec_ref_known(v_e_497_, 4);
v___x_644_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_613_, v_fst_621_, v_fst_626_, v_fst_636_, v_nondep_617_, v_snd_637_, v_a_500_, v_a_501_, v_a_632_);
return v___x_644_;
}
else
{
size_t v___x_645_; size_t v___x_646_; uint8_t v___x_647_; 
v___x_645_ = lean_ptr_addr(v_value_615_);
v___x_646_ = lean_ptr_addr(v_fst_626_);
v___x_647_ = lean_usize_dec_eq(v___x_645_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; 
lean_inc(v_declName_613_);
lean_del_object(v___x_639_);
lean_del_object(v___x_634_);
lean_dec_ref_known(v_e_497_, 4);
v___x_648_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_613_, v_fst_621_, v_fst_626_, v_fst_636_, v_nondep_617_, v_snd_637_, v_a_500_, v_a_501_, v_a_632_);
return v___x_648_;
}
else
{
size_t v___x_649_; size_t v___x_650_; uint8_t v___x_651_; 
v___x_649_ = lean_ptr_addr(v_body_616_);
v___x_650_ = lean_ptr_addr(v_fst_636_);
v___x_651_ = lean_usize_dec_eq(v___x_649_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
lean_inc(v_declName_613_);
lean_del_object(v___x_639_);
lean_del_object(v___x_634_);
lean_dec_ref_known(v_e_497_, 4);
v___x_652_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_613_, v_fst_621_, v_fst_626_, v_fst_636_, v_nondep_617_, v_snd_637_, v_a_500_, v_a_501_, v_a_632_);
return v___x_652_;
}
else
{
lean_object* v___x_654_; 
lean_dec(v_fst_636_);
lean_dec(v_fst_626_);
lean_dec(v_fst_621_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v_e_497_);
v___x_654_ = v___x_639_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_e_497_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_snd_637_);
v___x_654_ = v_reuseFailAlloc_658_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_656_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_654_);
v___x_656_ = v___x_634_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_a_632_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
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
lean_dec(v_fst_626_);
lean_dec(v_fst_621_);
lean_dec_ref_known(v_e_497_, 4);
return v___x_630_;
}
}
else
{
lean_dec(v_fst_621_);
lean_dec_ref_known(v_e_497_, 4);
lean_dec(v_offset_498_);
return v___x_623_;
}
}
else
{
lean_dec_ref_known(v_e_497_, 4);
lean_dec(v_offset_498_);
return v___x_618_;
}
}
case 10:
{
lean_object* v_data_661_; lean_object* v_expr_662_; lean_object* v___x_663_; 
v_data_661_ = lean_ctor_get(v_e_497_, 0);
v_expr_662_ = lean_ctor_get(v_e_497_, 1);
lean_inc_ref(v_expr_662_);
v___x_663_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_495_, v_d_496_, v_expr_662_, v_offset_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_685_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_a_665_ = lean_ctor_get(v___x_663_, 1);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_685_ == 0)
{
v___x_667_ = v___x_663_;
v_isShared_668_ = v_isSharedCheck_685_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_685_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_fst_669_; lean_object* v_snd_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_684_; 
v_fst_669_ = lean_ctor_get(v_a_664_, 0);
v_snd_670_ = lean_ctor_get(v_a_664_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_a_664_);
if (v_isSharedCheck_684_ == 0)
{
v___x_672_ = v_a_664_;
v_isShared_673_ = v_isSharedCheck_684_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_snd_670_);
lean_inc(v_fst_669_);
lean_dec(v_a_664_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_684_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
size_t v___x_674_; size_t v___x_675_; uint8_t v___x_676_; 
v___x_674_ = lean_ptr_addr(v_expr_662_);
v___x_675_ = lean_ptr_addr(v_fst_669_);
v___x_676_ = lean_usize_dec_eq(v___x_674_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
lean_inc(v_data_661_);
lean_del_object(v___x_672_);
lean_del_object(v___x_667_);
lean_dec_ref_known(v_e_497_, 2);
v___x_677_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_661_, v_fst_669_, v_snd_670_, v_a_500_, v_a_501_, v_a_665_);
return v___x_677_;
}
else
{
lean_object* v___x_679_; 
lean_dec(v_fst_669_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v_e_497_);
v___x_679_ = v___x_672_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_e_497_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_snd_670_);
v___x_679_ = v_reuseFailAlloc_683_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_681_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_679_);
v___x_681_ = v___x_667_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_a_665_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_497_, 2);
return v___x_663_;
}
}
case 11:
{
lean_object* v_typeName_686_; lean_object* v_idx_687_; lean_object* v_struct_688_; lean_object* v___x_689_; 
v_typeName_686_ = lean_ctor_get(v_e_497_, 0);
v_idx_687_ = lean_ctor_get(v_e_497_, 1);
v_struct_688_ = lean_ctor_get(v_e_497_, 2);
lean_inc_ref(v_struct_688_);
v___x_689_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_495_, v_d_496_, v_struct_688_, v_offset_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_711_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_a_691_ = lean_ctor_get(v___x_689_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_711_ == 0)
{
v___x_693_ = v___x_689_;
v_isShared_694_ = v_isSharedCheck_711_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_711_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_fst_695_; lean_object* v_snd_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_710_; 
v_fst_695_ = lean_ctor_get(v_a_690_, 0);
v_snd_696_ = lean_ctor_get(v_a_690_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_a_690_);
if (v_isSharedCheck_710_ == 0)
{
v___x_698_ = v_a_690_;
v_isShared_699_ = v_isSharedCheck_710_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_snd_696_);
lean_inc(v_fst_695_);
lean_dec(v_a_690_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_710_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
size_t v___x_700_; size_t v___x_701_; uint8_t v___x_702_; 
v___x_700_ = lean_ptr_addr(v_struct_688_);
v___x_701_ = lean_ptr_addr(v_fst_695_);
v___x_702_ = lean_usize_dec_eq(v___x_700_, v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; 
lean_inc(v_idx_687_);
lean_inc(v_typeName_686_);
lean_del_object(v___x_698_);
lean_del_object(v___x_693_);
lean_dec_ref_known(v_e_497_, 3);
v___x_703_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_686_, v_idx_687_, v_fst_695_, v_snd_696_, v_a_500_, v_a_501_, v_a_691_);
return v___x_703_;
}
else
{
lean_object* v___x_705_; 
lean_dec(v_fst_695_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v_e_497_);
v___x_705_ = v___x_698_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_e_497_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_snd_696_);
v___x_705_ = v_reuseFailAlloc_709_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_707_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_705_);
v___x_707_ = v___x_693_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_a_691_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_497_, 3);
return v___x_689_;
}
}
default: 
{
lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec(v_offset_498_);
lean_dec_ref(v_e_497_);
v___x_712_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
v___x_713_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_712_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
return v___x_713_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_495_ = stack[0].m_obj;
lean_object* v_d_496_ = stack[1].m_obj;
lean_object* v_e_497_ = stack[2].m_obj;
lean_object* v_offset_498_ = stack[3].m_obj;
lean_object* v_a_499_ = stack[4].m_obj;
uint8_t v_a_500_ = stack[5].m_num;
lean_object* v_a_501_ = stack[6].m_obj;
lean_object* v_a_502_ = stack[7].m_obj;
lean_object* v_res_714_;
v_res_714_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_495_, v_d_496_, v_e_497_, v_offset_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
stack->m_obj
 = v_res_714_;
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(lean_object* v_s_715_, lean_object* v_d_716_, lean_object* v_e_717_, lean_object* v_offset_718_, lean_object* v_a_719_, uint8_t v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_key_723_; lean_object* v_a_725_; lean_object* v___x_738_; 
lean_inc(v_offset_718_);
lean_inc_ref(v_e_717_);
v_key_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_723_, 0, v_e_717_);
lean_ctor_set(v_key_723_, 1, v_offset_718_);
v___x_738_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_719_, v_key_723_);
if (lean_obj_tag(v___x_738_) == 1)
{
lean_object* v_val_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec_ref_known(v_key_723_, 2);
lean_dec(v_offset_718_);
lean_dec_ref(v_e_717_);
v_val_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v_val_739_);
lean_ctor_set(v___x_740_, 1, v_a_719_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v_a_722_);
return v___x_741_;
}
else
{
lean_object* v_s_u2081_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
lean_dec(v___x_738_);
v_s_u2081_742_ = lean_nat_add(v_s_715_, v_offset_718_);
v___x_743_ = l_Lean_Expr_looseBVarRange(v_e_717_);
v___x_744_ = lean_nat_dec_le(v___x_743_, v_s_u2081_742_);
lean_dec(v___x_743_);
if (v___x_744_ == 0)
{
if (lean_obj_tag(v_e_717_) == 0)
{
lean_object* v_deBruijnIndex_745_; uint8_t v___x_746_; 
v_deBruijnIndex_745_ = lean_ctor_get(v_e_717_, 0);
v___x_746_ = lean_nat_dec_le(v_s_u2081_742_, v_deBruijnIndex_745_);
lean_dec(v_s_u2081_742_);
if (v___x_746_ == 0)
{
v_a_725_ = v_a_722_;
goto v___jp_724_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_inc(v_deBruijnIndex_745_);
lean_dec_ref_known(v_e_717_, 1);
lean_dec(v_offset_718_);
v___x_747_ = lean_nat_sub(v_deBruijnIndex_745_, v_d_716_);
lean_dec(v_deBruijnIndex_745_);
v___x_748_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_747_, v_a_722_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v_a_750_; lean_object* v___x_751_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
v_a_750_ = lean_ctor_get(v___x_748_, 1);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_748_, 2);
v___x_751_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_723_, v_a_749_, v_a_719_, v_a_720_, v_a_721_, v_a_750_);
return v___x_751_;
}
else
{
lean_object* v_a_752_; lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec_ref_known(v_key_723_, 2);
lean_dec_ref(v_a_719_);
v_a_752_ = lean_ctor_get(v___x_748_, 0);
v_a_753_ = lean_ctor_get(v___x_748_, 1);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_748_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_inc(v_a_752_);
lean_dec(v___x_748_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_752_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
else
{
lean_dec(v_s_u2081_742_);
v_a_725_ = v_a_722_;
goto v___jp_724_;
}
}
else
{
lean_object* v___x_761_; 
lean_dec(v_s_u2081_742_);
lean_dec(v_offset_718_);
v___x_761_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_723_, v_e_717_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
return v___x_761_;
}
}
v___jp_724_:
{
switch(lean_obj_tag(v_e_717_))
{
case 9:
{
lean_object* v___x_726_; 
lean_dec(v_offset_718_);
v___x_726_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_723_, v_e_717_, v_a_719_, v_a_720_, v_a_721_, v_a_725_);
return v___x_726_;
}
case 2:
{
lean_object* v___x_727_; 
lean_dec(v_offset_718_);
v___x_727_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_723_, v_e_717_, v_a_719_, v_a_720_, v_a_721_, v_a_725_);
return v___x_727_;
}
case 0:
{
lean_object* v___x_728_; 
lean_dec(v_offset_718_);
v___x_728_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_723_, v_e_717_, v_a_719_, v_a_720_, v_a_721_, v_a_725_);
return v___x_728_;
}
case 1:
{
lean_object* v___x_729_; 
lean_dec(v_offset_718_);
v___x_729_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_723_, v_e_717_, v_a_719_, v_a_720_, v_a_721_, v_a_725_);
return v___x_729_;
}
case 4:
{
lean_object* v___x_730_; 
lean_dec(v_offset_718_);
v___x_730_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_723_, v_e_717_, v_a_719_, v_a_720_, v_a_721_, v_a_725_);
return v___x_730_;
}
case 3:
{
lean_object* v___x_731_; 
lean_dec(v_offset_718_);
v___x_731_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_723_, v_e_717_, v_a_719_, v_a_720_, v_a_721_, v_a_725_);
return v___x_731_;
}
default: 
{
lean_object* v___x_732_; 
v___x_732_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_715_, v_d_716_, v_e_717_, v_offset_718_, v_a_719_, v_a_720_, v_a_721_, v_a_725_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v_a_734_; lean_object* v_fst_735_; lean_object* v_snd_736_; lean_object* v___x_737_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
v_a_734_ = lean_ctor_get(v___x_732_, 1);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_732_, 2);
v_fst_735_ = lean_ctor_get(v_a_733_, 0);
lean_inc(v_fst_735_);
v_snd_736_ = lean_ctor_get(v_a_733_, 1);
lean_inc(v_snd_736_);
lean_dec(v_a_733_);
v___x_737_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_723_, v_fst_735_, v_snd_736_, v_a_720_, v_a_721_, v_a_734_);
return v___x_737_;
}
else
{
lean_dec_ref_known(v_key_723_, 2);
return v___x_732_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_715_ = stack[0].m_obj;
lean_object* v_d_716_ = stack[1].m_obj;
lean_object* v_e_717_ = stack[2].m_obj;
lean_object* v_offset_718_ = stack[3].m_obj;
lean_object* v_a_719_ = stack[4].m_obj;
uint8_t v_a_720_ = stack[5].m_num;
lean_object* v_a_721_ = stack[6].m_obj;
lean_object* v_a_722_ = stack[7].m_obj;
lean_object* v_res_762_;
v_res_762_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_715_, v_d_716_, v_e_717_, v_offset_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
stack->m_obj
 = v_res_762_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1___boxed(lean_object* v_s_763_, lean_object* v_d_764_, lean_object* v_e_765_, lean_object* v_offset_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
uint8_t v_a_boxed_771_; lean_object* v_res_772_; 
v_a_boxed_771_ = lean_unbox(v_a_768_);
v_res_772_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_763_, v_d_764_, v_e_765_, v_offset_766_, v_a_767_, v_a_boxed_771_, v_a_769_, v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_d_764_);
lean_dec(v_s_763_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___boxed(lean_object* v_s_773_, lean_object* v_d_774_, lean_object* v_e_775_, lean_object* v_offset_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
uint8_t v_a_boxed_781_; lean_object* v_res_782_; 
v_a_boxed_781_ = lean_unbox(v_a_778_);
v_res_782_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_773_, v_d_774_, v_e_775_, v_offset_776_, v_a_777_, v_a_boxed_781_, v_a_779_, v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_d_774_);
lean_dec(v_s_773_);
return v_res_782_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_783_ = lean_box(0);
v___x_784_ = lean_unsigned_to_nat(16u);
v___x_785_ = lean_mk_array(v___x_784_, v___x_783_);
return v___x_785_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0);
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v___x_786_);
return v___x_788_;
}
}
lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27(lean_object* v_e_789_, lean_object* v_s_790_, lean_object* v_d_791_, uint8_t v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_795_ = l_Lean_Expr_looseBVarRange(v_e_789_);
v___x_796_ = lean_nat_dec_le(v___x_795_, v_s_790_);
lean_dec(v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v_a_799_; 
v___x_797_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_e_789_) == 0)
{
lean_object* v_deBruijnIndex_827_; uint8_t v___x_828_; 
v_deBruijnIndex_827_ = lean_ctor_get(v_e_789_, 0);
v___x_828_ = lean_nat_dec_le(v_s_790_, v_deBruijnIndex_827_);
if (v___x_828_ == 0)
{
v_a_799_ = v_a_794_;
goto v___jp_798_;
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; 
lean_inc(v_deBruijnIndex_827_);
lean_dec_ref_known(v_e_789_, 1);
v___x_829_ = lean_nat_sub(v_deBruijnIndex_827_, v_d_791_);
lean_dec(v_deBruijnIndex_827_);
v___x_830_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_829_, v_a_794_);
return v___x_830_;
}
}
else
{
v_a_799_ = v_a_794_;
goto v___jp_798_;
}
v___jp_798_:
{
switch(lean_obj_tag(v_e_789_))
{
case 9:
{
lean_object* v___x_800_; 
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_e_789_);
lean_ctor_set(v___x_800_, 1, v_a_799_);
return v___x_800_;
}
case 2:
{
lean_object* v___x_801_; 
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v_e_789_);
lean_ctor_set(v___x_801_, 1, v_a_799_);
return v___x_801_;
}
case 0:
{
lean_object* v___x_802_; 
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v_e_789_);
lean_ctor_set(v___x_802_, 1, v_a_799_);
return v___x_802_;
}
case 1:
{
lean_object* v___x_803_; 
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v_e_789_);
lean_ctor_set(v___x_803_, 1, v_a_799_);
return v___x_803_;
}
case 4:
{
lean_object* v___x_804_; 
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v_e_789_);
lean_ctor_set(v___x_804_, 1, v_a_799_);
return v___x_804_;
}
case 3:
{
lean_object* v___x_805_; 
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v_e_789_);
lean_ctor_set(v___x_805_, 1, v_a_799_);
return v___x_805_;
}
default: 
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1);
v___x_807_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_790_, v_d_791_, v_e_789_, v___x_797_, v___x_806_, v_a_792_, v_a_793_, v_a_799_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_817_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_a_809_ = lean_ctor_get(v___x_807_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_817_ == 0)
{
v___x_811_ = v___x_807_;
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v_fst_813_; lean_object* v___x_815_; 
v_fst_813_ = lean_ctor_get(v_a_808_, 0);
lean_inc(v_fst_813_);
lean_dec(v_a_808_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v_fst_813_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_fst_813_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_a_809_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
else
{
lean_object* v_a_818_; lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
v_a_818_ = lean_ctor_get(v___x_807_, 0);
v_a_819_ = lean_ctor_get(v___x_807_, 1);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_807_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_inc(v_a_818_);
lean_dec(v___x_807_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_818_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_831_; 
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_e_789_);
lean_ctor_set(v___x_831_, 1, v_a_794_);
return v___x_831_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_lowerLooseBVarsS_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_789_ = stack[0].m_obj;
lean_object* v_s_790_ = stack[1].m_obj;
lean_object* v_d_791_ = stack[2].m_obj;
uint8_t v_a_792_ = stack[3].m_num;
lean_object* v_a_793_ = stack[4].m_obj;
lean_object* v_a_794_ = stack[5].m_obj;
lean_object* v_res_832_;
v_res_832_ = l_Lean_Meta_Sym_lowerLooseBVarsS_x27(v_e_789_, v_s_790_, v_d_791_, v_a_792_, v_a_793_, v_a_794_);
stack->m_obj
 = v_res_832_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed(lean_object* v_e_833_, lean_object* v_s_834_, lean_object* v_d_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
uint8_t v_a_boxed_839_; lean_object* v_res_840_; 
v_a_boxed_839_ = lean_unbox(v_a_836_);
v_res_840_ = l_Lean_Meta_Sym_lowerLooseBVarsS_x27(v_e_833_, v_s_834_, v_d_835_, v_a_boxed_839_, v_a_837_, v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_d_835_);
lean_dec(v_s_834_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_841_, lean_object* v_m_842_, lean_object* v_a_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_842_, v_a_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_845_, lean_object* v_m_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(v_00_u03b2_845_, v_m_846_, v_a_847_);
lean_dec_ref(v_a_847_);
lean_dec_ref(v_m_846_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(lean_object* v_00_u03b2_849_, lean_object* v_a_850_, lean_object* v_x_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_850_, v_x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___boxed(lean_object* v_00_u03b2_853_, lean_object* v_a_854_, lean_object* v_x_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(v_00_u03b2_853_, v_a_854_, v_x_855_);
lean_dec(v_x_855_);
lean_dec_ref(v_a_854_);
return v_res_856_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0(void){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_857_;
}
}
lean_object* l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(lean_object* v_msg_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; lean_object* v___x_44__overap_867_; lean_object* v___x_868_; 
v___x_866_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0);
v___x_44__overap_867_ = lean_panic_fn_borrowed(v___x_866_, v_msg_858_);
lean_inc(v___y_864_);
lean_inc_ref(v___y_863_);
lean_inc(v___y_862_);
lean_inc_ref(v___y_861_);
lean_inc(v___y_860_);
lean_inc_ref(v___y_859_);
v___x_868_ = lean_apply_7(v___x_44__overap_867_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, lean_box(0));
return v___x_868_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_858_ = stack[0].m_obj;
lean_object* v___y_859_ = stack[1].m_obj;
lean_object* v___y_860_ = stack[2].m_obj;
lean_object* v___y_861_ = stack[3].m_obj;
lean_object* v___y_862_ = stack[4].m_obj;
lean_object* v___y_863_ = stack[5].m_obj;
lean_object* v___y_864_ = stack[6].m_obj;
lean_object* v_res_869_;
v_res_869_ = l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(v_msg_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
stack->m_obj
 = v_res_869_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___boxed(lean_object* v_msg_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(v_msg_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
return v_res_878_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_881_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2));
v___x_882_ = lean_unsigned_to_nat(16u);
v___x_883_ = lean_unsigned_to_nat(62u);
v___x_884_ = ((lean_object*)(l_Lean_Meta_Sym_lowerLooseBVarsS___closed__1));
v___x_885_ = ((lean_object*)(l_Lean_Meta_Sym_lowerLooseBVarsS___closed__0));
v___x_886_ = l_mkPanicMessageWithDecl(v___x_885_, v___x_884_, v___x_883_, v___x_882_, v___x_881_);
return v___x_886_;
}
}
lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS(lean_object* v_e_887_, lean_object* v_s_888_, lean_object* v_d_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v___x_897_; uint8_t v_debug_898_; lean_object* v___x_899_; lean_object* v_env_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_897_ = lean_st_ref_get(v_a_891_);
v_debug_898_ = lean_ctor_get_uint8(v___x_897_, sizeof(void*)*12);
lean_dec(v___x_897_);
v___x_899_ = lean_st_ref_get(v_a_895_);
v_env_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc_ref(v_env_900_);
lean_dec(v___x_899_);
v___x_901_ = lean_box(v_debug_898_);
v___x_902_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed), 6, 4);
lean_closure_set(v___x_902_, 0, v_e_887_);
lean_closure_set(v___x_902_, 1, v_s_888_);
lean_closure_set(v___x_902_, 2, v_d_889_);
lean_closure_set(v___x_902_, 3, v___x_901_);
v___x_903_ = 0;
v___x_904_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_904_, 0, v_env_900_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*1, v___x_903_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*1 + 1, v___x_903_);
v___x_905_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_902_, v___x_904_, v_a_891_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_916_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_916_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_916_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_916_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
if (lean_obj_tag(v_a_906_) == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; 
lean_dec_ref_known(v_a_906_, 1);
lean_del_object(v___x_908_);
v___x_910_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2, &l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2);
v___x_911_ = l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(v___x_910_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
return v___x_911_;
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; 
v_a_912_ = lean_ctor_get(v_a_906_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v_a_906_, 1);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v_a_912_);
v___x_914_ = v___x_908_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
v_a_917_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_905_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_905_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_lowerLooseBVarsS_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_887_ = stack[0].m_obj;
lean_object* v_s_888_ = stack[1].m_obj;
lean_object* v_d_889_ = stack[2].m_obj;
lean_object* v_a_890_ = stack[3].m_obj;
lean_object* v_a_891_ = stack[4].m_obj;
lean_object* v_a_892_ = stack[5].m_obj;
lean_object* v_a_893_ = stack[6].m_obj;
lean_object* v_a_894_ = stack[7].m_obj;
lean_object* v_a_895_ = stack[8].m_obj;
lean_object* v_res_925_;
v_res_925_ = l_Lean_Meta_Sym_lowerLooseBVarsS(v_e_887_, v_s_888_, v_d_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
stack->m_obj
 = v_res_925_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___boxed(lean_object* v_e_926_, lean_object* v_s_927_, lean_object* v_d_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Meta_Sym_lowerLooseBVarsS(v_e_926_, v_s_927_, v_d_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
return v_res_936_;
}
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(lean_object* v_s_937_, lean_object* v_d_938_, lean_object* v_e_939_, lean_object* v_offset_940_, lean_object* v_a_941_, uint8_t v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
switch(lean_obj_tag(v_e_939_))
{
case 5:
{
lean_object* v_fn_945_; lean_object* v_arg_946_; lean_object* v___x_947_; 
v_fn_945_ = lean_ctor_get(v_e_939_, 0);
v_arg_946_ = lean_ctor_get(v_e_939_, 1);
lean_inc(v_offset_940_);
lean_inc_ref(v_fn_945_);
v___x_947_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_937_, v_d_938_, v_fn_945_, v_offset_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v_a_949_; lean_object* v_fst_950_; lean_object* v_snd_951_; lean_object* v___x_952_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
v_a_949_ = lean_ctor_get(v___x_947_, 1);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_947_, 2);
v_fst_950_ = lean_ctor_get(v_a_948_, 0);
lean_inc(v_fst_950_);
v_snd_951_ = lean_ctor_get(v_a_948_, 1);
lean_inc(v_snd_951_);
lean_dec(v_a_948_);
lean_inc_ref(v_arg_946_);
v___x_952_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_937_, v_d_938_, v_arg_946_, v_offset_940_, v_snd_951_, v_a_942_, v_a_943_, v_a_949_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_978_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_a_954_ = lean_ctor_get(v___x_952_, 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_978_ == 0)
{
v___x_956_ = v___x_952_;
v_isShared_957_ = v_isSharedCheck_978_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_978_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_fst_958_; lean_object* v_snd_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_977_; 
v_fst_958_ = lean_ctor_get(v_a_953_, 0);
v_snd_959_ = lean_ctor_get(v_a_953_, 1);
v_isSharedCheck_977_ = !lean_is_exclusive(v_a_953_);
if (v_isSharedCheck_977_ == 0)
{
v___x_961_ = v_a_953_;
v_isShared_962_ = v_isSharedCheck_977_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_snd_959_);
lean_inc(v_fst_958_);
lean_dec(v_a_953_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_977_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
size_t v___x_963_; size_t v___x_964_; uint8_t v___x_965_; 
v___x_963_ = lean_ptr_addr(v_fn_945_);
v___x_964_ = lean_ptr_addr(v_fst_950_);
v___x_965_ = lean_usize_dec_eq(v___x_963_, v___x_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; 
lean_del_object(v___x_961_);
lean_del_object(v___x_956_);
lean_dec_ref_known(v_e_939_, 2);
v___x_966_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_950_, v_fst_958_, v_snd_959_, v_a_942_, v_a_943_, v_a_954_);
return v___x_966_;
}
else
{
size_t v___x_967_; size_t v___x_968_; uint8_t v___x_969_; 
v___x_967_ = lean_ptr_addr(v_arg_946_);
v___x_968_ = lean_ptr_addr(v_fst_958_);
v___x_969_ = lean_usize_dec_eq(v___x_967_, v___x_968_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; 
lean_del_object(v___x_961_);
lean_del_object(v___x_956_);
lean_dec_ref_known(v_e_939_, 2);
v___x_970_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_950_, v_fst_958_, v_snd_959_, v_a_942_, v_a_943_, v_a_954_);
return v___x_970_;
}
else
{
lean_object* v___x_972_; 
lean_dec(v_fst_958_);
lean_dec(v_fst_950_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v_e_939_);
v___x_972_ = v___x_961_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_e_939_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_snd_959_);
v___x_972_ = v_reuseFailAlloc_976_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_974_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_972_);
v___x_974_ = v___x_956_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_a_954_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_950_);
lean_dec_ref_known(v_e_939_, 2);
return v___x_952_;
}
}
else
{
lean_dec_ref_known(v_e_939_, 2);
lean_dec(v_offset_940_);
return v___x_947_;
}
}
case 6:
{
lean_object* v_binderName_979_; lean_object* v_binderType_980_; lean_object* v_body_981_; uint8_t v_binderInfo_982_; lean_object* v___x_983_; 
v_binderName_979_ = lean_ctor_get(v_e_939_, 0);
v_binderType_980_ = lean_ctor_get(v_e_939_, 1);
v_body_981_ = lean_ctor_get(v_e_939_, 2);
v_binderInfo_982_ = lean_ctor_get_uint8(v_e_939_, sizeof(void*)*3 + 8);
lean_inc(v_offset_940_);
lean_inc_ref(v_binderType_980_);
v___x_983_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_937_, v_d_938_, v_binderType_980_, v_offset_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v_a_985_; lean_object* v_fst_986_; lean_object* v_snd_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
v_a_985_ = lean_ctor_get(v___x_983_, 1);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_983_, 2);
v_fst_986_ = lean_ctor_get(v_a_984_, 0);
lean_inc(v_fst_986_);
v_snd_987_ = lean_ctor_get(v_a_984_, 1);
lean_inc(v_snd_987_);
lean_dec(v_a_984_);
v___x_988_ = lean_unsigned_to_nat(1u);
v___x_989_ = lean_nat_add(v_offset_940_, v___x_988_);
lean_dec(v_offset_940_);
lean_inc_ref(v_body_981_);
v___x_990_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_937_, v_d_938_, v_body_981_, v___x_989_, v_snd_987_, v_a_942_, v_a_943_, v_a_985_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1016_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_a_992_ = lean_ctor_get(v___x_990_, 1);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_994_ = v___x_990_;
v_isShared_995_ = v_isSharedCheck_1016_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1016_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v_fst_996_; lean_object* v_snd_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1015_; 
v_fst_996_ = lean_ctor_get(v_a_991_, 0);
v_snd_997_ = lean_ctor_get(v_a_991_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_a_991_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_999_ = v_a_991_;
v_isShared_1000_ = v_isSharedCheck_1015_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_snd_997_);
lean_inc(v_fst_996_);
lean_dec(v_a_991_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1015_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
size_t v___x_1001_; size_t v___x_1002_; uint8_t v___x_1003_; 
v___x_1001_ = lean_ptr_addr(v_binderType_980_);
v___x_1002_ = lean_ptr_addr(v_fst_986_);
v___x_1003_ = lean_usize_dec_eq(v___x_1001_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
lean_inc(v_binderName_979_);
lean_del_object(v___x_999_);
lean_del_object(v___x_994_);
lean_dec_ref_known(v_e_939_, 3);
v___x_1004_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_979_, v_binderInfo_982_, v_fst_986_, v_fst_996_, v_snd_997_, v_a_942_, v_a_943_, v_a_992_);
return v___x_1004_;
}
else
{
size_t v___x_1005_; size_t v___x_1006_; uint8_t v___x_1007_; 
v___x_1005_ = lean_ptr_addr(v_body_981_);
v___x_1006_ = lean_ptr_addr(v_fst_996_);
v___x_1007_ = lean_usize_dec_eq(v___x_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
lean_inc(v_binderName_979_);
lean_del_object(v___x_999_);
lean_del_object(v___x_994_);
lean_dec_ref_known(v_e_939_, 3);
v___x_1008_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_979_, v_binderInfo_982_, v_fst_986_, v_fst_996_, v_snd_997_, v_a_942_, v_a_943_, v_a_992_);
return v___x_1008_;
}
else
{
lean_object* v___x_1010_; 
lean_dec(v_fst_996_);
lean_dec(v_fst_986_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v_e_939_);
v___x_1010_ = v___x_999_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_e_939_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_snd_997_);
v___x_1010_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1012_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_1010_);
v___x_1012_ = v___x_994_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_a_992_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_986_);
lean_dec_ref_known(v_e_939_, 3);
return v___x_990_;
}
}
else
{
lean_dec_ref_known(v_e_939_, 3);
lean_dec(v_offset_940_);
return v___x_983_;
}
}
case 7:
{
lean_object* v_binderName_1017_; lean_object* v_binderType_1018_; lean_object* v_body_1019_; uint8_t v_binderInfo_1020_; lean_object* v___x_1021_; 
v_binderName_1017_ = lean_ctor_get(v_e_939_, 0);
v_binderType_1018_ = lean_ctor_get(v_e_939_, 1);
v_body_1019_ = lean_ctor_get(v_e_939_, 2);
v_binderInfo_1020_ = lean_ctor_get_uint8(v_e_939_, sizeof(void*)*3 + 8);
lean_inc(v_offset_940_);
lean_inc_ref(v_binderType_1018_);
v___x_1021_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_937_, v_d_938_, v_binderType_1018_, v_offset_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
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
v___x_1027_ = lean_nat_add(v_offset_940_, v___x_1026_);
lean_dec(v_offset_940_);
lean_inc_ref(v_body_1019_);
v___x_1028_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_937_, v_d_938_, v_body_1019_, v___x_1027_, v_snd_1025_, v_a_942_, v_a_943_, v_a_1023_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1054_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_a_1030_ = lean_ctor_get(v___x_1028_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1032_ = v___x_1028_;
v_isShared_1033_ = v_isSharedCheck_1054_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1054_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_fst_1034_; lean_object* v_snd_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1053_; 
v_fst_1034_ = lean_ctor_get(v_a_1029_, 0);
v_snd_1035_ = lean_ctor_get(v_a_1029_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_a_1029_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1037_ = v_a_1029_;
v_isShared_1038_ = v_isSharedCheck_1053_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_snd_1035_);
lean_inc(v_fst_1034_);
lean_dec(v_a_1029_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1053_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
size_t v___x_1039_; size_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1039_ = lean_ptr_addr(v_binderType_1018_);
v___x_1040_ = lean_ptr_addr(v_fst_1024_);
v___x_1041_ = lean_usize_dec_eq(v___x_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; 
lean_inc(v_binderName_1017_);
lean_del_object(v___x_1037_);
lean_del_object(v___x_1032_);
lean_dec_ref_known(v_e_939_, 3);
v___x_1042_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_1017_, v_binderInfo_1020_, v_fst_1024_, v_fst_1034_, v_snd_1035_, v_a_942_, v_a_943_, v_a_1030_);
return v___x_1042_;
}
else
{
size_t v___x_1043_; size_t v___x_1044_; uint8_t v___x_1045_; 
v___x_1043_ = lean_ptr_addr(v_body_1019_);
v___x_1044_ = lean_ptr_addr(v_fst_1034_);
v___x_1045_ = lean_usize_dec_eq(v___x_1043_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; 
lean_inc(v_binderName_1017_);
lean_del_object(v___x_1037_);
lean_del_object(v___x_1032_);
lean_dec_ref_known(v_e_939_, 3);
v___x_1046_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_1017_, v_binderInfo_1020_, v_fst_1024_, v_fst_1034_, v_snd_1035_, v_a_942_, v_a_943_, v_a_1030_);
return v___x_1046_;
}
else
{
lean_object* v___x_1048_; 
lean_dec(v_fst_1034_);
lean_dec(v_fst_1024_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v_e_939_);
v___x_1048_ = v___x_1037_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_e_939_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_snd_1035_);
v___x_1048_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1050_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1048_);
v___x_1050_ = v___x_1032_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_a_1030_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
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
lean_dec_ref_known(v_e_939_, 3);
return v___x_1028_;
}
}
else
{
lean_dec_ref_known(v_e_939_, 3);
lean_dec(v_offset_940_);
return v___x_1021_;
}
}
case 8:
{
lean_object* v_declName_1055_; lean_object* v_type_1056_; lean_object* v_value_1057_; lean_object* v_body_1058_; uint8_t v_nondep_1059_; lean_object* v___x_1060_; 
v_declName_1055_ = lean_ctor_get(v_e_939_, 0);
v_type_1056_ = lean_ctor_get(v_e_939_, 1);
v_value_1057_ = lean_ctor_get(v_e_939_, 2);
v_body_1058_ = lean_ctor_get(v_e_939_, 3);
v_nondep_1059_ = lean_ctor_get_uint8(v_e_939_, sizeof(void*)*4 + 8);
lean_inc(v_offset_940_);
lean_inc_ref(v_type_1056_);
v___x_1060_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_937_, v_d_938_, v_type_1056_, v_offset_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v_a_1062_; lean_object* v_fst_1063_; lean_object* v_snd_1064_; lean_object* v___x_1065_; 
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
lean_inc(v_offset_940_);
lean_inc_ref(v_value_1057_);
v___x_1065_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_937_, v_d_938_, v_value_1057_, v_offset_940_, v_snd_1064_, v_a_942_, v_a_943_, v_a_1062_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v_a_1067_; lean_object* v_fst_1068_; lean_object* v_snd_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
v_a_1067_ = lean_ctor_get(v___x_1065_, 1);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1065_, 2);
v_fst_1068_ = lean_ctor_get(v_a_1066_, 0);
lean_inc(v_fst_1068_);
v_snd_1069_ = lean_ctor_get(v_a_1066_, 1);
lean_inc(v_snd_1069_);
lean_dec(v_a_1066_);
v___x_1070_ = lean_unsigned_to_nat(1u);
v___x_1071_ = lean_nat_add(v_offset_940_, v___x_1070_);
lean_dec(v_offset_940_);
lean_inc_ref(v_body_1058_);
v___x_1072_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_937_, v_d_938_, v_body_1058_, v___x_1071_, v_snd_1069_, v_a_942_, v_a_943_, v_a_1067_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1102_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_a_1074_ = lean_ctor_get(v___x_1072_, 1);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1076_ = v___x_1072_;
v_isShared_1077_ = v_isSharedCheck_1102_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1102_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v_fst_1078_; lean_object* v_snd_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1101_; 
v_fst_1078_ = lean_ctor_get(v_a_1073_, 0);
v_snd_1079_ = lean_ctor_get(v_a_1073_, 1);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_a_1073_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1081_ = v_a_1073_;
v_isShared_1082_ = v_isSharedCheck_1101_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_snd_1079_);
lean_inc(v_fst_1078_);
lean_dec(v_a_1073_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1101_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
size_t v___x_1083_; size_t v___x_1084_; uint8_t v___x_1085_; 
v___x_1083_ = lean_ptr_addr(v_type_1056_);
v___x_1084_ = lean_ptr_addr(v_fst_1063_);
v___x_1085_ = lean_usize_dec_eq(v___x_1083_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
lean_inc(v_declName_1055_);
lean_del_object(v___x_1081_);
lean_del_object(v___x_1076_);
lean_dec_ref_known(v_e_939_, 4);
v___x_1086_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1055_, v_fst_1063_, v_fst_1068_, v_fst_1078_, v_nondep_1059_, v_snd_1079_, v_a_942_, v_a_943_, v_a_1074_);
return v___x_1086_;
}
else
{
size_t v___x_1087_; size_t v___x_1088_; uint8_t v___x_1089_; 
v___x_1087_ = lean_ptr_addr(v_value_1057_);
v___x_1088_ = lean_ptr_addr(v_fst_1068_);
v___x_1089_ = lean_usize_dec_eq(v___x_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
lean_inc(v_declName_1055_);
lean_del_object(v___x_1081_);
lean_del_object(v___x_1076_);
lean_dec_ref_known(v_e_939_, 4);
v___x_1090_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1055_, v_fst_1063_, v_fst_1068_, v_fst_1078_, v_nondep_1059_, v_snd_1079_, v_a_942_, v_a_943_, v_a_1074_);
return v___x_1090_;
}
else
{
size_t v___x_1091_; size_t v___x_1092_; uint8_t v___x_1093_; 
v___x_1091_ = lean_ptr_addr(v_body_1058_);
v___x_1092_ = lean_ptr_addr(v_fst_1078_);
v___x_1093_ = lean_usize_dec_eq(v___x_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
lean_inc(v_declName_1055_);
lean_del_object(v___x_1081_);
lean_del_object(v___x_1076_);
lean_dec_ref_known(v_e_939_, 4);
v___x_1094_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1055_, v_fst_1063_, v_fst_1068_, v_fst_1078_, v_nondep_1059_, v_snd_1079_, v_a_942_, v_a_943_, v_a_1074_);
return v___x_1094_;
}
else
{
lean_object* v___x_1096_; 
lean_dec(v_fst_1078_);
lean_dec(v_fst_1068_);
lean_dec(v_fst_1063_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v_e_939_);
v___x_1096_ = v___x_1081_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_e_939_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_snd_1079_);
v___x_1096_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1098_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1096_);
v___x_1098_ = v___x_1076_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_a_1074_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
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
lean_dec(v_fst_1068_);
lean_dec(v_fst_1063_);
lean_dec_ref_known(v_e_939_, 4);
return v___x_1072_;
}
}
else
{
lean_dec(v_fst_1063_);
lean_dec_ref_known(v_e_939_, 4);
lean_dec(v_offset_940_);
return v___x_1065_;
}
}
else
{
lean_dec_ref_known(v_e_939_, 4);
lean_dec(v_offset_940_);
return v___x_1060_;
}
}
case 10:
{
lean_object* v_data_1103_; lean_object* v_expr_1104_; lean_object* v___x_1105_; 
v_data_1103_ = lean_ctor_get(v_e_939_, 0);
v_expr_1104_ = lean_ctor_get(v_e_939_, 1);
lean_inc_ref(v_expr_1104_);
v___x_1105_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_937_, v_d_938_, v_expr_1104_, v_offset_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1127_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_a_1107_ = lean_ctor_get(v___x_1105_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1109_ = v___x_1105_;
v_isShared_1110_ = v_isSharedCheck_1127_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1127_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_fst_1111_; lean_object* v_snd_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1126_; 
v_fst_1111_ = lean_ctor_get(v_a_1106_, 0);
v_snd_1112_ = lean_ctor_get(v_a_1106_, 1);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_a_1106_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1114_ = v_a_1106_;
v_isShared_1115_ = v_isSharedCheck_1126_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_snd_1112_);
lean_inc(v_fst_1111_);
lean_dec(v_a_1106_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1126_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
size_t v___x_1116_; size_t v___x_1117_; uint8_t v___x_1118_; 
v___x_1116_ = lean_ptr_addr(v_expr_1104_);
v___x_1117_ = lean_ptr_addr(v_fst_1111_);
v___x_1118_ = lean_usize_dec_eq(v___x_1116_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
lean_inc(v_data_1103_);
lean_del_object(v___x_1114_);
lean_del_object(v___x_1109_);
lean_dec_ref_known(v_e_939_, 2);
v___x_1119_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_1103_, v_fst_1111_, v_snd_1112_, v_a_942_, v_a_943_, v_a_1107_);
return v___x_1119_;
}
else
{
lean_object* v___x_1121_; 
lean_dec(v_fst_1111_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v_e_939_);
v___x_1121_ = v___x_1114_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_e_939_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_snd_1112_);
v___x_1121_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1123_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1121_);
v___x_1123_ = v___x_1109_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_a_1107_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_939_, 2);
return v___x_1105_;
}
}
case 11:
{
lean_object* v_typeName_1128_; lean_object* v_idx_1129_; lean_object* v_struct_1130_; lean_object* v___x_1131_; 
v_typeName_1128_ = lean_ctor_get(v_e_939_, 0);
v_idx_1129_ = lean_ctor_get(v_e_939_, 1);
v_struct_1130_ = lean_ctor_get(v_e_939_, 2);
lean_inc_ref(v_struct_1130_);
v___x_1131_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_937_, v_d_938_, v_struct_1130_, v_offset_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1153_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_a_1133_ = lean_ctor_get(v___x_1131_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1135_ = v___x_1131_;
v_isShared_1136_ = v_isSharedCheck_1153_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1153_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v_fst_1137_; lean_object* v_snd_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1152_; 
v_fst_1137_ = lean_ctor_get(v_a_1132_, 0);
v_snd_1138_ = lean_ctor_get(v_a_1132_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_a_1132_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1140_ = v_a_1132_;
v_isShared_1141_ = v_isSharedCheck_1152_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_snd_1138_);
lean_inc(v_fst_1137_);
lean_dec(v_a_1132_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1152_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
size_t v___x_1142_; size_t v___x_1143_; uint8_t v___x_1144_; 
v___x_1142_ = lean_ptr_addr(v_struct_1130_);
v___x_1143_ = lean_ptr_addr(v_fst_1137_);
v___x_1144_ = lean_usize_dec_eq(v___x_1142_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; 
lean_inc(v_idx_1129_);
lean_inc(v_typeName_1128_);
lean_del_object(v___x_1140_);
lean_del_object(v___x_1135_);
lean_dec_ref_known(v_e_939_, 3);
v___x_1145_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_1128_, v_idx_1129_, v_fst_1137_, v_snd_1138_, v_a_942_, v_a_943_, v_a_1133_);
return v___x_1145_;
}
else
{
lean_object* v___x_1147_; 
lean_dec(v_fst_1137_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v_e_939_);
v___x_1147_ = v___x_1140_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_e_939_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_snd_1138_);
v___x_1147_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1149_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1147_);
v___x_1149_ = v___x_1135_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_a_1133_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_939_, 3);
return v___x_1131_;
}
}
default: 
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec(v_offset_940_);
lean_dec_ref(v_e_939_);
v___x_1154_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
v___x_1155_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_1154_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
return v___x_1155_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_937_ = stack[0].m_obj;
lean_object* v_d_938_ = stack[1].m_obj;
lean_object* v_e_939_ = stack[2].m_obj;
lean_object* v_offset_940_ = stack[3].m_obj;
lean_object* v_a_941_ = stack[4].m_obj;
uint8_t v_a_942_ = stack[5].m_num;
lean_object* v_a_943_ = stack[6].m_obj;
lean_object* v_a_944_ = stack[7].m_obj;
lean_object* v_res_1156_;
v_res_1156_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_937_, v_d_938_, v_e_939_, v_offset_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
stack->m_obj
 = v_res_1156_;
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(lean_object* v_s_1157_, lean_object* v_d_1158_, lean_object* v_e_1159_, lean_object* v_offset_1160_, lean_object* v_a_1161_, uint8_t v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_key_1165_; lean_object* v_a_1167_; lean_object* v___x_1180_; 
lean_inc(v_offset_1160_);
lean_inc_ref(v_e_1159_);
v_key_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1165_, 0, v_e_1159_);
lean_ctor_set(v_key_1165_, 1, v_offset_1160_);
v___x_1180_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_1161_, v_key_1165_);
if (lean_obj_tag(v___x_1180_) == 1)
{
lean_object* v_val_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec_ref_known(v_key_1165_, 2);
lean_dec(v_offset_1160_);
lean_dec_ref(v_e_1159_);
v_val_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_val_1181_);
lean_dec_ref_known(v___x_1180_, 1);
v___x_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1182_, 0, v_val_1181_);
lean_ctor_set(v___x_1182_, 1, v_a_1161_);
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
lean_ctor_set(v___x_1183_, 1, v_a_1164_);
return v___x_1183_;
}
else
{
lean_object* v_s_u2081_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
lean_dec(v___x_1180_);
v_s_u2081_1184_ = lean_nat_add(v_s_1157_, v_offset_1160_);
v___x_1185_ = l_Lean_Expr_looseBVarRange(v_e_1159_);
v___x_1186_ = lean_nat_dec_le(v___x_1185_, v_s_u2081_1184_);
lean_dec(v___x_1185_);
if (v___x_1186_ == 0)
{
if (lean_obj_tag(v_e_1159_) == 0)
{
lean_object* v_deBruijnIndex_1187_; uint8_t v___x_1188_; 
v_deBruijnIndex_1187_ = lean_ctor_get(v_e_1159_, 0);
v___x_1188_ = lean_nat_dec_le(v_s_u2081_1184_, v_deBruijnIndex_1187_);
lean_dec(v_s_u2081_1184_);
if (v___x_1188_ == 0)
{
v_a_1167_ = v_a_1164_;
goto v___jp_1166_;
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_inc(v_deBruijnIndex_1187_);
lean_dec_ref_known(v_e_1159_, 1);
lean_dec(v_offset_1160_);
v___x_1189_ = lean_nat_add(v_deBruijnIndex_1187_, v_d_1158_);
lean_dec(v_deBruijnIndex_1187_);
v___x_1190_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_1189_, v_a_1164_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v_a_1192_; lean_object* v___x_1193_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
v_a_1192_ = lean_ctor_get(v___x_1190_, 1);
lean_inc(v_a_1192_);
lean_dec_ref_known(v___x_1190_, 2);
v___x_1193_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1165_, v_a_1191_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1192_);
return v___x_1193_;
}
else
{
lean_object* v_a_1194_; lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec_ref_known(v_key_1165_, 2);
lean_dec_ref(v_a_1161_);
v_a_1194_ = lean_ctor_get(v___x_1190_, 0);
v_a_1195_ = lean_ctor_get(v___x_1190_, 1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1190_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_inc(v_a_1194_);
lean_dec(v___x_1190_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1194_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
else
{
lean_dec(v_s_u2081_1184_);
v_a_1167_ = v_a_1164_;
goto v___jp_1166_;
}
}
else
{
lean_object* v___x_1203_; 
lean_dec(v_s_u2081_1184_);
lean_dec(v_offset_1160_);
v___x_1203_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1165_, v_e_1159_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1203_;
}
}
v___jp_1166_:
{
switch(lean_obj_tag(v_e_1159_))
{
case 9:
{
lean_object* v___x_1168_; 
lean_dec(v_offset_1160_);
v___x_1168_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1165_, v_e_1159_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1167_);
return v___x_1168_;
}
case 2:
{
lean_object* v___x_1169_; 
lean_dec(v_offset_1160_);
v___x_1169_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1165_, v_e_1159_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1167_);
return v___x_1169_;
}
case 0:
{
lean_object* v___x_1170_; 
lean_dec(v_offset_1160_);
v___x_1170_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1165_, v_e_1159_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1167_);
return v___x_1170_;
}
case 1:
{
lean_object* v___x_1171_; 
lean_dec(v_offset_1160_);
v___x_1171_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1165_, v_e_1159_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1167_);
return v___x_1171_;
}
case 4:
{
lean_object* v___x_1172_; 
lean_dec(v_offset_1160_);
v___x_1172_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1165_, v_e_1159_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1167_);
return v___x_1172_;
}
case 3:
{
lean_object* v___x_1173_; 
lean_dec(v_offset_1160_);
v___x_1173_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1165_, v_e_1159_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1167_);
return v___x_1173_;
}
default: 
{
lean_object* v___x_1174_; 
v___x_1174_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_1157_, v_d_1158_, v_e_1159_, v_offset_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1167_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v_a_1176_; lean_object* v_fst_1177_; lean_object* v_snd_1178_; lean_object* v___x_1179_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
v_a_1176_ = lean_ctor_get(v___x_1174_, 1);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1174_, 2);
v_fst_1177_ = lean_ctor_get(v_a_1175_, 0);
lean_inc(v_fst_1177_);
v_snd_1178_ = lean_ctor_get(v_a_1175_, 1);
lean_inc(v_snd_1178_);
lean_dec(v_a_1175_);
v___x_1179_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1165_, v_fst_1177_, v_snd_1178_, v_a_1162_, v_a_1163_, v_a_1176_);
return v___x_1179_;
}
else
{
lean_dec_ref_known(v_key_1165_, 2);
return v___x_1174_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1157_ = stack[0].m_obj;
lean_object* v_d_1158_ = stack[1].m_obj;
lean_object* v_e_1159_ = stack[2].m_obj;
lean_object* v_offset_1160_ = stack[3].m_obj;
lean_object* v_a_1161_ = stack[4].m_obj;
uint8_t v_a_1162_ = stack[5].m_num;
lean_object* v_a_1163_ = stack[6].m_obj;
lean_object* v_a_1164_ = stack[7].m_obj;
lean_object* v_res_1204_;
v_res_1204_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1157_, v_d_1158_, v_e_1159_, v_offset_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
stack->m_obj
 = v_res_1204_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0___boxed(lean_object* v_s_1205_, lean_object* v_d_1206_, lean_object* v_e_1207_, lean_object* v_offset_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
uint8_t v_a_boxed_1213_; lean_object* v_res_1214_; 
v_a_boxed_1213_ = lean_unbox(v_a_1210_);
v_res_1214_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1205_, v_d_1206_, v_e_1207_, v_offset_1208_, v_a_1209_, v_a_boxed_1213_, v_a_1211_, v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_d_1206_);
lean_dec(v_s_1205_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0___boxed(lean_object* v_s_1215_, lean_object* v_d_1216_, lean_object* v_e_1217_, lean_object* v_offset_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
uint8_t v_a_boxed_1223_; lean_object* v_res_1224_; 
v_a_boxed_1223_ = lean_unbox(v_a_1220_);
v_res_1224_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_1215_, v_d_1216_, v_e_1217_, v_offset_1218_, v_a_1219_, v_a_boxed_1223_, v_a_1221_, v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_d_1216_);
lean_dec(v_s_1215_);
return v_res_1224_;
}
}
lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27(lean_object* v_e_1225_, lean_object* v_s_1226_, lean_object* v_d_1227_, uint8_t v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1231_ = l_Lean_Expr_looseBVarRange(v_e_1225_);
v___x_1232_ = lean_nat_dec_le(v___x_1231_, v_s_1226_);
lean_dec(v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v_a_1235_; 
v___x_1233_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_e_1225_) == 0)
{
lean_object* v_deBruijnIndex_1263_; uint8_t v___x_1264_; 
v_deBruijnIndex_1263_ = lean_ctor_get(v_e_1225_, 0);
v___x_1264_ = lean_nat_dec_le(v_s_1226_, v_deBruijnIndex_1263_);
if (v___x_1264_ == 0)
{
v_a_1235_ = v_a_1230_;
goto v___jp_1234_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_inc(v_deBruijnIndex_1263_);
lean_dec_ref_known(v_e_1225_, 1);
v___x_1265_ = lean_nat_add(v_deBruijnIndex_1263_, v_d_1227_);
lean_dec(v_deBruijnIndex_1263_);
v___x_1266_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_1265_, v_a_1230_);
return v___x_1266_;
}
}
else
{
v_a_1235_ = v_a_1230_;
goto v___jp_1234_;
}
v___jp_1234_:
{
switch(lean_obj_tag(v_e_1225_))
{
case 9:
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v_e_1225_);
lean_ctor_set(v___x_1236_, 1, v_a_1235_);
return v___x_1236_;
}
case 2:
{
lean_object* v___x_1237_; 
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_e_1225_);
lean_ctor_set(v___x_1237_, 1, v_a_1235_);
return v___x_1237_;
}
case 0:
{
lean_object* v___x_1238_; 
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v_e_1225_);
lean_ctor_set(v___x_1238_, 1, v_a_1235_);
return v___x_1238_;
}
case 1:
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v_e_1225_);
lean_ctor_set(v___x_1239_, 1, v_a_1235_);
return v___x_1239_;
}
case 4:
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v_e_1225_);
lean_ctor_set(v___x_1240_, 1, v_a_1235_);
return v___x_1240_;
}
case 3:
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v_e_1225_);
lean_ctor_set(v___x_1241_, 1, v_a_1235_);
return v___x_1241_;
}
default: 
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1);
v___x_1243_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_1226_, v_d_1227_, v_e_1225_, v___x_1233_, v___x_1242_, v_a_1228_, v_a_1229_, v_a_1235_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1253_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_a_1245_ = lean_ctor_get(v___x_1243_, 1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1247_ = v___x_1243_;
v_isShared_1248_ = v_isSharedCheck_1253_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1253_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v_fst_1249_; lean_object* v___x_1251_; 
v_fst_1249_ = lean_ctor_get(v_a_1244_, 0);
lean_inc(v_fst_1249_);
lean_dec(v_a_1244_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v_fst_1249_);
v___x_1251_ = v___x_1247_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_fst_1249_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_a_1245_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
v_a_1254_ = lean_ctor_get(v___x_1243_, 0);
v_a_1255_ = lean_ctor_get(v___x_1243_, 1);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1243_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_inc(v_a_1254_);
lean_dec(v___x_1243_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1254_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v_e_1225_);
lean_ctor_set(v___x_1267_, 1, v_a_1230_);
return v___x_1267_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_liftLooseBVarsS_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1225_ = stack[0].m_obj;
lean_object* v_s_1226_ = stack[1].m_obj;
lean_object* v_d_1227_ = stack[2].m_obj;
uint8_t v_a_1228_ = stack[3].m_num;
lean_object* v_a_1229_ = stack[4].m_obj;
lean_object* v_a_1230_ = stack[5].m_obj;
lean_object* v_res_1268_;
v_res_1268_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_e_1225_, v_s_1226_, v_d_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
stack->m_obj
 = v_res_1268_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27___boxed(lean_object* v_e_1269_, lean_object* v_s_1270_, lean_object* v_d_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
uint8_t v_a_boxed_1275_; lean_object* v_res_1276_; 
v_a_boxed_1275_ = lean_unbox(v_a_1272_);
v_res_1276_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_e_1269_, v_s_1270_, v_d_1271_, v_a_boxed_1275_, v_a_1273_, v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_d_1271_);
lean_dec(v_s_1270_);
return v_res_1276_;
}
}
lean_object* l_Lean_Meta_Sym_liftLooseBVarsS(lean_object* v_e_1277_, lean_object* v_s_1278_, lean_object* v_d_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v___x_1287_; uint8_t v_debug_1288_; lean_object* v___x_1289_; lean_object* v_env_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1287_ = lean_st_ref_get(v_a_1281_);
v_debug_1288_ = lean_ctor_get_uint8(v___x_1287_, sizeof(void*)*12);
lean_dec(v___x_1287_);
v___x_1289_ = lean_st_ref_get(v_a_1285_);
v_env_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc_ref(v_env_1290_);
lean_dec(v___x_1289_);
v___x_1291_ = lean_box(v_debug_1288_);
v___x_1292_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_liftLooseBVarsS_x27___boxed), 6, 4);
lean_closure_set(v___x_1292_, 0, v_e_1277_);
lean_closure_set(v___x_1292_, 1, v_s_1278_);
lean_closure_set(v___x_1292_, 2, v_d_1279_);
lean_closure_set(v___x_1292_, 3, v___x_1291_);
v___x_1293_ = 0;
v___x_1294_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1294_, 0, v_env_1290_);
lean_ctor_set_uint8(v___x_1294_, sizeof(void*)*1, v___x_1293_);
lean_ctor_set_uint8(v___x_1294_, sizeof(void*)*1 + 1, v___x_1293_);
v___x_1295_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_1292_, v___x_1294_, v_a_1281_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1306_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1306_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1306_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
if (lean_obj_tag(v_a_1296_) == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec_ref_known(v_a_1296_, 1);
lean_del_object(v___x_1298_);
v___x_1300_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2, &l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2);
v___x_1301_ = l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(v___x_1300_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_);
return v___x_1301_;
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; 
v_a_1302_ = lean_ctor_get(v_a_1296_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v_a_1296_, 1);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v_a_1302_);
v___x_1304_ = v___x_1298_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
v_a_1307_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1295_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1295_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_liftLooseBVarsS_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1277_ = stack[0].m_obj;
lean_object* v_s_1278_ = stack[1].m_obj;
lean_object* v_d_1279_ = stack[2].m_obj;
lean_object* v_a_1280_ = stack[3].m_obj;
lean_object* v_a_1281_ = stack[4].m_obj;
lean_object* v_a_1282_ = stack[5].m_obj;
lean_object* v_a_1283_ = stack[6].m_obj;
lean_object* v_a_1284_ = stack[7].m_obj;
lean_object* v_a_1285_ = stack[8].m_obj;
lean_object* v_res_1315_;
v_res_1315_ = l_Lean_Meta_Sym_liftLooseBVarsS(v_e_1277_, v_s_1278_, v_d_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_);
stack->m_obj
 = v_res_1315_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___boxed(lean_object* v_e_1316_, lean_object* v_s_1317_, lean_object* v_d_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Meta_Sym_liftLooseBVarsS(v_e_1316_, v_s_1317_, v_d_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
return v_res_1326_;
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
