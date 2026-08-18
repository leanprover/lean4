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
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_24317__boxed_14_; lean_object* v_res_15_; 
v___y_24317__boxed_14_ = lean_unbox(v___y_11_);
v_res_15_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(v_idx_10_, v___y_24317__boxed_14_, v___y_12_, v___y_13_);
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
uint8_t v_bi_boxed_78_; uint8_t v___y_24329__boxed_79_; lean_object* v_res_80_; 
v_bi_boxed_78_ = lean_unbox(v_bi_71_);
v___y_24329__boxed_79_ = lean_unbox(v___y_75_);
v_res_80_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_x_70_, v_bi_boxed_78_, v_t_72_, v_b_73_, v___y_74_, v___y_24329__boxed_79_, v___y_76_, v___y_77_);
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
uint8_t v___y_24435__boxed_130_; lean_object* v_res_131_; 
v___y_24435__boxed_130_ = lean_unbox(v___y_127_);
v_res_131_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_structName_123_, v_idx_124_, v_struct_125_, v___y_126_, v___y_24435__boxed_130_, v___y_128_, v___y_129_);
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
uint8_t v_bi_boxed_194_; uint8_t v___y_24518__boxed_195_; lean_object* v_res_196_; 
v_bi_boxed_194_ = lean_unbox(v_bi_187_);
v___y_24518__boxed_195_ = lean_unbox(v___y_191_);
v_res_196_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_x_186_, v_bi_boxed_194_, v_t_188_, v_b_189_, v___y_190_, v___y_24518__boxed_195_, v___y_192_, v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11_spec__12___redArg(lean_object* v_m_197_, lean_object* v_query_198_, lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_x_201_){
_start:
{
lean_object* v_zero_202_; uint8_t v_isZero_203_; 
v_zero_202_ = lean_unsigned_to_nat(0u);
v_isZero_203_ = lean_nat_dec_eq(v_x_200_, v_zero_202_);
if (v_isZero_203_ == 1)
{
lean_dec(v_x_201_);
lean_dec(v_x_200_);
if (lean_obj_tag(v_x_199_) == 0)
{
lean_object* v___x_204_; 
v___x_204_ = lean_box(2);
return v___x_204_;
}
else
{
lean_object* v_val_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
v_val_205_ = lean_ctor_get(v_x_199_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v_x_199_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_val_205_);
lean_dec(v_x_199_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_val_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
else
{
lean_object* v_keyArray_213_; lean_object* v_valueArray_214_; lean_object* v___x_215_; uint8_t v_isSome_216_; 
v_keyArray_213_ = lean_ctor_get(v_m_197_, 1);
v_valueArray_214_ = lean_ctor_get(v_m_197_, 2);
v___x_215_ = lean_array_fget_borrowed(v_keyArray_213_, v_x_201_);
v_isSome_216_ = lean_noption_is_some(v___x_215_);
if (v_isSome_216_ == 0)
{
lean_dec(v_x_200_);
if (lean_obj_tag(v_x_199_) == 0)
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v_x_201_);
return v___x_217_;
}
else
{
lean_object* v_val_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec(v_x_201_);
v_val_218_ = lean_ctor_get(v_x_199_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v_x_199_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_val_218_);
lean_dec(v_x_199_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_val_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
else
{
lean_object* v_one_226_; lean_object* v_n_227_; lean_object* v___y_229_; 
v_one_226_ = lean_unsigned_to_nat(1u);
v_n_227_ = lean_nat_sub(v_x_200_, v_one_226_);
lean_dec(v_x_200_);
if (v_isSome_216_ == 0)
{
goto v___jp_235_;
}
else
{
lean_object* v___x_237_; uint8_t v_isSome_238_; 
v___x_237_ = lean_array_fget_borrowed(v_valueArray_214_, v_x_201_);
v_isSome_238_ = lean_noption_is_some(v___x_237_);
if (v_isSome_238_ == 0)
{
goto v___jp_235_;
}
else
{
lean_object* v_val_239_; lean_object* v_fst_240_; lean_object* v_snd_241_; lean_object* v_fst_242_; lean_object* v_snd_243_; lean_object* v_val_244_; uint8_t v___y_246_; size_t v___x_253_; size_t v___x_254_; uint8_t v___x_255_; 
lean_inc(v___x_215_);
v_val_239_ = lean_noption_get(v___x_215_);
v_fst_240_ = lean_ctor_get(v_val_239_, 0);
lean_inc(v_fst_240_);
v_snd_241_ = lean_ctor_get(v_val_239_, 1);
lean_inc(v_snd_241_);
v_fst_242_ = lean_ctor_get(v_query_198_, 0);
v_snd_243_ = lean_ctor_get(v_query_198_, 1);
lean_inc(v___x_237_);
v_val_244_ = lean_noption_get(v___x_237_);
v___x_253_ = lean_ptr_addr(v_fst_240_);
lean_dec(v_fst_240_);
v___x_254_ = lean_ptr_addr(v_fst_242_);
v___x_255_ = lean_usize_dec_eq(v___x_253_, v___x_254_);
if (v___x_255_ == 0)
{
lean_dec(v_snd_241_);
v___y_246_ = v___x_255_;
goto v___jp_245_;
}
else
{
uint8_t v___x_256_; 
v___x_256_ = lean_nat_dec_eq(v_snd_241_, v_snd_243_);
lean_dec(v_snd_241_);
v___y_246_ = v___x_256_;
goto v___jp_245_;
}
v___jp_245_:
{
if (v___y_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
lean_dec(v_val_244_);
lean_dec(v_val_239_);
v___x_247_ = lean_array_get_size(v_keyArray_213_);
v___x_248_ = lean_nat_add(v_x_201_, v_one_226_);
lean_dec(v_x_201_);
v___x_249_ = lean_nat_dec_lt(v___x_248_, v___x_247_);
if (v___x_249_ == 0)
{
lean_dec(v___x_248_);
v_x_200_ = v_n_227_;
v_x_201_ = v_zero_202_;
goto _start;
}
else
{
v_x_200_ = v_n_227_;
v_x_201_ = v___x_248_;
goto _start;
}
}
else
{
lean_object* v___x_252_; 
lean_dec(v_n_227_);
lean_dec(v_x_199_);
v___x_252_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_252_, 0, v_x_201_);
lean_ctor_set(v___x_252_, 1, v_val_239_);
lean_ctor_set(v___x_252_, 2, v_val_244_);
return v___x_252_;
}
}
}
}
v___jp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_230_ = lean_array_get_size(v_keyArray_213_);
v___x_231_ = lean_nat_add(v_x_201_, v_one_226_);
lean_dec(v_x_201_);
v___x_232_ = lean_nat_dec_lt(v___x_231_, v___x_230_);
if (v___x_232_ == 0)
{
lean_dec(v___x_231_);
v_x_199_ = v___y_229_;
v_x_200_ = v_n_227_;
v_x_201_ = v_zero_202_;
goto _start;
}
else
{
v_x_199_ = v___y_229_;
v_x_200_ = v_n_227_;
v_x_201_ = v___x_231_;
goto _start;
}
}
v___jp_235_:
{
if (lean_obj_tag(v_x_199_) == 0)
{
lean_object* v___x_236_; 
lean_inc(v_x_201_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v_x_201_);
v___y_229_ = v___x_236_;
goto v___jp_228_;
}
else
{
v___y_229_ = v_x_199_;
goto v___jp_228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_m_257_, lean_object* v_query_258_, lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11_spec__12___redArg(v_m_257_, v_query_258_, v_x_259_, v_x_260_, v_x_261_);
lean_dec_ref(v_query_258_);
lean_dec_ref(v_m_257_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11___redArg(lean_object* v_m_263_, lean_object* v_query_264_){
_start:
{
lean_object* v_keyArray_265_; lean_object* v_fst_266_; lean_object* v_snd_267_; lean_object* v___x_268_; size_t v___x_269_; size_t v___x_270_; size_t v___x_271_; uint64_t v___x_272_; uint64_t v___x_273_; uint64_t v___x_274_; uint64_t v___x_275_; uint64_t v___x_276_; uint64_t v_fold_277_; uint64_t v___x_278_; uint64_t v___x_279_; uint64_t v___x_280_; size_t v___x_281_; size_t v___x_282_; size_t v___x_283_; size_t v___x_284_; size_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_keyArray_265_ = lean_ctor_get(v_m_263_, 1);
v_fst_266_ = lean_ctor_get(v_query_264_, 0);
v_snd_267_ = lean_ctor_get(v_query_264_, 1);
v___x_268_ = lean_array_get_size(v_keyArray_265_);
v___x_269_ = lean_ptr_addr(v_fst_266_);
v___x_270_ = ((size_t)3ULL);
v___x_271_ = lean_usize_shift_right(v___x_269_, v___x_270_);
v___x_272_ = lean_usize_to_uint64(v___x_271_);
v___x_273_ = lean_uint64_of_nat(v_snd_267_);
v___x_274_ = lean_uint64_mix_hash(v___x_272_, v___x_273_);
v___x_275_ = 32ULL;
v___x_276_ = lean_uint64_shift_right(v___x_274_, v___x_275_);
v_fold_277_ = lean_uint64_xor(v___x_274_, v___x_276_);
v___x_278_ = 16ULL;
v___x_279_ = lean_uint64_shift_right(v_fold_277_, v___x_278_);
v___x_280_ = lean_uint64_xor(v_fold_277_, v___x_279_);
v___x_281_ = lean_uint64_to_usize(v___x_280_);
v___x_282_ = lean_usize_of_nat(v___x_268_);
v___x_283_ = ((size_t)1ULL);
v___x_284_ = lean_usize_sub(v___x_282_, v___x_283_);
v___x_285_ = lean_usize_land(v___x_281_, v___x_284_);
v___x_286_ = lean_usize_to_nat(v___x_285_);
v___x_287_ = lean_box(0);
v___x_288_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11_spec__12___redArg(v_m_263_, v_query_264_, v___x_287_, v___x_268_, v___x_286_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11___redArg___boxed(lean_object* v_m_289_, lean_object* v_query_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11___redArg(v_m_289_, v_query_290_);
lean_dec_ref(v_query_290_);
lean_dec_ref(v_m_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(lean_object* v_m_292_, lean_object* v_query_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11___redArg(v_m_292_, v_query_293_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_index_295_; lean_object* v_key_296_; lean_object* v_value_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
v_index_295_ = lean_ctor_get(v___x_294_, 0);
v_key_296_ = lean_ctor_get(v___x_294_, 1);
v_value_297_ = lean_ctor_get(v___x_294_, 2);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_294_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_value_297_);
lean_inc(v_key_296_);
lean_inc(v_index_295_);
lean_dec(v___x_294_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_index_295_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_key_296_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_value_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
else
{
lean_object* v___x_305_; 
lean_dec(v___x_294_);
v___x_305_ = lean_box(1);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg___boxed(lean_object* v_m_306_, lean_object* v_query_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_m_306_, v_query_307_);
lean_dec_ref(v_query_307_);
lean_dec_ref(v_m_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(lean_object* v_m_309_, lean_object* v_a_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_m_309_, v_a_310_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_value_312_; lean_object* v___x_313_; 
v_value_312_ = lean_ctor_get(v___x_311_, 2);
lean_inc(v_value_312_);
lean_dec_ref_known(v___x_311_, 3);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v_value_312_);
return v___x_313_;
}
else
{
lean_object* v___x_314_; 
v___x_314_ = lean_box(0);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_m_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_315_, v_a_316_);
lean_dec_ref(v_a_316_);
lean_dec_ref(v_m_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(lean_object* v_f_318_, lean_object* v_a_319_, lean_object* v___y_320_, uint8_t v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___y_325_; lean_object* v___y_326_; 
if (v___y_321_ == 0)
{
v___y_325_ = v___y_320_;
v___y_326_ = v___y_323_;
goto v___jp_324_;
}
else
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_318_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_350_; 
v_a_349_ = lean_ctor_get(v___x_348_, 1);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_348_, 2);
v___x_350_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_319_, v___y_321_, v___y_322_, v_a_349_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; 
v_a_351_ = lean_ctor_get(v___x_350_, 1);
lean_inc(v_a_351_);
lean_dec_ref_known(v___x_350_, 2);
v___y_325_ = v___y_320_;
v___y_326_ = v_a_351_;
goto v___jp_324_;
}
else
{
lean_object* v_a_352_; lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_dec_ref(v___y_320_);
lean_dec_ref(v_a_319_);
lean_dec_ref(v_f_318_);
v_a_352_ = lean_ctor_get(v___x_350_, 0);
v_a_353_ = lean_ctor_get(v___x_350_, 1);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_350_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_inc(v_a_352_);
lean_dec(v___x_350_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
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
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_352_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
else
{
lean_object* v_a_361_; lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec_ref(v___y_320_);
lean_dec_ref(v_a_319_);
lean_dec_ref(v_f_318_);
v_a_361_ = lean_ctor_get(v___x_348_, 0);
v_a_362_ = lean_ctor_get(v___x_348_, 1);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_348_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_inc(v_a_361_);
lean_dec(v___x_348_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_361_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
v___jp_324_:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = l_Lean_Expr_app___override(v_f_318_, v_a_319_);
v___x_328_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_327_, v___y_326_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_338_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
v_a_330_ = lean_ctor_get(v___x_328_, 1);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_338_ == 0)
{
v___x_332_ = v___x_328_;
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_inc(v_a_329_);
lean_dec(v___x_328_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v_a_329_);
lean_ctor_set(v___x_334_, 1, v___y_325_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_334_);
v___x_336_ = v___x_332_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_a_330_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
else
{
lean_object* v_a_339_; lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec_ref(v___y_325_);
v_a_339_ = lean_ctor_get(v___x_328_, 0);
v_a_340_ = lean_ctor_get(v___x_328_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_328_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_inc(v_a_339_);
lean_dec(v___x_328_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_339_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2___boxed(lean_object* v_f_370_, lean_object* v_a_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
uint8_t v___y_24808__boxed_376_; lean_object* v_res_377_; 
v___y_24808__boxed_376_ = lean_unbox(v___y_373_);
v_res_377_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_f_370_, v_a_371_, v___y_372_, v___y_24808__boxed_376_, v___y_374_, v___y_375_);
lean_dec_ref(v___y_374_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(lean_object* v_x_378_, lean_object* v_t_379_, lean_object* v_v_380_, lean_object* v_b_381_, uint8_t v_nondep_382_, lean_object* v___y_383_, uint8_t v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___y_388_; lean_object* v___y_389_; 
if (v___y_384_ == 0)
{
v___y_388_ = v___y_383_;
v___y_389_ = v___y_386_;
goto v___jp_387_;
}
else
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_379_, v___y_384_, v___y_385_, v___y_386_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_413_; 
v_a_412_ = lean_ctor_get(v___x_411_, 1);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_411_, 2);
v___x_413_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_380_, v___y_384_, v___y_385_, v_a_412_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_415_; 
v_a_414_ = lean_ctor_get(v___x_413_, 1);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 2);
v___x_415_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_381_, v___y_384_, v___y_385_, v_a_414_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; 
v_a_416_ = lean_ctor_get(v___x_415_, 1);
lean_inc(v_a_416_);
lean_dec_ref_known(v___x_415_, 2);
v___y_388_ = v___y_383_;
v___y_389_ = v_a_416_;
goto v___jp_387_;
}
else
{
lean_object* v_a_417_; lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec_ref(v___y_383_);
lean_dec_ref(v_b_381_);
lean_dec_ref(v_v_380_);
lean_dec_ref(v_t_379_);
lean_dec(v_x_378_);
v_a_417_ = lean_ctor_get(v___x_415_, 0);
v_a_418_ = lean_ctor_get(v___x_415_, 1);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_415_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_inc(v_a_417_);
lean_dec(v___x_415_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_417_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
else
{
lean_object* v_a_426_; lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec_ref(v___y_383_);
lean_dec_ref(v_b_381_);
lean_dec_ref(v_v_380_);
lean_dec_ref(v_t_379_);
lean_dec(v_x_378_);
v_a_426_ = lean_ctor_get(v___x_413_, 0);
v_a_427_ = lean_ctor_get(v___x_413_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_413_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_inc(v_a_426_);
lean_dec(v___x_413_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_426_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
else
{
lean_object* v_a_435_; lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec_ref(v___y_383_);
lean_dec_ref(v_b_381_);
lean_dec_ref(v_v_380_);
lean_dec_ref(v_t_379_);
lean_dec(v_x_378_);
v_a_435_ = lean_ctor_get(v___x_411_, 0);
v_a_436_ = lean_ctor_get(v___x_411_, 1);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_411_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_inc(v_a_435_);
lean_dec(v___x_411_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_435_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
v___jp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = l_Lean_Expr_letE___override(v_x_378_, v_t_379_, v_v_380_, v_b_381_, v_nondep_382_);
v___x_391_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_390_, v___y_389_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_401_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_a_393_ = lean_ctor_get(v___x_391_, 1);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_401_ == 0)
{
v___x_395_ = v___x_391_;
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_a_392_);
lean_ctor_set(v___x_397_, 1, v___y_388_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_a_393_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
else
{
lean_object* v_a_402_; lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec_ref(v___y_388_);
v_a_402_ = lean_ctor_get(v___x_391_, 0);
v_a_403_ = lean_ctor_get(v___x_391_, 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_391_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_inc(v_a_402_);
lean_dec(v___x_391_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_402_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5___boxed(lean_object* v_x_444_, lean_object* v_t_445_, lean_object* v_v_446_, lean_object* v_b_447_, lean_object* v_nondep_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
uint8_t v_nondep_boxed_453_; uint8_t v___y_24914__boxed_454_; lean_object* v_res_455_; 
v_nondep_boxed_453_ = lean_unbox(v_nondep_448_);
v___y_24914__boxed_454_ = lean_unbox(v___y_450_);
v_res_455_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_x_444_, v_t_445_, v_v_446_, v_b_447_, v_nondep_boxed_453_, v___y_449_, v___y_24914__boxed_454_, v___y_451_, v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(lean_object* v_msg_463_, lean_object* v___y_464_, uint8_t v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___f_468_; lean_object* v___f_469_; lean_object* v___f_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___f_480_; lean_object* v___f_481_; lean_object* v___f_482_; lean_object* v___f_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_23833__overap_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___f_468_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0));
v___f_469_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1));
v___f_470_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2));
v___x_471_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3));
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v___f_468_);
v___x_473_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4));
v___x_474_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5));
v___x_475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_475_, 0, v___x_472_);
lean_ctor_set(v___x_475_, 1, v___x_473_);
lean_ctor_set(v___x_475_, 2, v___f_469_);
lean_ctor_set(v___x_475_, 3, v___f_470_);
lean_ctor_set(v___x_475_, 4, v___x_474_);
v___x_476_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6));
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = l_ReaderT_instMonad___redArg(v___x_477_);
v___x_479_ = l_ReaderT_instMonad___redArg(v___x_478_);
lean_inc_ref_n(v___x_479_, 6);
v___f_480_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_480_, 0, v___x_479_);
v___f_481_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_481_, 0, v___x_479_);
v___f_482_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_482_, 0, v___x_479_);
v___f_483_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_483_, 0, v___x_479_);
v___x_484_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_484_, 0, lean_box(0));
lean_closure_set(v___x_484_, 1, lean_box(0));
lean_closure_set(v___x_484_, 2, v___x_479_);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v___f_480_);
v___x_486_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_486_, 0, lean_box(0));
lean_closure_set(v___x_486_, 1, lean_box(0));
lean_closure_set(v___x_486_, 2, v___x_479_);
v___x_487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
lean_ctor_set(v___x_487_, 2, v___f_481_);
lean_ctor_set(v___x_487_, 3, v___f_482_);
lean_ctor_set(v___x_487_, 4, v___f_483_);
v___x_488_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_488_, 0, lean_box(0));
lean_closure_set(v___x_488_, 1, lean_box(0));
lean_closure_set(v___x_488_, 2, v___x_479_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = l_Lean_instInhabitedExpr;
v___x_491_ = l_instInhabitedOfMonad___redArg(v___x_489_, v___x_490_);
v___x_23833__overap_492_ = lean_panic_fn_borrowed(v___x_491_, v_msg_463_);
lean_dec(v___x_491_);
v___x_493_ = lean_box(v___y_465_);
lean_inc_ref(v___y_466_);
v___x_494_ = lean_apply_4(v___x_23833__overap_492_, v___y_464_, v___x_493_, v___y_466_, v___y_467_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___boxed(lean_object* v_msg_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
uint8_t v___y_25057__boxed_500_; lean_object* v_res_501_; 
v___y_25057__boxed_500_ = lean_unbox(v___y_497_);
v_res_501_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v_msg_495_, v___y_496_, v___y_25057__boxed_500_, v___y_498_, v___y_499_);
lean_dec_ref(v___y_498_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(lean_object* v_d_502_, lean_object* v_e_503_, lean_object* v___y_504_, uint8_t v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___y_509_; lean_object* v___y_510_; 
if (v___y_505_ == 0)
{
v___y_509_ = v___y_504_;
v___y_510_ = v___y_507_;
goto v___jp_508_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_503_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; 
v_a_533_ = lean_ctor_get(v___x_532_, 1);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 2);
v___y_509_ = v___y_504_;
v___y_510_ = v_a_533_;
goto v___jp_508_;
}
else
{
lean_object* v_a_534_; lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec_ref(v___y_504_);
lean_dec_ref(v_e_503_);
lean_dec(v_d_502_);
v_a_534_ = lean_ctor_get(v___x_532_, 0);
v_a_535_ = lean_ctor_get(v___x_532_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_532_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_inc(v_a_534_);
lean_dec(v___x_532_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_534_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
v___jp_508_:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = l_Lean_Expr_mdata___override(v_d_502_, v_e_503_);
v___x_512_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_511_, v___y_510_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_522_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
v_a_514_ = lean_ctor_get(v___x_512_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_522_ == 0)
{
v___x_516_ = v___x_512_;
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_inc(v_a_513_);
lean_dec(v___x_512_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_a_513_);
lean_ctor_set(v___x_518_, 1, v___y_509_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_518_);
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_a_514_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
else
{
lean_object* v_a_523_; lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec_ref(v___y_509_);
v_a_523_ = lean_ctor_get(v___x_512_, 0);
v_a_524_ = lean_ctor_get(v___x_512_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_512_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_inc(v_a_523_);
lean_dec(v___x_512_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_523_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6___boxed(lean_object* v_d_543_, lean_object* v_e_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
uint8_t v___y_25128__boxed_549_; lean_object* v_res_550_; 
v___y_25128__boxed_549_ = lean_unbox(v___y_546_);
v_res_550_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_d_543_, v_e_544_, v___y_545_, v___y_25128__boxed_549_, v___y_547_, v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_550_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_554_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2));
v___x_555_ = lean_unsigned_to_nat(67u);
v___x_556_ = lean_unsigned_to_nat(35u);
v___x_557_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1));
v___x_558_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0));
v___x_559_ = l_mkPanicMessageWithDecl(v___x_558_, v___x_557_, v___x_556_, v___x_555_, v___x_554_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(lean_object* v_s_560_, lean_object* v_d_561_, lean_object* v_e_562_, lean_object* v_offset_563_, lean_object* v_a_564_, uint8_t v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
switch(lean_obj_tag(v_e_562_))
{
case 5:
{
lean_object* v_fn_568_; lean_object* v_arg_569_; lean_object* v___x_570_; 
v_fn_568_ = lean_ctor_get(v_e_562_, 0);
v_arg_569_ = lean_ctor_get(v_e_562_, 1);
lean_inc(v_offset_563_);
lean_inc_ref(v_fn_568_);
v___x_570_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_560_, v_d_561_, v_fn_568_, v_offset_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v_a_572_; lean_object* v_fst_573_; lean_object* v_snd_574_; lean_object* v___x_575_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
v_a_572_ = lean_ctor_get(v___x_570_, 1);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_570_, 2);
v_fst_573_ = lean_ctor_get(v_a_571_, 0);
lean_inc(v_fst_573_);
v_snd_574_ = lean_ctor_get(v_a_571_, 1);
lean_inc(v_snd_574_);
lean_dec(v_a_571_);
lean_inc_ref(v_arg_569_);
v___x_575_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_560_, v_d_561_, v_arg_569_, v_offset_563_, v_snd_574_, v_a_565_, v_a_566_, v_a_572_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_602_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_a_577_ = lean_ctor_get(v___x_575_, 1);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_602_ == 0)
{
v___x_579_ = v___x_575_;
v_isShared_580_ = v_isSharedCheck_602_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_602_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v_fst_581_; lean_object* v_snd_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_601_; 
v_fst_581_ = lean_ctor_get(v_a_576_, 0);
v_snd_582_ = lean_ctor_get(v_a_576_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v_a_576_);
if (v_isSharedCheck_601_ == 0)
{
v___x_584_ = v_a_576_;
v_isShared_585_ = v_isSharedCheck_601_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_snd_582_);
lean_inc(v_fst_581_);
lean_dec(v_a_576_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_601_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
uint8_t v___y_587_; size_t v___x_595_; size_t v___x_596_; uint8_t v___x_597_; 
v___x_595_ = lean_ptr_addr(v_fn_568_);
v___x_596_ = lean_ptr_addr(v_fst_573_);
v___x_597_ = lean_usize_dec_eq(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
v___y_587_ = v___x_597_;
goto v___jp_586_;
}
else
{
size_t v___x_598_; size_t v___x_599_; uint8_t v___x_600_; 
v___x_598_ = lean_ptr_addr(v_arg_569_);
v___x_599_ = lean_ptr_addr(v_fst_581_);
v___x_600_ = lean_usize_dec_eq(v___x_598_, v___x_599_);
v___y_587_ = v___x_600_;
goto v___jp_586_;
}
v___jp_586_:
{
if (v___y_587_ == 0)
{
lean_object* v___x_588_; 
lean_del_object(v___x_584_);
lean_del_object(v___x_579_);
lean_dec_ref_known(v_e_562_, 2);
v___x_588_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_573_, v_fst_581_, v_snd_582_, v_a_565_, v_a_566_, v_a_577_);
return v___x_588_;
}
else
{
lean_object* v___x_590_; 
lean_dec(v_fst_581_);
lean_dec(v_fst_573_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v_e_562_);
v___x_590_ = v___x_584_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_e_562_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_snd_582_);
v___x_590_ = v_reuseFailAlloc_594_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_590_);
v___x_592_ = v___x_579_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_a_577_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_573_);
lean_dec_ref_known(v_e_562_, 2);
return v___x_575_;
}
}
else
{
lean_dec_ref_known(v_e_562_, 2);
lean_dec(v_offset_563_);
return v___x_570_;
}
}
case 6:
{
lean_object* v_binderName_603_; lean_object* v_binderType_604_; lean_object* v_body_605_; uint8_t v_binderInfo_606_; lean_object* v___x_607_; 
v_binderName_603_ = lean_ctor_get(v_e_562_, 0);
v_binderType_604_ = lean_ctor_get(v_e_562_, 1);
v_body_605_ = lean_ctor_get(v_e_562_, 2);
v_binderInfo_606_ = lean_ctor_get_uint8(v_e_562_, sizeof(void*)*3 + 8);
lean_inc(v_offset_563_);
lean_inc_ref(v_binderType_604_);
v___x_607_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_560_, v_d_561_, v_binderType_604_, v_offset_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v_a_609_; lean_object* v_fst_610_; lean_object* v_snd_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
v_a_609_ = lean_ctor_get(v___x_607_, 1);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_607_, 2);
v_fst_610_ = lean_ctor_get(v_a_608_, 0);
lean_inc(v_fst_610_);
v_snd_611_ = lean_ctor_get(v_a_608_, 1);
lean_inc(v_snd_611_);
lean_dec(v_a_608_);
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = lean_nat_add(v_offset_563_, v___x_612_);
lean_dec(v_offset_563_);
lean_inc_ref(v_body_605_);
v___x_614_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_560_, v_d_561_, v_body_605_, v___x_613_, v_snd_611_, v_a_565_, v_a_566_, v_a_609_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_641_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_a_616_ = lean_ctor_get(v___x_614_, 1);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_641_ == 0)
{
v___x_618_ = v___x_614_;
v_isShared_619_ = v_isSharedCheck_641_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_641_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v_fst_620_; lean_object* v_snd_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_640_; 
v_fst_620_ = lean_ctor_get(v_a_615_, 0);
v_snd_621_ = lean_ctor_get(v_a_615_, 1);
v_isSharedCheck_640_ = !lean_is_exclusive(v_a_615_);
if (v_isSharedCheck_640_ == 0)
{
v___x_623_ = v_a_615_;
v_isShared_624_ = v_isSharedCheck_640_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_snd_621_);
lean_inc(v_fst_620_);
lean_dec(v_a_615_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_640_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
uint8_t v___y_626_; size_t v___x_634_; size_t v___x_635_; uint8_t v___x_636_; 
v___x_634_ = lean_ptr_addr(v_binderType_604_);
v___x_635_ = lean_ptr_addr(v_fst_610_);
v___x_636_ = lean_usize_dec_eq(v___x_634_, v___x_635_);
if (v___x_636_ == 0)
{
v___y_626_ = v___x_636_;
goto v___jp_625_;
}
else
{
size_t v___x_637_; size_t v___x_638_; uint8_t v___x_639_; 
v___x_637_ = lean_ptr_addr(v_body_605_);
v___x_638_ = lean_ptr_addr(v_fst_620_);
v___x_639_ = lean_usize_dec_eq(v___x_637_, v___x_638_);
v___y_626_ = v___x_639_;
goto v___jp_625_;
}
v___jp_625_:
{
if (v___y_626_ == 0)
{
lean_object* v___x_627_; 
lean_inc(v_binderName_603_);
lean_del_object(v___x_623_);
lean_del_object(v___x_618_);
lean_dec_ref_known(v_e_562_, 3);
v___x_627_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_603_, v_binderInfo_606_, v_fst_610_, v_fst_620_, v_snd_621_, v_a_565_, v_a_566_, v_a_616_);
return v___x_627_;
}
else
{
lean_object* v___x_629_; 
lean_dec(v_fst_620_);
lean_dec(v_fst_610_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v_e_562_);
v___x_629_ = v___x_623_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_e_562_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_snd_621_);
v___x_629_ = v_reuseFailAlloc_633_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_629_);
v___x_631_ = v___x_618_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_a_616_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_610_);
lean_dec_ref_known(v_e_562_, 3);
return v___x_614_;
}
}
else
{
lean_dec_ref_known(v_e_562_, 3);
lean_dec(v_offset_563_);
return v___x_607_;
}
}
case 7:
{
lean_object* v_binderName_642_; lean_object* v_binderType_643_; lean_object* v_body_644_; uint8_t v_binderInfo_645_; lean_object* v___x_646_; 
v_binderName_642_ = lean_ctor_get(v_e_562_, 0);
v_binderType_643_ = lean_ctor_get(v_e_562_, 1);
v_body_644_ = lean_ctor_get(v_e_562_, 2);
v_binderInfo_645_ = lean_ctor_get_uint8(v_e_562_, sizeof(void*)*3 + 8);
lean_inc(v_offset_563_);
lean_inc_ref(v_binderType_643_);
v___x_646_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_560_, v_d_561_, v_binderType_643_, v_offset_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v_a_648_; lean_object* v_fst_649_; lean_object* v_snd_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
v_a_648_ = lean_ctor_get(v___x_646_, 1);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_646_, 2);
v_fst_649_ = lean_ctor_get(v_a_647_, 0);
lean_inc(v_fst_649_);
v_snd_650_ = lean_ctor_get(v_a_647_, 1);
lean_inc(v_snd_650_);
lean_dec(v_a_647_);
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_nat_add(v_offset_563_, v___x_651_);
lean_dec(v_offset_563_);
lean_inc_ref(v_body_644_);
v___x_653_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_560_, v_d_561_, v_body_644_, v___x_652_, v_snd_650_, v_a_565_, v_a_566_, v_a_648_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_680_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_a_655_ = lean_ctor_get(v___x_653_, 1);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_680_ == 0)
{
v___x_657_ = v___x_653_;
v_isShared_658_ = v_isSharedCheck_680_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_680_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_fst_659_; lean_object* v_snd_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_679_; 
v_fst_659_ = lean_ctor_get(v_a_654_, 0);
v_snd_660_ = lean_ctor_get(v_a_654_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v_a_654_);
if (v_isSharedCheck_679_ == 0)
{
v___x_662_ = v_a_654_;
v_isShared_663_ = v_isSharedCheck_679_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_snd_660_);
lean_inc(v_fst_659_);
lean_dec(v_a_654_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_679_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
uint8_t v___y_665_; size_t v___x_673_; size_t v___x_674_; uint8_t v___x_675_; 
v___x_673_ = lean_ptr_addr(v_binderType_643_);
v___x_674_ = lean_ptr_addr(v_fst_649_);
v___x_675_ = lean_usize_dec_eq(v___x_673_, v___x_674_);
if (v___x_675_ == 0)
{
v___y_665_ = v___x_675_;
goto v___jp_664_;
}
else
{
size_t v___x_676_; size_t v___x_677_; uint8_t v___x_678_; 
v___x_676_ = lean_ptr_addr(v_body_644_);
v___x_677_ = lean_ptr_addr(v_fst_659_);
v___x_678_ = lean_usize_dec_eq(v___x_676_, v___x_677_);
v___y_665_ = v___x_678_;
goto v___jp_664_;
}
v___jp_664_:
{
if (v___y_665_ == 0)
{
lean_object* v___x_666_; 
lean_inc(v_binderName_642_);
lean_del_object(v___x_662_);
lean_del_object(v___x_657_);
lean_dec_ref_known(v_e_562_, 3);
v___x_666_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_642_, v_binderInfo_645_, v_fst_649_, v_fst_659_, v_snd_660_, v_a_565_, v_a_566_, v_a_655_);
return v___x_666_;
}
else
{
lean_object* v___x_668_; 
lean_dec(v_fst_659_);
lean_dec(v_fst_649_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v_e_562_);
v___x_668_ = v___x_662_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_e_562_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_snd_660_);
v___x_668_ = v_reuseFailAlloc_672_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_670_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_668_);
v___x_670_ = v___x_657_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_a_655_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_649_);
lean_dec_ref_known(v_e_562_, 3);
return v___x_653_;
}
}
else
{
lean_dec_ref_known(v_e_562_, 3);
lean_dec(v_offset_563_);
return v___x_646_;
}
}
case 8:
{
lean_object* v_declName_681_; lean_object* v_type_682_; lean_object* v_value_683_; lean_object* v_body_684_; uint8_t v_nondep_685_; lean_object* v___x_686_; 
v_declName_681_ = lean_ctor_get(v_e_562_, 0);
v_type_682_ = lean_ctor_get(v_e_562_, 1);
v_value_683_ = lean_ctor_get(v_e_562_, 2);
v_body_684_ = lean_ctor_get(v_e_562_, 3);
v_nondep_685_ = lean_ctor_get_uint8(v_e_562_, sizeof(void*)*4 + 8);
lean_inc(v_offset_563_);
lean_inc_ref(v_type_682_);
v___x_686_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_560_, v_d_561_, v_type_682_, v_offset_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v_a_688_; lean_object* v_fst_689_; lean_object* v_snd_690_; lean_object* v___x_691_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
v_a_688_ = lean_ctor_get(v___x_686_, 1);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_686_, 2);
v_fst_689_ = lean_ctor_get(v_a_687_, 0);
lean_inc(v_fst_689_);
v_snd_690_ = lean_ctor_get(v_a_687_, 1);
lean_inc(v_snd_690_);
lean_dec(v_a_687_);
lean_inc(v_offset_563_);
lean_inc_ref(v_value_683_);
v___x_691_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_560_, v_d_561_, v_value_683_, v_offset_563_, v_snd_690_, v_a_565_, v_a_566_, v_a_688_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v_a_693_; lean_object* v_fst_694_; lean_object* v_snd_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
v_a_693_ = lean_ctor_get(v___x_691_, 1);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_691_, 2);
v_fst_694_ = lean_ctor_get(v_a_692_, 0);
lean_inc(v_fst_694_);
v_snd_695_ = lean_ctor_get(v_a_692_, 1);
lean_inc(v_snd_695_);
lean_dec(v_a_692_);
v___x_696_ = lean_unsigned_to_nat(1u);
v___x_697_ = lean_nat_add(v_offset_563_, v___x_696_);
lean_dec(v_offset_563_);
lean_inc_ref(v_body_684_);
v___x_698_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_560_, v_d_561_, v_body_684_, v___x_697_, v_snd_695_, v_a_565_, v_a_566_, v_a_693_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_729_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_a_700_ = lean_ctor_get(v___x_698_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_729_ == 0)
{
v___x_702_ = v___x_698_;
v_isShared_703_ = v_isSharedCheck_729_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_729_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_fst_704_; lean_object* v_snd_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_728_; 
v_fst_704_ = lean_ctor_get(v_a_699_, 0);
v_snd_705_ = lean_ctor_get(v_a_699_, 1);
v_isSharedCheck_728_ = !lean_is_exclusive(v_a_699_);
if (v_isSharedCheck_728_ == 0)
{
v___x_707_ = v_a_699_;
v_isShared_708_ = v_isSharedCheck_728_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_snd_705_);
lean_inc(v_fst_704_);
lean_dec(v_a_699_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_728_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
uint8_t v___y_710_; size_t v___x_722_; size_t v___x_723_; uint8_t v___x_724_; 
v___x_722_ = lean_ptr_addr(v_type_682_);
v___x_723_ = lean_ptr_addr(v_fst_689_);
v___x_724_ = lean_usize_dec_eq(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
v___y_710_ = v___x_724_;
goto v___jp_709_;
}
else
{
size_t v___x_725_; size_t v___x_726_; uint8_t v___x_727_; 
v___x_725_ = lean_ptr_addr(v_value_683_);
v___x_726_ = lean_ptr_addr(v_fst_694_);
v___x_727_ = lean_usize_dec_eq(v___x_725_, v___x_726_);
v___y_710_ = v___x_727_;
goto v___jp_709_;
}
v___jp_709_:
{
if (v___y_710_ == 0)
{
lean_object* v___x_711_; 
lean_inc(v_declName_681_);
lean_del_object(v___x_707_);
lean_del_object(v___x_702_);
lean_dec_ref_known(v_e_562_, 4);
v___x_711_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_681_, v_fst_689_, v_fst_694_, v_fst_704_, v_nondep_685_, v_snd_705_, v_a_565_, v_a_566_, v_a_700_);
return v___x_711_;
}
else
{
size_t v___x_712_; size_t v___x_713_; uint8_t v___x_714_; 
v___x_712_ = lean_ptr_addr(v_body_684_);
v___x_713_ = lean_ptr_addr(v_fst_704_);
v___x_714_ = lean_usize_dec_eq(v___x_712_, v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
lean_inc(v_declName_681_);
lean_del_object(v___x_707_);
lean_del_object(v___x_702_);
lean_dec_ref_known(v_e_562_, 4);
v___x_715_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_681_, v_fst_689_, v_fst_694_, v_fst_704_, v_nondep_685_, v_snd_705_, v_a_565_, v_a_566_, v_a_700_);
return v___x_715_;
}
else
{
lean_object* v___x_717_; 
lean_dec(v_fst_704_);
lean_dec(v_fst_694_);
lean_dec(v_fst_689_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v_e_562_);
v___x_717_ = v___x_707_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_e_562_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_snd_705_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_717_);
v___x_719_ = v___x_702_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_a_700_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
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
lean_dec(v_fst_694_);
lean_dec(v_fst_689_);
lean_dec_ref_known(v_e_562_, 4);
return v___x_698_;
}
}
else
{
lean_dec(v_fst_689_);
lean_dec_ref_known(v_e_562_, 4);
lean_dec(v_offset_563_);
return v___x_691_;
}
}
else
{
lean_dec_ref_known(v_e_562_, 4);
lean_dec(v_offset_563_);
return v___x_686_;
}
}
case 10:
{
lean_object* v_data_730_; lean_object* v_expr_731_; lean_object* v___x_732_; 
v_data_730_ = lean_ctor_get(v_e_562_, 0);
v_expr_731_ = lean_ctor_get(v_e_562_, 1);
lean_inc_ref(v_expr_731_);
v___x_732_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_560_, v_d_561_, v_expr_731_, v_offset_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_754_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_a_734_ = lean_ctor_get(v___x_732_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_754_ == 0)
{
v___x_736_ = v___x_732_;
v_isShared_737_ = v_isSharedCheck_754_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_754_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v_fst_738_; lean_object* v_snd_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_753_; 
v_fst_738_ = lean_ctor_get(v_a_733_, 0);
v_snd_739_ = lean_ctor_get(v_a_733_, 1);
v_isSharedCheck_753_ = !lean_is_exclusive(v_a_733_);
if (v_isSharedCheck_753_ == 0)
{
v___x_741_ = v_a_733_;
v_isShared_742_ = v_isSharedCheck_753_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_snd_739_);
lean_inc(v_fst_738_);
lean_dec(v_a_733_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_753_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
size_t v___x_743_; size_t v___x_744_; uint8_t v___x_745_; 
v___x_743_ = lean_ptr_addr(v_expr_731_);
v___x_744_ = lean_ptr_addr(v_fst_738_);
v___x_745_ = lean_usize_dec_eq(v___x_743_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
lean_inc(v_data_730_);
lean_del_object(v___x_741_);
lean_del_object(v___x_736_);
lean_dec_ref_known(v_e_562_, 2);
v___x_746_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_730_, v_fst_738_, v_snd_739_, v_a_565_, v_a_566_, v_a_734_);
return v___x_746_;
}
else
{
lean_object* v___x_748_; 
lean_dec(v_fst_738_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v_e_562_);
v___x_748_ = v___x_741_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_e_562_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_snd_739_);
v___x_748_ = v_reuseFailAlloc_752_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_750_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_748_);
v___x_750_ = v___x_736_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_a_734_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_562_, 2);
return v___x_732_;
}
}
case 11:
{
lean_object* v_typeName_755_; lean_object* v_idx_756_; lean_object* v_struct_757_; lean_object* v___x_758_; 
v_typeName_755_ = lean_ctor_get(v_e_562_, 0);
v_idx_756_ = lean_ctor_get(v_e_562_, 1);
v_struct_757_ = lean_ctor_get(v_e_562_, 2);
lean_inc_ref(v_struct_757_);
v___x_758_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_560_, v_d_561_, v_struct_757_, v_offset_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_780_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_a_760_ = lean_ctor_get(v___x_758_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_780_ == 0)
{
v___x_762_ = v___x_758_;
v_isShared_763_ = v_isSharedCheck_780_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_780_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_fst_764_; lean_object* v_snd_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_779_; 
v_fst_764_ = lean_ctor_get(v_a_759_, 0);
v_snd_765_ = lean_ctor_get(v_a_759_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v_a_759_);
if (v_isSharedCheck_779_ == 0)
{
v___x_767_ = v_a_759_;
v_isShared_768_ = v_isSharedCheck_779_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_snd_765_);
lean_inc(v_fst_764_);
lean_dec(v_a_759_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_779_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
size_t v___x_769_; size_t v___x_770_; uint8_t v___x_771_; 
v___x_769_ = lean_ptr_addr(v_struct_757_);
v___x_770_ = lean_ptr_addr(v_fst_764_);
v___x_771_ = lean_usize_dec_eq(v___x_769_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_inc(v_idx_756_);
lean_inc(v_typeName_755_);
lean_del_object(v___x_767_);
lean_del_object(v___x_762_);
lean_dec_ref_known(v_e_562_, 3);
v___x_772_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_755_, v_idx_756_, v_fst_764_, v_snd_765_, v_a_565_, v_a_566_, v_a_760_);
return v___x_772_;
}
else
{
lean_object* v___x_774_; 
lean_dec(v_fst_764_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v_e_562_);
v___x_774_ = v___x_767_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_e_562_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_snd_765_);
v___x_774_ = v_reuseFailAlloc_778_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_774_);
v___x_776_ = v___x_762_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_a_760_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_562_, 3);
return v___x_758_;
}
}
default: 
{
lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec(v_offset_563_);
lean_dec_ref(v_e_562_);
v___x_781_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
v___x_782_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_781_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
return v___x_782_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(lean_object* v_s_783_, lean_object* v_d_784_, lean_object* v_e_785_, lean_object* v_offset_786_, lean_object* v_a_787_, uint8_t v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_key_791_; lean_object* v_a_793_; lean_object* v___x_806_; 
lean_inc(v_offset_786_);
lean_inc_ref(v_e_785_);
v_key_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_791_, 0, v_e_785_);
lean_ctor_set(v_key_791_, 1, v_offset_786_);
v___x_806_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_787_, v_key_791_);
if (lean_obj_tag(v___x_806_) == 1)
{
lean_object* v_val_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec_ref_known(v_key_791_, 2);
lean_dec(v_offset_786_);
lean_dec_ref(v_e_785_);
v_val_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_val_807_);
lean_dec_ref_known(v___x_806_, 1);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v_val_807_);
lean_ctor_set(v___x_808_, 1, v_a_787_);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v_a_790_);
return v___x_809_;
}
else
{
lean_object* v_s_u2081_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
lean_dec(v___x_806_);
v_s_u2081_810_ = lean_nat_add(v_s_783_, v_offset_786_);
v___x_811_ = l_Lean_Expr_looseBVarRange(v_e_785_);
v___x_812_ = lean_nat_dec_le(v___x_811_, v_s_u2081_810_);
lean_dec(v___x_811_);
if (v___x_812_ == 0)
{
if (lean_obj_tag(v_e_785_) == 0)
{
lean_object* v_deBruijnIndex_813_; uint8_t v___x_814_; 
v_deBruijnIndex_813_ = lean_ctor_get(v_e_785_, 0);
v___x_814_ = lean_nat_dec_le(v_s_u2081_810_, v_deBruijnIndex_813_);
lean_dec(v_s_u2081_810_);
if (v___x_814_ == 0)
{
v_a_793_ = v_a_790_;
goto v___jp_792_;
}
else
{
lean_object* v___x_815_; lean_object* v___x_816_; 
lean_inc(v_deBruijnIndex_813_);
lean_dec_ref_known(v_e_785_, 1);
lean_dec(v_offset_786_);
v___x_815_ = lean_nat_sub(v_deBruijnIndex_813_, v_d_784_);
lean_dec(v_deBruijnIndex_813_);
v___x_816_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_815_, v_a_790_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v_a_818_; lean_object* v___x_819_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
v_a_818_ = lean_ctor_get(v___x_816_, 1);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_816_, 2);
v___x_819_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_791_, v_a_817_, v_a_787_, v_a_788_, v_a_789_, v_a_818_);
return v___x_819_;
}
else
{
lean_object* v_a_820_; lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec_ref_known(v_key_791_, 2);
lean_dec_ref(v_a_787_);
v_a_820_ = lean_ctor_get(v___x_816_, 0);
v_a_821_ = lean_ctor_get(v___x_816_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_816_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_inc(v_a_820_);
lean_dec(v___x_816_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_820_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
else
{
lean_dec(v_s_u2081_810_);
v_a_793_ = v_a_790_;
goto v___jp_792_;
}
}
else
{
lean_object* v___x_829_; 
lean_dec(v_s_u2081_810_);
lean_dec(v_offset_786_);
v___x_829_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_791_, v_e_785_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
return v___x_829_;
}
}
v___jp_792_:
{
switch(lean_obj_tag(v_e_785_))
{
case 9:
{
lean_object* v___x_794_; 
lean_dec(v_offset_786_);
v___x_794_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_791_, v_e_785_, v_a_787_, v_a_788_, v_a_789_, v_a_793_);
return v___x_794_;
}
case 2:
{
lean_object* v___x_795_; 
lean_dec(v_offset_786_);
v___x_795_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_791_, v_e_785_, v_a_787_, v_a_788_, v_a_789_, v_a_793_);
return v___x_795_;
}
case 0:
{
lean_object* v___x_796_; 
lean_dec(v_offset_786_);
v___x_796_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_791_, v_e_785_, v_a_787_, v_a_788_, v_a_789_, v_a_793_);
return v___x_796_;
}
case 1:
{
lean_object* v___x_797_; 
lean_dec(v_offset_786_);
v___x_797_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_791_, v_e_785_, v_a_787_, v_a_788_, v_a_789_, v_a_793_);
return v___x_797_;
}
case 4:
{
lean_object* v___x_798_; 
lean_dec(v_offset_786_);
v___x_798_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_791_, v_e_785_, v_a_787_, v_a_788_, v_a_789_, v_a_793_);
return v___x_798_;
}
case 3:
{
lean_object* v___x_799_; 
lean_dec(v_offset_786_);
v___x_799_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_791_, v_e_785_, v_a_787_, v_a_788_, v_a_789_, v_a_793_);
return v___x_799_;
}
default: 
{
lean_object* v___x_800_; 
v___x_800_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_783_, v_d_784_, v_e_785_, v_offset_786_, v_a_787_, v_a_788_, v_a_789_, v_a_793_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v_a_802_; lean_object* v_fst_803_; lean_object* v_snd_804_; lean_object* v___x_805_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
v_a_802_ = lean_ctor_get(v___x_800_, 1);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_800_, 2);
v_fst_803_ = lean_ctor_get(v_a_801_, 0);
lean_inc(v_fst_803_);
v_snd_804_ = lean_ctor_get(v_a_801_, 1);
lean_inc(v_snd_804_);
lean_dec(v_a_801_);
v___x_805_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_791_, v_fst_803_, v_snd_804_, v_a_788_, v_a_789_, v_a_802_);
return v___x_805_;
}
else
{
lean_dec_ref_known(v_key_791_, 2);
return v___x_800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1___boxed(lean_object* v_s_830_, lean_object* v_d_831_, lean_object* v_e_832_, lean_object* v_offset_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
uint8_t v_a_boxed_838_; lean_object* v_res_839_; 
v_a_boxed_838_ = lean_unbox(v_a_835_);
v_res_839_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_830_, v_d_831_, v_e_832_, v_offset_833_, v_a_834_, v_a_boxed_838_, v_a_836_, v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_d_831_);
lean_dec(v_s_830_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___boxed(lean_object* v_s_840_, lean_object* v_d_841_, lean_object* v_e_842_, lean_object* v_offset_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
uint8_t v_a_boxed_848_; lean_object* v_res_849_; 
v_a_boxed_848_ = lean_unbox(v_a_845_);
v_res_849_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_840_, v_d_841_, v_e_842_, v_offset_843_, v_a_844_, v_a_boxed_848_, v_a_846_, v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_d_841_);
lean_dec(v_s_840_);
return v_res_849_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0(void){
_start:
{
lean_object* v_cellCount_850_; lean_object* v___x_851_; 
v_cellCount_850_ = lean_unsigned_to_nat(16u);
v___x_851_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_850_);
return v___x_851_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1(void){
_start:
{
lean_object* v_cellCount_852_; lean_object* v___x_853_; 
v_cellCount_852_ = lean_unsigned_to_nat(16u);
v___x_853_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_852_);
return v___x_853_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__2(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_854_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1);
v___x_855_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v___x_855_);
lean_ctor_set(v___x_857_, 2, v___x_854_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27(lean_object* v_e_858_, lean_object* v_s_859_, lean_object* v_d_860_, uint8_t v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = l_Lean_Expr_looseBVarRange(v_e_858_);
v___x_865_ = lean_nat_dec_le(v___x_864_, v_s_859_);
lean_dec(v___x_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; lean_object* v_a_868_; 
v___x_866_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_e_858_) == 0)
{
lean_object* v_deBruijnIndex_896_; uint8_t v___x_897_; 
v_deBruijnIndex_896_ = lean_ctor_get(v_e_858_, 0);
v___x_897_ = lean_nat_dec_le(v_s_859_, v_deBruijnIndex_896_);
if (v___x_897_ == 0)
{
v_a_868_ = v_a_863_;
goto v___jp_867_;
}
else
{
lean_object* v___x_898_; lean_object* v___x_899_; 
lean_inc(v_deBruijnIndex_896_);
lean_dec_ref_known(v_e_858_, 1);
v___x_898_ = lean_nat_sub(v_deBruijnIndex_896_, v_d_860_);
lean_dec(v_deBruijnIndex_896_);
v___x_899_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_898_, v_a_863_);
return v___x_899_;
}
}
else
{
v_a_868_ = v_a_863_;
goto v___jp_867_;
}
v___jp_867_:
{
switch(lean_obj_tag(v_e_858_))
{
case 9:
{
lean_object* v___x_869_; 
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v_e_858_);
lean_ctor_set(v___x_869_, 1, v_a_868_);
return v___x_869_;
}
case 2:
{
lean_object* v___x_870_; 
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v_e_858_);
lean_ctor_set(v___x_870_, 1, v_a_868_);
return v___x_870_;
}
case 0:
{
lean_object* v___x_871_; 
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v_e_858_);
lean_ctor_set(v___x_871_, 1, v_a_868_);
return v___x_871_;
}
case 1:
{
lean_object* v___x_872_; 
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v_e_858_);
lean_ctor_set(v___x_872_, 1, v_a_868_);
return v___x_872_;
}
case 4:
{
lean_object* v___x_873_; 
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v_e_858_);
lean_ctor_set(v___x_873_, 1, v_a_868_);
return v___x_873_;
}
case 3:
{
lean_object* v___x_874_; 
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v_e_858_);
lean_ctor_set(v___x_874_, 1, v_a_868_);
return v___x_874_;
}
default: 
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__2, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__2_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__2);
v___x_876_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_859_, v_d_860_, v_e_858_, v___x_866_, v___x_875_, v_a_861_, v_a_862_, v_a_868_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_886_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_a_878_ = lean_ctor_get(v___x_876_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_886_ == 0)
{
v___x_880_ = v___x_876_;
v_isShared_881_ = v_isSharedCheck_886_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_886_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_fst_882_; lean_object* v___x_884_; 
v_fst_882_ = lean_ctor_get(v_a_877_, 0);
lean_inc(v_fst_882_);
lean_dec(v_a_877_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v_fst_882_);
v___x_884_ = v___x_880_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_fst_882_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_a_878_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
else
{
lean_object* v_a_887_; lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
v_a_887_ = lean_ctor_get(v___x_876_, 0);
v_a_888_ = lean_ctor_get(v___x_876_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_876_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_inc(v_a_887_);
lean_dec(v___x_876_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_887_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_900_; 
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v_e_858_);
lean_ctor_set(v___x_900_, 1, v_a_863_);
return v___x_900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed(lean_object* v_e_901_, lean_object* v_s_902_, lean_object* v_d_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
uint8_t v_a_boxed_907_; lean_object* v_res_908_; 
v_a_boxed_907_ = lean_unbox(v_a_904_);
v_res_908_ = l_Lean_Meta_Sym_lowerLooseBVarsS_x27(v_e_901_, v_s_902_, v_d_903_, v_a_boxed_907_, v_a_905_, v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_d_903_);
lean_dec(v_s_902_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_909_, lean_object* v_m_910_, lean_object* v_a_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_910_, v_a_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_913_, lean_object* v_m_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(v_00_u03b2_913_, v_m_914_, v_a_915_);
lean_dec_ref(v_a_915_);
lean_dec_ref(v_m_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(lean_object* v_00_u03b2_917_, lean_object* v_m_918_, lean_object* v_query_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_m_918_, v_query_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___boxed(lean_object* v_00_u03b2_921_, lean_object* v_m_922_, lean_object* v_query_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(v_00_u03b2_921_, v_m_922_, v_query_923_);
lean_dec_ref(v_query_923_);
lean_dec_ref(v_m_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11(lean_object* v_00_u03b2_925_, lean_object* v_m_926_, lean_object* v_query_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11___redArg(v_m_926_, v_query_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11___boxed(lean_object* v_00_u03b2_929_, lean_object* v_m_930_, lean_object* v_query_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11(v_00_u03b2_929_, v_m_930_, v_query_931_);
lean_dec_ref(v_query_931_);
lean_dec_ref(v_m_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_933_, lean_object* v_m_934_, lean_object* v_query_935_, lean_object* v_x_936_, lean_object* v_x_937_, lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11_spec__12___redArg(v_m_934_, v_query_935_, v_x_936_, v_x_937_, v_x_938_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11_spec__12___boxed(lean_object* v_00_u03b2_941_, lean_object* v_m_942_, lean_object* v_query_943_, lean_object* v_x_944_, lean_object* v_x_945_, lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10_spec__11_spec__12(v_00_u03b2_941_, v_m_942_, v_query_943_, v_x_944_, v_x_945_, v_x_946_, v_x_947_);
lean_dec_ref(v_query_943_);
lean_dec_ref(v_m_942_);
return v_res_948_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0(void){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(lean_object* v_msg_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___x_958_; lean_object* v___x_44__overap_959_; lean_object* v___x_960_; 
v___x_958_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0);
v___x_44__overap_959_ = lean_panic_fn_borrowed(v___x_958_, v_msg_950_);
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
lean_inc(v___y_954_);
lean_inc_ref(v___y_953_);
lean_inc(v___y_952_);
lean_inc_ref(v___y_951_);
v___x_960_ = lean_apply_7(v___x_44__overap_959_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, lean_box(0));
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___boxed(lean_object* v_msg_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(v_msg_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
return v_res_969_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_972_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2));
v___x_973_ = lean_unsigned_to_nat(16u);
v___x_974_ = lean_unsigned_to_nat(62u);
v___x_975_ = ((lean_object*)(l_Lean_Meta_Sym_lowerLooseBVarsS___closed__1));
v___x_976_ = ((lean_object*)(l_Lean_Meta_Sym_lowerLooseBVarsS___closed__0));
v___x_977_ = l_mkPanicMessageWithDecl(v___x_976_, v___x_975_, v___x_974_, v___x_973_, v___x_972_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS(lean_object* v_e_978_, lean_object* v_s_979_, lean_object* v_d_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v_debug_990_; lean_object* v_env_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_988_ = lean_st_ref_get(v_a_982_);
v___x_989_ = lean_st_ref_get(v_a_986_);
v_debug_990_ = lean_ctor_get_uint8(v___x_988_, sizeof(void*)*11);
lean_dec(v___x_988_);
v_env_991_ = lean_ctor_get(v___x_989_, 0);
lean_inc_ref(v_env_991_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(v_debug_990_);
v___x_993_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed), 6, 4);
lean_closure_set(v___x_993_, 0, v_e_978_);
lean_closure_set(v___x_993_, 1, v_s_979_);
lean_closure_set(v___x_993_, 2, v_d_980_);
lean_closure_set(v___x_993_, 3, v___x_992_);
v___x_994_ = 0;
v___x_995_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_995_, 0, v_env_991_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*1, v___x_994_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*1 + 1, v___x_994_);
v___x_996_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_993_, v___x_995_, v_a_982_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1007_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1007_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1007_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
if (lean_obj_tag(v_a_997_) == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_dec_ref_known(v_a_997_, 1);
lean_del_object(v___x_999_);
v___x_1001_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2, &l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2);
v___x_1002_ = l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(v___x_1001_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
return v___x_1002_;
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; 
v_a_1003_ = lean_ctor_get(v_a_997_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v_a_997_, 1);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v_a_1003_);
v___x_1005_ = v___x_999_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
v_a_1008_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_996_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_996_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___boxed(lean_object* v_e_1016_, lean_object* v_s_1017_, lean_object* v_d_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Meta_Sym_lowerLooseBVarsS(v_e_1016_, v_s_1017_, v_d_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(lean_object* v_s_1027_, lean_object* v_d_1028_, lean_object* v_e_1029_, lean_object* v_offset_1030_, lean_object* v_a_1031_, uint8_t v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
switch(lean_obj_tag(v_e_1029_))
{
case 5:
{
lean_object* v_fn_1035_; lean_object* v_arg_1036_; lean_object* v___x_1037_; 
v_fn_1035_ = lean_ctor_get(v_e_1029_, 0);
v_arg_1036_ = lean_ctor_get(v_e_1029_, 1);
lean_inc(v_offset_1030_);
lean_inc_ref(v_fn_1035_);
v___x_1037_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1027_, v_d_1028_, v_fn_1035_, v_offset_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v_a_1039_; lean_object* v_fst_1040_; lean_object* v_snd_1041_; lean_object* v___x_1042_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
v_a_1039_ = lean_ctor_get(v___x_1037_, 1);
lean_inc(v_a_1039_);
lean_dec_ref_known(v___x_1037_, 2);
v_fst_1040_ = lean_ctor_get(v_a_1038_, 0);
lean_inc(v_fst_1040_);
v_snd_1041_ = lean_ctor_get(v_a_1038_, 1);
lean_inc(v_snd_1041_);
lean_dec(v_a_1038_);
lean_inc_ref(v_arg_1036_);
v___x_1042_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1027_, v_d_1028_, v_arg_1036_, v_offset_1030_, v_snd_1041_, v_a_1032_, v_a_1033_, v_a_1039_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1069_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_a_1044_ = lean_ctor_get(v___x_1042_, 1);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1046_ = v___x_1042_;
v_isShared_1047_ = v_isSharedCheck_1069_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1069_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v_fst_1048_; lean_object* v_snd_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1068_; 
v_fst_1048_ = lean_ctor_get(v_a_1043_, 0);
v_snd_1049_ = lean_ctor_get(v_a_1043_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_a_1043_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1051_ = v_a_1043_;
v_isShared_1052_ = v_isSharedCheck_1068_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_snd_1049_);
lean_inc(v_fst_1048_);
lean_dec(v_a_1043_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1068_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
uint8_t v___y_1054_; size_t v___x_1062_; size_t v___x_1063_; uint8_t v___x_1064_; 
v___x_1062_ = lean_ptr_addr(v_fn_1035_);
v___x_1063_ = lean_ptr_addr(v_fst_1040_);
v___x_1064_ = lean_usize_dec_eq(v___x_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
v___y_1054_ = v___x_1064_;
goto v___jp_1053_;
}
else
{
size_t v___x_1065_; size_t v___x_1066_; uint8_t v___x_1067_; 
v___x_1065_ = lean_ptr_addr(v_arg_1036_);
v___x_1066_ = lean_ptr_addr(v_fst_1048_);
v___x_1067_ = lean_usize_dec_eq(v___x_1065_, v___x_1066_);
v___y_1054_ = v___x_1067_;
goto v___jp_1053_;
}
v___jp_1053_:
{
if (v___y_1054_ == 0)
{
lean_object* v___x_1055_; 
lean_del_object(v___x_1051_);
lean_del_object(v___x_1046_);
lean_dec_ref_known(v_e_1029_, 2);
v___x_1055_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_1040_, v_fst_1048_, v_snd_1049_, v_a_1032_, v_a_1033_, v_a_1044_);
return v___x_1055_;
}
else
{
lean_object* v___x_1057_; 
lean_dec(v_fst_1048_);
lean_dec(v_fst_1040_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v_e_1029_);
v___x_1057_ = v___x_1051_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_e_1029_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_snd_1049_);
v___x_1057_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1059_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1057_);
v___x_1059_ = v___x_1046_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_a_1044_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1040_);
lean_dec_ref_known(v_e_1029_, 2);
return v___x_1042_;
}
}
else
{
lean_dec_ref_known(v_e_1029_, 2);
lean_dec(v_offset_1030_);
return v___x_1037_;
}
}
case 6:
{
lean_object* v_binderName_1070_; lean_object* v_binderType_1071_; lean_object* v_body_1072_; uint8_t v_binderInfo_1073_; lean_object* v___x_1074_; 
v_binderName_1070_ = lean_ctor_get(v_e_1029_, 0);
v_binderType_1071_ = lean_ctor_get(v_e_1029_, 1);
v_body_1072_ = lean_ctor_get(v_e_1029_, 2);
v_binderInfo_1073_ = lean_ctor_get_uint8(v_e_1029_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1030_);
lean_inc_ref(v_binderType_1071_);
v___x_1074_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1027_, v_d_1028_, v_binderType_1071_, v_offset_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v_a_1076_; lean_object* v_fst_1077_; lean_object* v_snd_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
v_a_1076_ = lean_ctor_get(v___x_1074_, 1);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1074_, 2);
v_fst_1077_ = lean_ctor_get(v_a_1075_, 0);
lean_inc(v_fst_1077_);
v_snd_1078_ = lean_ctor_get(v_a_1075_, 1);
lean_inc(v_snd_1078_);
lean_dec(v_a_1075_);
v___x_1079_ = lean_unsigned_to_nat(1u);
v___x_1080_ = lean_nat_add(v_offset_1030_, v___x_1079_);
lean_dec(v_offset_1030_);
lean_inc_ref(v_body_1072_);
v___x_1081_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1027_, v_d_1028_, v_body_1072_, v___x_1080_, v_snd_1078_, v_a_1032_, v_a_1033_, v_a_1076_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1108_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_a_1083_ = lean_ctor_get(v___x_1081_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1085_ = v___x_1081_;
v_isShared_1086_ = v_isSharedCheck_1108_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1108_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v_fst_1087_; lean_object* v_snd_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1107_; 
v_fst_1087_ = lean_ctor_get(v_a_1082_, 0);
v_snd_1088_ = lean_ctor_get(v_a_1082_, 1);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_a_1082_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1090_ = v_a_1082_;
v_isShared_1091_ = v_isSharedCheck_1107_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_snd_1088_);
lean_inc(v_fst_1087_);
lean_dec(v_a_1082_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1107_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
uint8_t v___y_1093_; size_t v___x_1101_; size_t v___x_1102_; uint8_t v___x_1103_; 
v___x_1101_ = lean_ptr_addr(v_binderType_1071_);
v___x_1102_ = lean_ptr_addr(v_fst_1077_);
v___x_1103_ = lean_usize_dec_eq(v___x_1101_, v___x_1102_);
if (v___x_1103_ == 0)
{
v___y_1093_ = v___x_1103_;
goto v___jp_1092_;
}
else
{
size_t v___x_1104_; size_t v___x_1105_; uint8_t v___x_1106_; 
v___x_1104_ = lean_ptr_addr(v_body_1072_);
v___x_1105_ = lean_ptr_addr(v_fst_1087_);
v___x_1106_ = lean_usize_dec_eq(v___x_1104_, v___x_1105_);
v___y_1093_ = v___x_1106_;
goto v___jp_1092_;
}
v___jp_1092_:
{
if (v___y_1093_ == 0)
{
lean_object* v___x_1094_; 
lean_inc(v_binderName_1070_);
lean_del_object(v___x_1090_);
lean_del_object(v___x_1085_);
lean_dec_ref_known(v_e_1029_, 3);
v___x_1094_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_1070_, v_binderInfo_1073_, v_fst_1077_, v_fst_1087_, v_snd_1088_, v_a_1032_, v_a_1033_, v_a_1083_);
return v___x_1094_;
}
else
{
lean_object* v___x_1096_; 
lean_dec(v_fst_1087_);
lean_dec(v_fst_1077_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v_e_1029_);
v___x_1096_ = v___x_1090_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_e_1029_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_snd_1088_);
v___x_1096_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1098_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1096_);
v___x_1098_ = v___x_1085_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_a_1083_);
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
else
{
lean_dec(v_fst_1077_);
lean_dec_ref_known(v_e_1029_, 3);
return v___x_1081_;
}
}
else
{
lean_dec_ref_known(v_e_1029_, 3);
lean_dec(v_offset_1030_);
return v___x_1074_;
}
}
case 7:
{
lean_object* v_binderName_1109_; lean_object* v_binderType_1110_; lean_object* v_body_1111_; uint8_t v_binderInfo_1112_; lean_object* v___x_1113_; 
v_binderName_1109_ = lean_ctor_get(v_e_1029_, 0);
v_binderType_1110_ = lean_ctor_get(v_e_1029_, 1);
v_body_1111_ = lean_ctor_get(v_e_1029_, 2);
v_binderInfo_1112_ = lean_ctor_get_uint8(v_e_1029_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1030_);
lean_inc_ref(v_binderType_1110_);
v___x_1113_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1027_, v_d_1028_, v_binderType_1110_, v_offset_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v_a_1115_; lean_object* v_fst_1116_; lean_object* v_snd_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
v_a_1115_ = lean_ctor_get(v___x_1113_, 1);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1113_, 2);
v_fst_1116_ = lean_ctor_get(v_a_1114_, 0);
lean_inc(v_fst_1116_);
v_snd_1117_ = lean_ctor_get(v_a_1114_, 1);
lean_inc(v_snd_1117_);
lean_dec(v_a_1114_);
v___x_1118_ = lean_unsigned_to_nat(1u);
v___x_1119_ = lean_nat_add(v_offset_1030_, v___x_1118_);
lean_dec(v_offset_1030_);
lean_inc_ref(v_body_1111_);
v___x_1120_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1027_, v_d_1028_, v_body_1111_, v___x_1119_, v_snd_1117_, v_a_1032_, v_a_1033_, v_a_1115_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1147_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
v_a_1122_ = lean_ctor_get(v___x_1120_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1124_ = v___x_1120_;
v_isShared_1125_ = v_isSharedCheck_1147_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_inc(v_a_1121_);
lean_dec(v___x_1120_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1147_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_fst_1126_; lean_object* v_snd_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1146_; 
v_fst_1126_ = lean_ctor_get(v_a_1121_, 0);
v_snd_1127_ = lean_ctor_get(v_a_1121_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_a_1121_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1129_ = v_a_1121_;
v_isShared_1130_ = v_isSharedCheck_1146_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_snd_1127_);
lean_inc(v_fst_1126_);
lean_dec(v_a_1121_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1146_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint8_t v___y_1132_; size_t v___x_1140_; size_t v___x_1141_; uint8_t v___x_1142_; 
v___x_1140_ = lean_ptr_addr(v_binderType_1110_);
v___x_1141_ = lean_ptr_addr(v_fst_1116_);
v___x_1142_ = lean_usize_dec_eq(v___x_1140_, v___x_1141_);
if (v___x_1142_ == 0)
{
v___y_1132_ = v___x_1142_;
goto v___jp_1131_;
}
else
{
size_t v___x_1143_; size_t v___x_1144_; uint8_t v___x_1145_; 
v___x_1143_ = lean_ptr_addr(v_body_1111_);
v___x_1144_ = lean_ptr_addr(v_fst_1126_);
v___x_1145_ = lean_usize_dec_eq(v___x_1143_, v___x_1144_);
v___y_1132_ = v___x_1145_;
goto v___jp_1131_;
}
v___jp_1131_:
{
if (v___y_1132_ == 0)
{
lean_object* v___x_1133_; 
lean_inc(v_binderName_1109_);
lean_del_object(v___x_1129_);
lean_del_object(v___x_1124_);
lean_dec_ref_known(v_e_1029_, 3);
v___x_1133_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_1109_, v_binderInfo_1112_, v_fst_1116_, v_fst_1126_, v_snd_1127_, v_a_1032_, v_a_1033_, v_a_1122_);
return v___x_1133_;
}
else
{
lean_object* v___x_1135_; 
lean_dec(v_fst_1126_);
lean_dec(v_fst_1116_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v_e_1029_);
v___x_1135_ = v___x_1129_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_e_1029_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_snd_1127_);
v___x_1135_ = v_reuseFailAlloc_1139_;
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
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_a_1122_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1116_);
lean_dec_ref_known(v_e_1029_, 3);
return v___x_1120_;
}
}
else
{
lean_dec_ref_known(v_e_1029_, 3);
lean_dec(v_offset_1030_);
return v___x_1113_;
}
}
case 8:
{
lean_object* v_declName_1148_; lean_object* v_type_1149_; lean_object* v_value_1150_; lean_object* v_body_1151_; uint8_t v_nondep_1152_; lean_object* v___x_1153_; 
v_declName_1148_ = lean_ctor_get(v_e_1029_, 0);
v_type_1149_ = lean_ctor_get(v_e_1029_, 1);
v_value_1150_ = lean_ctor_get(v_e_1029_, 2);
v_body_1151_ = lean_ctor_get(v_e_1029_, 3);
v_nondep_1152_ = lean_ctor_get_uint8(v_e_1029_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1030_);
lean_inc_ref(v_type_1149_);
v___x_1153_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1027_, v_d_1028_, v_type_1149_, v_offset_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v_a_1155_; lean_object* v_fst_1156_; lean_object* v_snd_1157_; lean_object* v___x_1158_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_a_1154_);
v_a_1155_ = lean_ctor_get(v___x_1153_, 1);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1153_, 2);
v_fst_1156_ = lean_ctor_get(v_a_1154_, 0);
lean_inc(v_fst_1156_);
v_snd_1157_ = lean_ctor_get(v_a_1154_, 1);
lean_inc(v_snd_1157_);
lean_dec(v_a_1154_);
lean_inc(v_offset_1030_);
lean_inc_ref(v_value_1150_);
v___x_1158_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1027_, v_d_1028_, v_value_1150_, v_offset_1030_, v_snd_1157_, v_a_1032_, v_a_1033_, v_a_1155_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v_a_1160_; lean_object* v_fst_1161_; lean_object* v_snd_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
v_a_1160_ = lean_ctor_get(v___x_1158_, 1);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1158_, 2);
v_fst_1161_ = lean_ctor_get(v_a_1159_, 0);
lean_inc(v_fst_1161_);
v_snd_1162_ = lean_ctor_get(v_a_1159_, 1);
lean_inc(v_snd_1162_);
lean_dec(v_a_1159_);
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_add(v_offset_1030_, v___x_1163_);
lean_dec(v_offset_1030_);
lean_inc_ref(v_body_1151_);
v___x_1165_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1027_, v_d_1028_, v_body_1151_, v___x_1164_, v_snd_1162_, v_a_1032_, v_a_1033_, v_a_1160_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1196_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_a_1167_ = lean_ctor_get(v___x_1165_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1169_ = v___x_1165_;
v_isShared_1170_ = v_isSharedCheck_1196_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1196_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_fst_1171_; lean_object* v_snd_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1195_; 
v_fst_1171_ = lean_ctor_get(v_a_1166_, 0);
v_snd_1172_ = lean_ctor_get(v_a_1166_, 1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_a_1166_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1174_ = v_a_1166_;
v_isShared_1175_ = v_isSharedCheck_1195_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_snd_1172_);
lean_inc(v_fst_1171_);
lean_dec(v_a_1166_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1195_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
uint8_t v___y_1177_; size_t v___x_1189_; size_t v___x_1190_; uint8_t v___x_1191_; 
v___x_1189_ = lean_ptr_addr(v_type_1149_);
v___x_1190_ = lean_ptr_addr(v_fst_1156_);
v___x_1191_ = lean_usize_dec_eq(v___x_1189_, v___x_1190_);
if (v___x_1191_ == 0)
{
v___y_1177_ = v___x_1191_;
goto v___jp_1176_;
}
else
{
size_t v___x_1192_; size_t v___x_1193_; uint8_t v___x_1194_; 
v___x_1192_ = lean_ptr_addr(v_value_1150_);
v___x_1193_ = lean_ptr_addr(v_fst_1161_);
v___x_1194_ = lean_usize_dec_eq(v___x_1192_, v___x_1193_);
v___y_1177_ = v___x_1194_;
goto v___jp_1176_;
}
v___jp_1176_:
{
if (v___y_1177_ == 0)
{
lean_object* v___x_1178_; 
lean_inc(v_declName_1148_);
lean_del_object(v___x_1174_);
lean_del_object(v___x_1169_);
lean_dec_ref_known(v_e_1029_, 4);
v___x_1178_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1148_, v_fst_1156_, v_fst_1161_, v_fst_1171_, v_nondep_1152_, v_snd_1172_, v_a_1032_, v_a_1033_, v_a_1167_);
return v___x_1178_;
}
else
{
size_t v___x_1179_; size_t v___x_1180_; uint8_t v___x_1181_; 
v___x_1179_ = lean_ptr_addr(v_body_1151_);
v___x_1180_ = lean_ptr_addr(v_fst_1171_);
v___x_1181_ = lean_usize_dec_eq(v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
lean_inc(v_declName_1148_);
lean_del_object(v___x_1174_);
lean_del_object(v___x_1169_);
lean_dec_ref_known(v_e_1029_, 4);
v___x_1182_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1148_, v_fst_1156_, v_fst_1161_, v_fst_1171_, v_nondep_1152_, v_snd_1172_, v_a_1032_, v_a_1033_, v_a_1167_);
return v___x_1182_;
}
else
{
lean_object* v___x_1184_; 
lean_dec(v_fst_1171_);
lean_dec(v_fst_1161_);
lean_dec(v_fst_1156_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v_e_1029_);
v___x_1184_ = v___x_1174_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_e_1029_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_snd_1172_);
v___x_1184_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1186_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1184_);
v___x_1186_ = v___x_1169_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_a_1167_);
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
}
}
}
else
{
lean_dec(v_fst_1161_);
lean_dec(v_fst_1156_);
lean_dec_ref_known(v_e_1029_, 4);
return v___x_1165_;
}
}
else
{
lean_dec(v_fst_1156_);
lean_dec_ref_known(v_e_1029_, 4);
lean_dec(v_offset_1030_);
return v___x_1158_;
}
}
else
{
lean_dec_ref_known(v_e_1029_, 4);
lean_dec(v_offset_1030_);
return v___x_1153_;
}
}
case 10:
{
lean_object* v_data_1197_; lean_object* v_expr_1198_; lean_object* v___x_1199_; 
v_data_1197_ = lean_ctor_get(v_e_1029_, 0);
v_expr_1198_ = lean_ctor_get(v_e_1029_, 1);
lean_inc_ref(v_expr_1198_);
v___x_1199_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1027_, v_d_1028_, v_expr_1198_, v_offset_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1221_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
v_a_1201_ = lean_ctor_get(v___x_1199_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1203_ = v___x_1199_;
v_isShared_1204_ = v_isSharedCheck_1221_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_inc(v_a_1200_);
lean_dec(v___x_1199_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1221_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_fst_1205_; lean_object* v_snd_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1220_; 
v_fst_1205_ = lean_ctor_get(v_a_1200_, 0);
v_snd_1206_ = lean_ctor_get(v_a_1200_, 1);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_a_1200_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1208_ = v_a_1200_;
v_isShared_1209_ = v_isSharedCheck_1220_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_snd_1206_);
lean_inc(v_fst_1205_);
lean_dec(v_a_1200_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1220_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
size_t v___x_1210_; size_t v___x_1211_; uint8_t v___x_1212_; 
v___x_1210_ = lean_ptr_addr(v_expr_1198_);
v___x_1211_ = lean_ptr_addr(v_fst_1205_);
v___x_1212_ = lean_usize_dec_eq(v___x_1210_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_inc(v_data_1197_);
lean_del_object(v___x_1208_);
lean_del_object(v___x_1203_);
lean_dec_ref_known(v_e_1029_, 2);
v___x_1213_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_1197_, v_fst_1205_, v_snd_1206_, v_a_1032_, v_a_1033_, v_a_1201_);
return v___x_1213_;
}
else
{
lean_object* v___x_1215_; 
lean_dec(v_fst_1205_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v_e_1029_);
v___x_1215_ = v___x_1208_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_e_1029_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_snd_1206_);
v___x_1215_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1217_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1215_);
v___x_1217_ = v___x_1203_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_a_1201_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1029_, 2);
return v___x_1199_;
}
}
case 11:
{
lean_object* v_typeName_1222_; lean_object* v_idx_1223_; lean_object* v_struct_1224_; lean_object* v___x_1225_; 
v_typeName_1222_ = lean_ctor_get(v_e_1029_, 0);
v_idx_1223_ = lean_ctor_get(v_e_1029_, 1);
v_struct_1224_ = lean_ctor_get(v_e_1029_, 2);
lean_inc_ref(v_struct_1224_);
v___x_1225_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1027_, v_d_1028_, v_struct_1224_, v_offset_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1247_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_a_1227_ = lean_ctor_get(v___x_1225_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1229_ = v___x_1225_;
v_isShared_1230_ = v_isSharedCheck_1247_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1247_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v_fst_1231_; lean_object* v_snd_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1246_; 
v_fst_1231_ = lean_ctor_get(v_a_1226_, 0);
v_snd_1232_ = lean_ctor_get(v_a_1226_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_a_1226_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1234_ = v_a_1226_;
v_isShared_1235_ = v_isSharedCheck_1246_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_snd_1232_);
lean_inc(v_fst_1231_);
lean_dec(v_a_1226_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1246_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
size_t v___x_1236_; size_t v___x_1237_; uint8_t v___x_1238_; 
v___x_1236_ = lean_ptr_addr(v_struct_1224_);
v___x_1237_ = lean_ptr_addr(v_fst_1231_);
v___x_1238_ = lean_usize_dec_eq(v___x_1236_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_inc(v_idx_1223_);
lean_inc(v_typeName_1222_);
lean_del_object(v___x_1234_);
lean_del_object(v___x_1229_);
lean_dec_ref_known(v_e_1029_, 3);
v___x_1239_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_1222_, v_idx_1223_, v_fst_1231_, v_snd_1232_, v_a_1032_, v_a_1033_, v_a_1227_);
return v___x_1239_;
}
else
{
lean_object* v___x_1241_; 
lean_dec(v_fst_1231_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v_e_1029_);
v___x_1241_ = v___x_1234_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_e_1029_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_snd_1232_);
v___x_1241_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1243_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1241_);
v___x_1243_ = v___x_1229_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_a_1227_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1029_, 3);
return v___x_1225_;
}
}
default: 
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
lean_dec(v_offset_1030_);
lean_dec_ref(v_e_1029_);
v___x_1248_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
v___x_1249_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_1248_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
return v___x_1249_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(lean_object* v_s_1250_, lean_object* v_d_1251_, lean_object* v_e_1252_, lean_object* v_offset_1253_, lean_object* v_a_1254_, uint8_t v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v_key_1258_; lean_object* v_a_1260_; lean_object* v___x_1273_; 
lean_inc(v_offset_1253_);
lean_inc_ref(v_e_1252_);
v_key_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1258_, 0, v_e_1252_);
lean_ctor_set(v_key_1258_, 1, v_offset_1253_);
v___x_1273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_1254_, v_key_1258_);
if (lean_obj_tag(v___x_1273_) == 1)
{
lean_object* v_val_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_dec_ref_known(v_key_1258_, 2);
lean_dec(v_offset_1253_);
lean_dec_ref(v_e_1252_);
v_val_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_val_1274_);
lean_dec_ref_known(v___x_1273_, 1);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v_val_1274_);
lean_ctor_set(v___x_1275_, 1, v_a_1254_);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v_a_1257_);
return v___x_1276_;
}
else
{
lean_object* v_s_u2081_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
lean_dec(v___x_1273_);
v_s_u2081_1277_ = lean_nat_add(v_s_1250_, v_offset_1253_);
v___x_1278_ = l_Lean_Expr_looseBVarRange(v_e_1252_);
v___x_1279_ = lean_nat_dec_le(v___x_1278_, v_s_u2081_1277_);
lean_dec(v___x_1278_);
if (v___x_1279_ == 0)
{
if (lean_obj_tag(v_e_1252_) == 0)
{
lean_object* v_deBruijnIndex_1280_; uint8_t v___x_1281_; 
v_deBruijnIndex_1280_ = lean_ctor_get(v_e_1252_, 0);
v___x_1281_ = lean_nat_dec_le(v_s_u2081_1277_, v_deBruijnIndex_1280_);
lean_dec(v_s_u2081_1277_);
if (v___x_1281_ == 0)
{
v_a_1260_ = v_a_1257_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
lean_inc(v_deBruijnIndex_1280_);
lean_dec_ref_known(v_e_1252_, 1);
lean_dec(v_offset_1253_);
v___x_1282_ = lean_nat_add(v_deBruijnIndex_1280_, v_d_1251_);
lean_dec(v_deBruijnIndex_1280_);
v___x_1283_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_1282_, v_a_1257_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v_a_1285_; lean_object* v___x_1286_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
v_a_1285_ = lean_ctor_get(v___x_1283_, 1);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1283_, 2);
v___x_1286_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1258_, v_a_1284_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1285_);
return v___x_1286_;
}
else
{
lean_object* v_a_1287_; lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref_known(v_key_1258_, 2);
lean_dec_ref(v_a_1254_);
v_a_1287_ = lean_ctor_get(v___x_1283_, 0);
v_a_1288_ = lean_ctor_get(v___x_1283_, 1);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1283_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_inc(v_a_1287_);
lean_dec(v___x_1283_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1287_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
else
{
lean_dec(v_s_u2081_1277_);
v_a_1260_ = v_a_1257_;
goto v___jp_1259_;
}
}
else
{
lean_object* v___x_1296_; 
lean_dec(v_s_u2081_1277_);
lean_dec(v_offset_1253_);
v___x_1296_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1258_, v_e_1252_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
return v___x_1296_;
}
}
v___jp_1259_:
{
switch(lean_obj_tag(v_e_1252_))
{
case 9:
{
lean_object* v___x_1261_; 
lean_dec(v_offset_1253_);
v___x_1261_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1258_, v_e_1252_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1260_);
return v___x_1261_;
}
case 2:
{
lean_object* v___x_1262_; 
lean_dec(v_offset_1253_);
v___x_1262_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1258_, v_e_1252_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1260_);
return v___x_1262_;
}
case 0:
{
lean_object* v___x_1263_; 
lean_dec(v_offset_1253_);
v___x_1263_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1258_, v_e_1252_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1260_);
return v___x_1263_;
}
case 1:
{
lean_object* v___x_1264_; 
lean_dec(v_offset_1253_);
v___x_1264_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1258_, v_e_1252_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1260_);
return v___x_1264_;
}
case 4:
{
lean_object* v___x_1265_; 
lean_dec(v_offset_1253_);
v___x_1265_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1258_, v_e_1252_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1260_);
return v___x_1265_;
}
case 3:
{
lean_object* v___x_1266_; 
lean_dec(v_offset_1253_);
v___x_1266_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1258_, v_e_1252_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1260_);
return v___x_1266_;
}
default: 
{
lean_object* v___x_1267_; 
v___x_1267_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_1250_, v_d_1251_, v_e_1252_, v_offset_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1260_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v_a_1269_; lean_object* v_fst_1270_; lean_object* v_snd_1271_; lean_object* v___x_1272_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
v_a_1269_ = lean_ctor_get(v___x_1267_, 1);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1267_, 2);
v_fst_1270_ = lean_ctor_get(v_a_1268_, 0);
lean_inc(v_fst_1270_);
v_snd_1271_ = lean_ctor_get(v_a_1268_, 1);
lean_inc(v_snd_1271_);
lean_dec(v_a_1268_);
v___x_1272_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1258_, v_fst_1270_, v_snd_1271_, v_a_1255_, v_a_1256_, v_a_1269_);
return v___x_1272_;
}
else
{
lean_dec_ref_known(v_key_1258_, 2);
return v___x_1267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0___boxed(lean_object* v_s_1297_, lean_object* v_d_1298_, lean_object* v_e_1299_, lean_object* v_offset_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
uint8_t v_a_boxed_1305_; lean_object* v_res_1306_; 
v_a_boxed_1305_ = lean_unbox(v_a_1302_);
v_res_1306_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1297_, v_d_1298_, v_e_1299_, v_offset_1300_, v_a_1301_, v_a_boxed_1305_, v_a_1303_, v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_d_1298_);
lean_dec(v_s_1297_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0___boxed(lean_object* v_s_1307_, lean_object* v_d_1308_, lean_object* v_e_1309_, lean_object* v_offset_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
uint8_t v_a_boxed_1315_; lean_object* v_res_1316_; 
v_a_boxed_1315_ = lean_unbox(v_a_1312_);
v_res_1316_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_1307_, v_d_1308_, v_e_1309_, v_offset_1310_, v_a_1311_, v_a_boxed_1315_, v_a_1313_, v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_d_1308_);
lean_dec(v_s_1307_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27(lean_object* v_e_1317_, lean_object* v_s_1318_, lean_object* v_d_1319_, uint8_t v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = l_Lean_Expr_looseBVarRange(v_e_1317_);
v___x_1324_ = lean_nat_dec_le(v___x_1323_, v_s_1318_);
lean_dec(v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v_a_1327_; 
v___x_1325_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_e_1317_) == 0)
{
lean_object* v_deBruijnIndex_1355_; uint8_t v___x_1356_; 
v_deBruijnIndex_1355_ = lean_ctor_get(v_e_1317_, 0);
v___x_1356_ = lean_nat_dec_le(v_s_1318_, v_deBruijnIndex_1355_);
if (v___x_1356_ == 0)
{
v_a_1327_ = v_a_1322_;
goto v___jp_1326_;
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_inc(v_deBruijnIndex_1355_);
lean_dec_ref_known(v_e_1317_, 1);
v___x_1357_ = lean_nat_add(v_deBruijnIndex_1355_, v_d_1319_);
lean_dec(v_deBruijnIndex_1355_);
v___x_1358_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_1357_, v_a_1322_);
return v___x_1358_;
}
}
else
{
v_a_1327_ = v_a_1322_;
goto v___jp_1326_;
}
v___jp_1326_:
{
switch(lean_obj_tag(v_e_1317_))
{
case 9:
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v_e_1317_);
lean_ctor_set(v___x_1328_, 1, v_a_1327_);
return v___x_1328_;
}
case 2:
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v_e_1317_);
lean_ctor_set(v___x_1329_, 1, v_a_1327_);
return v___x_1329_;
}
case 0:
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1330_, 0, v_e_1317_);
lean_ctor_set(v___x_1330_, 1, v_a_1327_);
return v___x_1330_;
}
case 1:
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_e_1317_);
lean_ctor_set(v___x_1331_, 1, v_a_1327_);
return v___x_1331_;
}
case 4:
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v_e_1317_);
lean_ctor_set(v___x_1332_, 1, v_a_1327_);
return v___x_1332_;
}
case 3:
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v_e_1317_);
lean_ctor_set(v___x_1333_, 1, v_a_1327_);
return v___x_1333_;
}
default: 
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__2, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__2_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__2);
v___x_1335_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_1318_, v_d_1319_, v_e_1317_, v___x_1325_, v___x_1334_, v_a_1320_, v_a_1321_, v_a_1327_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1345_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_a_1337_ = lean_ctor_get(v___x_1335_, 1);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1339_ = v___x_1335_;
v_isShared_1340_ = v_isSharedCheck_1345_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1345_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v_fst_1341_; lean_object* v___x_1343_; 
v_fst_1341_ = lean_ctor_get(v_a_1336_, 0);
lean_inc(v_fst_1341_);
lean_dec(v_a_1336_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v_fst_1341_);
v___x_1343_ = v___x_1339_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_fst_1341_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_a_1337_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
v_a_1346_ = lean_ctor_get(v___x_1335_, 0);
v_a_1347_ = lean_ctor_get(v___x_1335_, 1);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1335_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_inc(v_a_1346_);
lean_dec(v___x_1335_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1346_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v_e_1317_);
lean_ctor_set(v___x_1359_, 1, v_a_1322_);
return v___x_1359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27___boxed(lean_object* v_e_1360_, lean_object* v_s_1361_, lean_object* v_d_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
uint8_t v_a_boxed_1366_; lean_object* v_res_1367_; 
v_a_boxed_1366_ = lean_unbox(v_a_1363_);
v_res_1367_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_e_1360_, v_s_1361_, v_d_1362_, v_a_boxed_1366_, v_a_1364_, v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_d_1362_);
lean_dec(v_s_1361_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS(lean_object* v_e_1368_, lean_object* v_s_1369_, lean_object* v_d_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v_debug_1380_; lean_object* v_env_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1378_ = lean_st_ref_get(v_a_1372_);
v___x_1379_ = lean_st_ref_get(v_a_1376_);
v_debug_1380_ = lean_ctor_get_uint8(v___x_1378_, sizeof(void*)*11);
lean_dec(v___x_1378_);
v_env_1381_ = lean_ctor_get(v___x_1379_, 0);
lean_inc_ref(v_env_1381_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(v_debug_1380_);
v___x_1383_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_liftLooseBVarsS_x27___boxed), 6, 4);
lean_closure_set(v___x_1383_, 0, v_e_1368_);
lean_closure_set(v___x_1383_, 1, v_s_1369_);
lean_closure_set(v___x_1383_, 2, v_d_1370_);
lean_closure_set(v___x_1383_, 3, v___x_1382_);
v___x_1384_ = 0;
v___x_1385_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1385_, 0, v_env_1381_);
lean_ctor_set_uint8(v___x_1385_, sizeof(void*)*1, v___x_1384_);
lean_ctor_set_uint8(v___x_1385_, sizeof(void*)*1 + 1, v___x_1384_);
v___x_1386_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_1383_, v___x_1385_, v_a_1372_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1397_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1397_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1397_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
if (lean_obj_tag(v_a_1387_) == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec_ref_known(v_a_1387_, 1);
lean_del_object(v___x_1389_);
v___x_1391_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2, &l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS___closed__2);
v___x_1392_ = l_panic___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(v___x_1391_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
return v___x_1392_;
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; 
v_a_1393_ = lean_ctor_get(v_a_1387_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v_a_1387_, 1);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v_a_1393_);
v___x_1395_ = v___x_1389_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
v_a_1398_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1386_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1386_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___boxed(lean_object* v_e_1406_, lean_object* v_s_1407_, lean_object* v_d_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_Meta_Sym_liftLooseBVarsS(v_e_1406_, v_s_1407_, v_d_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
return v_res_1416_;
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
