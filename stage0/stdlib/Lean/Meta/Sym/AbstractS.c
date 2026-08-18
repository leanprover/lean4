// Lean compiler output
// Module: Lean.Meta.Sym.AbstractS
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.Sym.ReplaceS import Init.Omega
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
lean_object* l_Lean_LocalDecl_index(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_noption_get(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3;
static const lean_closure_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_map, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_pure, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_seqRight, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_bind, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.Sym.ReplaceS.0.Lean.Meta.Sym.visit"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.ReplaceS"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_abstractFVarsRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Sym.AlphaShareBuilder"};
static const lean_object* l_Lean_Meta_Sym_abstractFVarsRange___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_abstractFVarsRange___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_abstractFVarsRange___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Sym.Internal.liftBuilderM"};
static const lean_object* l_Lean_Meta_Sym_abstractFVarsRange___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_abstractFVarsRange___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_abstractFVarsRange___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_abstractFVarsRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_4_ = ((lean_object*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2));
v___x_5_ = lean_unsigned_to_nat(14u);
v___x_6_ = lean_unsigned_to_nat(22u);
v___x_7_ = ((lean_object*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1));
v___x_8_ = ((lean_object*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0));
v___x_9_ = l_mkPanicMessageWithDecl(v___x_8_, v___x_7_, v___x_6_, v___x_5_, v___x_4_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(lean_object* v_toDeBruijn_x3f_12_, lean_object* v___x_13_, lean_object* v_maxFVar_14_, lean_object* v_minIndex_15_, lean_object* v_lctx_16_, lean_object* v___x_17_, lean_object* v_e_18_, lean_object* v_offset_19_, uint8_t v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___y_24_; lean_object* v___y_32_; 
switch(lean_obj_tag(v_e_18_))
{
case 1:
{
lean_object* v_fvarId_37_; lean_object* v___x_38_; 
lean_dec_ref(v_lctx_16_);
v_fvarId_37_ = lean_ctor_get(v_e_18_, 0);
lean_inc(v_fvarId_37_);
v___x_38_ = lean_apply_1(v_toDeBruijn_x3f_12_, v_fvarId_37_);
if (lean_obj_tag(v___x_38_) == 1)
{
lean_object* v_val_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_68_; 
lean_dec_ref_known(v_e_18_, 1);
v_val_39_ = lean_ctor_get(v___x_38_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_68_ == 0)
{
v___x_41_ = v___x_38_;
v_isShared_42_ = v_isSharedCheck_68_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_val_39_);
lean_dec(v___x_38_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_68_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_43_; lean_object* v___x_2595__overap_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_43_ = lean_nat_add(v_offset_19_, v_val_39_);
lean_dec(v_val_39_);
v___x_2595__overap_44_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v___x_13_, v___x_43_);
v___x_45_ = lean_box(v___y_20_);
lean_inc_ref(v___y_21_);
v___x_46_ = lean_apply_3(v___x_2595__overap_44_, v___x_45_, v___y_21_, v___y_22_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_58_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
v_a_48_ = lean_ctor_get(v___x_46_, 1);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_58_ == 0)
{
v___x_50_ = v___x_46_;
v_isShared_51_ = v_isSharedCheck_58_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_inc(v_a_47_);
lean_dec(v___x_46_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_58_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_53_; 
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 0, v_a_47_);
v___x_53_ = v___x_41_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_a_47_);
v___x_53_ = v_reuseFailAlloc_57_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
lean_object* v___x_55_; 
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 0, v___x_53_);
v___x_55_ = v___x_50_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_53_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v_a_48_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
}
else
{
lean_object* v_a_59_; lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
lean_del_object(v___x_41_);
v_a_59_ = lean_ctor_get(v___x_46_, 0);
v_a_60_ = lean_ctor_get(v___x_46_, 1);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v___x_46_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_inc(v_a_59_);
lean_dec(v___x_46_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_a_59_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v_a_60_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v___x_38_);
lean_dec_ref(v___x_13_);
v___x_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_69_, 0, v_e_18_);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___y_22_);
return v___x_70_;
}
}
case 9:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___x_13_);
lean_dec_ref(v_toDeBruijn_x3f_12_);
v___x_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_71_, 0, v_e_18_);
v___x_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___y_22_);
return v___x_72_;
}
case 2:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___x_13_);
lean_dec_ref(v_toDeBruijn_x3f_12_);
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v_e_18_);
v___x_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___y_22_);
return v___x_74_;
}
case 0:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___x_13_);
lean_dec_ref(v_toDeBruijn_x3f_12_);
v___x_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_75_, 0, v_e_18_);
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___y_22_);
return v___x_76_;
}
case 4:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___x_13_);
lean_dec_ref(v_toDeBruijn_x3f_12_);
v___x_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_77_, 0, v_e_18_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___y_22_);
return v___x_78_;
}
case 3:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___x_13_);
lean_dec_ref(v_toDeBruijn_x3f_12_);
v___x_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_79_, 0, v_e_18_);
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___y_22_);
return v___x_80_;
}
default: 
{
uint8_t v___x_81_; 
lean_dec_ref(v___x_13_);
lean_dec_ref(v_toDeBruijn_x3f_12_);
v___x_81_ = l_Lean_Expr_hasFVar(v_e_18_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec_ref(v_lctx_16_);
v___x_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_82_, 0, v_e_18_);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___y_22_);
return v___x_83_;
}
else
{
lean_object* v___f_84_; lean_object* v___f_85_; lean_object* v___x_86_; 
v___f_84_ = ((lean_object*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4));
v___f_85_ = ((lean_object*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5));
lean_inc_ref(v_e_18_);
v___x_86_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_84_, v___f_85_, v_maxFVar_14_, v_e_18_);
if (lean_obj_tag(v___x_86_) == 1)
{
lean_object* v_val_87_; 
v_val_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_val_87_);
lean_dec_ref_known(v___x_86_, 1);
if (lean_obj_tag(v_val_87_) == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_box(0);
v___x_89_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_90_ = l_panic___redArg(v___x_88_, v___x_89_);
v___y_32_ = v___x_90_;
goto v___jp_31_;
}
else
{
lean_object* v_val_91_; 
v_val_91_ = lean_ctor_get(v_val_87_, 0);
lean_inc(v_val_91_);
lean_dec_ref_known(v_val_87_, 1);
v___y_32_ = v_val_91_;
goto v___jp_31_;
}
}
else
{
lean_object* v___x_92_; lean_object* v___x_93_; 
lean_dec(v___x_86_);
lean_dec_ref(v_e_18_);
lean_dec_ref(v_lctx_16_);
v___x_92_ = lean_box(0);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___y_22_);
return v___x_93_;
}
}
}
}
v___jp_23_:
{
lean_object* v_maxIndex_25_; uint8_t v___x_26_; 
v_maxIndex_25_ = l_Lean_LocalDecl_index(v___y_24_);
lean_dec_ref(v___y_24_);
v___x_26_ = lean_nat_dec_lt(v_maxIndex_25_, v_minIndex_15_);
lean_dec(v_maxIndex_25_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; 
lean_dec_ref(v_e_18_);
v___x_27_ = lean_box(0);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
lean_ctor_set(v___x_28_, 1, v___y_22_);
return v___x_28_;
}
else
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_29_, 0, v_e_18_);
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v___y_22_);
return v___x_30_;
}
}
v___jp_31_:
{
lean_object* v___x_33_; 
v___x_33_ = lean_local_ctx_find(v_lctx_16_, v___y_32_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_35_ = l_panic___redArg(v___x_17_, v___x_34_);
v___y_24_ = v___x_35_;
goto v___jp_23_;
}
else
{
lean_object* v_val_36_; 
v_val_36_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_val_36_);
lean_dec_ref_known(v___x_33_, 1);
v___y_24_ = v_val_36_;
goto v___jp_23_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed(lean_object* v_toDeBruijn_x3f_94_, lean_object* v___x_95_, lean_object* v_maxFVar_96_, lean_object* v_minIndex_97_, lean_object* v_lctx_98_, lean_object* v___x_99_, lean_object* v_e_100_, lean_object* v_offset_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
uint8_t v___y_2690__boxed_105_; lean_object* v_res_106_; 
v___y_2690__boxed_105_ = lean_unbox(v___y_102_);
v_res_106_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(v_toDeBruijn_x3f_94_, v___x_95_, v_maxFVar_96_, v_minIndex_97_, v_lctx_98_, v___x_99_, v_e_100_, v_offset_101_, v___y_2690__boxed_105_, v___y_103_, v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v_offset_101_);
lean_dec_ref(v___x_99_);
lean_dec(v_minIndex_97_);
lean_dec_ref(v_maxFVar_96_);
return v_res_106_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0(void){
_start:
{
lean_object* v_cellCount_107_; lean_object* v___x_108_; 
v_cellCount_107_ = lean_unsigned_to_nat(16u);
v___x_108_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_107_);
return v___x_108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1(void){
_start:
{
lean_object* v_cellCount_109_; lean_object* v___x_110_; 
v_cellCount_109_ = lean_unsigned_to_nat(16u);
v___x_110_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_109_);
return v___x_110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_111_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1);
v___x_112_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0);
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_111_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(lean_object* v_e_115_, lean_object* v_lctx_116_, lean_object* v_maxFVar_117_, lean_object* v_minFVarId_118_, lean_object* v_toDeBruijn_x3f_119_, uint8_t v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___y_126_; lean_object* v___x_227_; 
v___x_123_ = l_Lean_instInhabitedLocalDecl_default;
v___x_124_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
lean_inc_ref(v_lctx_116_);
v___x_227_ = lean_local_ctx_find(v_lctx_116_, v_minFVarId_118_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_229_ = l_panic___redArg(v___x_123_, v___x_228_);
v___y_126_ = v___x_229_;
goto v___jp_125_;
}
else
{
lean_object* v_val_230_; 
v_val_230_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_val_230_);
lean_dec_ref_known(v___x_227_, 1);
v___y_126_ = v_val_230_;
goto v___jp_125_;
}
v___jp_125_:
{
lean_object* v_minIndex_127_; lean_object* v___f_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_minIndex_127_ = l_Lean_LocalDecl_index(v___y_126_);
lean_dec_ref(v___y_126_);
lean_inc_ref(v_lctx_116_);
lean_inc(v_minIndex_127_);
lean_inc_ref(v_maxFVar_117_);
lean_inc_ref(v_toDeBruijn_x3f_119_);
v___f_128_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed), 11, 6);
lean_closure_set(v___f_128_, 0, v_toDeBruijn_x3f_119_);
lean_closure_set(v___f_128_, 1, v___x_124_);
lean_closure_set(v___f_128_, 2, v_maxFVar_117_);
lean_closure_set(v___f_128_, 3, v_minIndex_127_);
lean_closure_set(v___f_128_, 4, v_lctx_116_);
lean_closure_set(v___f_128_, 5, v___x_123_);
v___x_129_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_e_115_);
v___x_130_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(v_toDeBruijn_x3f_119_, v___x_124_, v_maxFVar_117_, v_minIndex_127_, v_lctx_116_, v___x_123_, v_e_115_, v___x_129_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_minIndex_127_);
lean_dec_ref(v_maxFVar_117_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
if (lean_obj_tag(v_a_131_) == 1)
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_140_; 
lean_dec_ref(v___f_128_);
lean_dec_ref(v_e_115_);
v_a_132_ = lean_ctor_get(v___x_130_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; 
v_unused_141_ = lean_ctor_get(v___x_130_, 0);
lean_dec(v_unused_141_);
v___x_134_ = v___x_130_;
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_130_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v_val_136_; lean_object* v___x_138_; 
v_val_136_ = lean_ctor_get(v_a_131_, 0);
lean_inc(v_val_136_);
lean_dec_ref_known(v_a_131_, 1);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v_val_136_);
v___x_138_ = v___x_134_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_val_136_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_a_132_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
else
{
lean_dec(v_a_131_);
switch(lean_obj_tag(v_e_115_))
{
case 9:
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
lean_dec_ref(v___f_128_);
v_a_142_ = lean_ctor_get(v___x_130_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_149_ == 0)
{
lean_object* v_unused_150_; 
v_unused_150_ = lean_ctor_get(v___x_130_, 0);
lean_dec(v_unused_150_);
v___x_144_ = v___x_130_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_130_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v_e_115_);
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_e_115_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
case 2:
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_dec_ref(v___f_128_);
v_a_151_ = lean_ctor_get(v___x_130_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; 
v_unused_159_ = lean_ctor_get(v___x_130_, 0);
lean_dec(v_unused_159_);
v___x_153_ = v___x_130_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_130_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v_e_115_);
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_e_115_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
case 0:
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
lean_dec_ref(v___f_128_);
v_a_160_ = lean_ctor_get(v___x_130_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_167_ == 0)
{
lean_object* v_unused_168_; 
v_unused_168_ = lean_ctor_get(v___x_130_, 0);
lean_dec(v_unused_168_);
v___x_162_ = v___x_130_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_130_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v_e_115_);
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_e_115_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
case 1:
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
lean_dec_ref(v___f_128_);
v_a_169_ = lean_ctor_get(v___x_130_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_176_ == 0)
{
lean_object* v_unused_177_; 
v_unused_177_ = lean_ctor_get(v___x_130_, 0);
lean_dec(v_unused_177_);
v___x_171_ = v___x_130_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_130_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v_e_115_);
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_e_115_);
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
case 4:
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_dec_ref(v___f_128_);
v_a_178_ = lean_ctor_get(v___x_130_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; 
v_unused_186_ = lean_ctor_get(v___x_130_, 0);
lean_dec(v_unused_186_);
v___x_180_ = v___x_130_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_130_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v_e_115_);
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_e_115_);
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
case 3:
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
lean_dec_ref(v___f_128_);
v_a_187_ = lean_ctor_get(v___x_130_, 1);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_194_ == 0)
{
lean_object* v_unused_195_; 
v_unused_195_ = lean_ctor_get(v___x_130_, 0);
lean_dec(v_unused_195_);
v___x_189_ = v___x_130_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_130_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v_e_115_);
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_e_115_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
default: 
{
lean_object* v_a_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_a_196_ = lean_ctor_get(v___x_130_, 1);
lean_inc(v_a_196_);
lean_dec_ref_known(v___x_130_, 2);
v___x_197_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2);
v___x_198_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_115_, v___x_129_, v___f_128_, v___x_197_, v_a_120_, v_a_121_, v_a_196_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_208_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_a_200_ = lean_ctor_get(v___x_198_, 1);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_208_ == 0)
{
v___x_202_ = v___x_198_;
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v_fst_204_; lean_object* v___x_206_; 
v_fst_204_ = lean_ctor_get(v_a_199_, 0);
lean_inc(v_fst_204_);
lean_dec(v_a_199_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v_fst_204_);
v___x_206_ = v___x_202_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_fst_204_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_a_200_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
else
{
lean_object* v_a_209_; lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
v_a_209_ = lean_ctor_get(v___x_198_, 0);
v_a_210_ = lean_ctor_get(v___x_198_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_198_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_inc(v_a_209_);
lean_dec(v___x_198_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_209_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_218_; lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
lean_dec_ref(v___f_128_);
lean_dec_ref(v_e_115_);
v_a_218_ = lean_ctor_get(v___x_130_, 0);
v_a_219_ = lean_ctor_get(v___x_130_, 1);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_130_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_inc(v_a_218_);
lean_dec(v___x_130_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_218_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_a_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___boxed(lean_object* v_e_231_, lean_object* v_lctx_232_, lean_object* v_maxFVar_233_, lean_object* v_minFVarId_234_, lean_object* v_toDeBruijn_x3f_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
uint8_t v_a_boxed_239_; lean_object* v_res_240_; 
v_a_boxed_239_ = lean_unbox(v_a_236_);
v_res_240_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(v_e_231_, v_lctx_232_, v_maxFVar_233_, v_minFVarId_234_, v_toDeBruijn_x3f_235_, v_a_boxed_239_, v_a_237_, v_a_238_);
lean_dec_ref(v_a_237_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(lean_object* v_start_241_, lean_object* v_xs_242_, lean_object* v_fvarId_243_, lean_object* v_bidx_244_, lean_object* v_i_245_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_246_ = lean_array_fget_borrowed(v_xs_242_, v_i_245_);
v___x_247_ = l_Lean_Expr_fvarId_x21(v___x_246_);
v___x_248_ = l_Lean_instBEqFVarId_beq(v___x_247_, v_fvarId_243_);
lean_dec(v___x_247_);
if (v___x_248_ == 0)
{
uint8_t v___x_249_; 
v___x_249_ = lean_nat_dec_lt(v_start_241_, v_i_245_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec(v_i_245_);
lean_dec(v_bidx_244_);
v___x_250_ = lean_box(0);
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_unsigned_to_nat(1u);
v___x_252_ = lean_nat_add(v_bidx_244_, v___x_251_);
lean_dec(v_bidx_244_);
v___x_253_ = lean_nat_sub(v_i_245_, v___x_251_);
lean_dec(v_i_245_);
v_bidx_244_ = v___x_252_;
v_i_245_ = v___x_253_;
goto _start;
}
}
else
{
lean_object* v___x_255_; 
lean_dec(v_i_245_);
v___x_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_255_, 0, v_bidx_244_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg___boxed(lean_object* v_start_256_, lean_object* v_xs_257_, lean_object* v_fvarId_258_, lean_object* v_bidx_259_, lean_object* v_i_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_256_, v_xs_257_, v_fvarId_258_, v_bidx_259_, v_i_260_);
lean_dec(v_fvarId_258_);
lean_dec_ref(v_xs_257_);
lean_dec(v_start_256_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(lean_object* v_start_262_, lean_object* v_xs_263_, lean_object* v_fvarId_264_, lean_object* v_bidx_265_, lean_object* v_i_266_, lean_object* v_h_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_262_, v_xs_263_, v_fvarId_264_, v_bidx_265_, v_i_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___boxed(lean_object* v_start_269_, lean_object* v_xs_270_, lean_object* v_fvarId_271_, lean_object* v_bidx_272_, lean_object* v_i_273_, lean_object* v_h_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(v_start_269_, v_xs_270_, v_fvarId_271_, v_bidx_272_, v_i_273_, v_h_274_);
lean_dec(v_fvarId_271_);
lean_dec_ref(v_xs_270_);
lean_dec(v_start_269_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(lean_object* v_msg_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = l_Lean_instInhabitedLocalDecl_default;
v___x_278_ = lean_panic_fn_borrowed(v___x_277_, v_msg_276_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(lean_object* v_idx_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = l_Lean_Expr_bvar___override(v_idx_279_);
v___x_282_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_281_, v___y_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(lean_object* v_idx_283_, uint8_t v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v_idx_283_, v___y_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___boxed(lean_object* v_idx_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
uint8_t v___y_25960__boxed_292_; lean_object* v_res_293_; 
v___y_25960__boxed_292_ = lean_unbox(v___y_289_);
v_res_293_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v_idx_288_, v___y_25960__boxed_292_, v___y_290_, v___y_291_);
lean_dec_ref(v___y_290_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(lean_object* v_msg_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_box(0);
v___x_296_ = lean_panic_fn_borrowed(v___x_295_, v_msg_294_);
return v___x_296_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0(void){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(lean_object* v_msg_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_2645__overap_307_; lean_object* v___x_308_; 
v___x_306_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0, &l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0);
v___x_2645__overap_307_ = lean_panic_fn_borrowed(v___x_306_, v_msg_298_);
lean_inc(v___y_304_);
lean_inc_ref(v___y_303_);
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
lean_inc(v___y_300_);
lean_inc_ref(v___y_299_);
v___x_308_ = lean_apply_7(v___x_2645__overap_307_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, lean_box(0));
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___boxed(lean_object* v_msg_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v_msg_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(lean_object* v_msg_325_, lean_object* v___y_326_, uint8_t v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___f_330_; lean_object* v___f_331_; lean_object* v___f_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___f_342_; lean_object* v___f_343_; lean_object* v___f_344_; lean_object* v___f_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_25269__overap_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___f_330_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__0));
v___f_331_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__1));
v___f_332_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__2));
v___x_333_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__3));
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___f_330_);
v___x_335_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__4));
v___x_336_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__5));
v___x_337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_337_, 0, v___x_334_);
lean_ctor_set(v___x_337_, 1, v___x_335_);
lean_ctor_set(v___x_337_, 2, v___f_331_);
lean_ctor_set(v___x_337_, 3, v___f_332_);
lean_ctor_set(v___x_337_, 4, v___x_336_);
v___x_338_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__6));
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = l_ReaderT_instMonad___redArg(v___x_339_);
v___x_341_ = l_ReaderT_instMonad___redArg(v___x_340_);
lean_inc_ref_n(v___x_341_, 6);
v___f_342_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_342_, 0, v___x_341_);
v___f_343_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_343_, 0, v___x_341_);
v___f_344_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_344_, 0, v___x_341_);
v___f_345_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_345_, 0, v___x_341_);
v___x_346_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_346_, 0, lean_box(0));
lean_closure_set(v___x_346_, 1, lean_box(0));
lean_closure_set(v___x_346_, 2, v___x_341_);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___f_342_);
v___x_348_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_348_, 0, lean_box(0));
lean_closure_set(v___x_348_, 1, lean_box(0));
lean_closure_set(v___x_348_, 2, v___x_341_);
v___x_349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_349_, 0, v___x_347_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
lean_ctor_set(v___x_349_, 2, v___f_343_);
lean_ctor_set(v___x_349_, 3, v___f_344_);
lean_ctor_set(v___x_349_, 4, v___f_345_);
v___x_350_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_350_, 0, lean_box(0));
lean_closure_set(v___x_350_, 1, lean_box(0));
lean_closure_set(v___x_350_, 2, v___x_341_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_349_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_352_ = l_Lean_instInhabitedExpr;
v___x_353_ = l_instInhabitedOfMonad___redArg(v___x_351_, v___x_352_);
v___x_25269__overap_354_ = lean_panic_fn_borrowed(v___x_353_, v_msg_325_);
lean_dec(v___x_353_);
v___x_355_ = lean_box(v___y_327_);
lean_inc_ref(v___y_328_);
v___x_356_ = lean_apply_4(v___x_25269__overap_354_, v___y_326_, v___x_355_, v___y_328_, v___y_329_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___boxed(lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
uint8_t v___y_26018__boxed_362_; lean_object* v_res_363_; 
v___y_26018__boxed_362_ = lean_unbox(v___y_359_);
v_res_363_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(v_msg_357_, v___y_358_, v___y_26018__boxed_362_, v___y_360_, v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(lean_object* v_d_364_, lean_object* v_e_365_, lean_object* v___y_366_, uint8_t v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___y_371_; lean_object* v___y_372_; 
if (v___y_367_ == 0)
{
v___y_371_ = v___y_366_;
v___y_372_ = v___y_369_;
goto v___jp_370_;
}
else
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_365_, v___y_367_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; 
v_a_395_ = lean_ctor_get(v___x_394_, 1);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 2);
v___y_371_ = v___y_366_;
v___y_372_ = v_a_395_;
goto v___jp_370_;
}
else
{
lean_object* v_a_396_; lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec_ref(v___y_366_);
lean_dec_ref(v_e_365_);
lean_dec(v_d_364_);
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
v___jp_370_:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = l_Lean_Expr_mdata___override(v_d_364_, v_e_365_);
v___x_374_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_373_, v___y_372_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_384_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_a_376_ = lean_ctor_get(v___x_374_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_384_ == 0)
{
v___x_378_ = v___x_374_;
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v_a_375_);
lean_ctor_set(v___x_380_, 1, v___y_371_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_380_);
v___x_382_ = v___x_378_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_a_376_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec_ref(v___y_371_);
v_a_385_ = lean_ctor_get(v___x_374_, 0);
v_a_386_ = lean_ctor_get(v___x_374_, 1);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_374_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_inc(v_a_385_);
lean_dec(v___x_374_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_385_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10___boxed(lean_object* v_d_405_, lean_object* v_e_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
uint8_t v___y_26089__boxed_411_; lean_object* v_res_412_; 
v___y_26089__boxed_411_ = lean_unbox(v___y_408_);
v_res_412_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(v_d_405_, v_e_406_, v___y_407_, v___y_26089__boxed_411_, v___y_409_, v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(lean_object* v_structName_413_, lean_object* v_idx_414_, lean_object* v_struct_415_, lean_object* v___y_416_, uint8_t v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___y_421_; lean_object* v___y_422_; 
if (v___y_417_ == 0)
{
v___y_421_ = v___y_416_;
v___y_422_ = v___y_419_;
goto v___jp_420_;
}
else
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_415_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; 
v_a_445_ = lean_ctor_get(v___x_444_, 1);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 2);
v___y_421_ = v___y_416_;
v___y_422_ = v_a_445_;
goto v___jp_420_;
}
else
{
lean_object* v_a_446_; lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec_ref(v___y_416_);
lean_dec_ref(v_struct_415_);
lean_dec(v_idx_414_);
lean_dec(v_structName_413_);
v_a_446_ = lean_ctor_get(v___x_444_, 0);
v_a_447_ = lean_ctor_get(v___x_444_, 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_444_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_inc(v_a_446_);
lean_dec(v___x_444_);
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
v___jp_420_:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = l_Lean_Expr_proj___override(v_structName_413_, v_idx_414_, v_struct_415_);
v___x_424_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_423_, v___y_422_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_434_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_a_426_ = lean_ctor_get(v___x_424_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_434_ == 0)
{
v___x_428_ = v___x_424_;
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v_a_425_);
lean_ctor_set(v___x_430_, 1, v___y_421_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_a_426_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
else
{
lean_object* v_a_435_; lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec_ref(v___y_421_);
v_a_435_ = lean_ctor_get(v___x_424_, 0);
v_a_436_ = lean_ctor_get(v___x_424_, 1);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_424_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_inc(v_a_435_);
lean_dec(v___x_424_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11___boxed(lean_object* v_structName_455_, lean_object* v_idx_456_, lean_object* v_struct_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
uint8_t v___y_26172__boxed_462_; lean_object* v_res_463_; 
v___y_26172__boxed_462_ = lean_unbox(v___y_459_);
v_res_463_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(v_structName_455_, v_idx_456_, v_struct_457_, v___y_458_, v___y_26172__boxed_462_, v___y_460_, v___y_461_);
lean_dec_ref(v___y_460_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(lean_object* v_keys_464_, lean_object* v_vals_465_, lean_object* v_i_466_, lean_object* v_k_467_){
_start:
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_array_get_size(v_keys_464_);
v___x_469_ = lean_nat_dec_lt(v_i_466_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
lean_dec(v_i_466_);
v___x_470_ = lean_box(0);
return v___x_470_;
}
else
{
lean_object* v_k_x27_471_; size_t v___x_472_; size_t v___x_473_; uint8_t v___x_474_; 
v_k_x27_471_ = lean_array_fget_borrowed(v_keys_464_, v_i_466_);
v___x_472_ = lean_ptr_addr(v_k_467_);
v___x_473_ = lean_ptr_addr(v_k_x27_471_);
v___x_474_ = lean_usize_dec_eq(v___x_472_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_unsigned_to_nat(1u);
v___x_476_ = lean_nat_add(v_i_466_, v___x_475_);
lean_dec(v_i_466_);
v_i_466_ = v___x_476_;
goto _start;
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_array_fget_borrowed(v_vals_465_, v_i_466_);
lean_dec(v_i_466_);
lean_inc(v___x_478_);
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_keys_480_, lean_object* v_vals_481_, lean_object* v_i_482_, lean_object* v_k_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_keys_480_, v_vals_481_, v_i_482_, v_k_483_);
lean_dec_ref(v_k_483_);
lean_dec_ref(v_vals_481_);
lean_dec_ref(v_keys_480_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(lean_object* v_x_485_, size_t v_x_486_, lean_object* v_x_487_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
lean_object* v_es_488_; lean_object* v___x_489_; size_t v___x_490_; size_t v___x_491_; lean_object* v_j_492_; lean_object* v___x_493_; 
v_es_488_ = lean_ctor_get(v_x_485_, 0);
v___x_489_ = lean_box(2);
v___x_490_ = ((size_t)31ULL);
v___x_491_ = lean_usize_land(v_x_486_, v___x_490_);
v_j_492_ = lean_usize_to_nat(v___x_491_);
v___x_493_ = lean_array_get_borrowed(v___x_489_, v_es_488_, v_j_492_);
lean_dec(v_j_492_);
switch(lean_obj_tag(v___x_493_))
{
case 0:
{
lean_object* v_key_494_; lean_object* v_val_495_; size_t v___x_496_; size_t v___x_497_; uint8_t v___x_498_; 
v_key_494_ = lean_ctor_get(v___x_493_, 0);
v_val_495_ = lean_ctor_get(v___x_493_, 1);
v___x_496_ = lean_ptr_addr(v_x_487_);
v___x_497_ = lean_ptr_addr(v_key_494_);
v___x_498_ = lean_usize_dec_eq(v___x_496_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
v___x_499_ = lean_box(0);
return v___x_499_;
}
else
{
lean_object* v___x_500_; 
lean_inc(v_val_495_);
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v_val_495_);
return v___x_500_;
}
}
case 1:
{
lean_object* v_node_501_; size_t v___x_502_; size_t v___x_503_; 
v_node_501_ = lean_ctor_get(v___x_493_, 0);
v___x_502_ = ((size_t)5ULL);
v___x_503_ = lean_usize_shift_right(v_x_486_, v___x_502_);
v_x_485_ = v_node_501_;
v_x_486_ = v___x_503_;
goto _start;
}
default: 
{
lean_object* v___x_505_; 
v___x_505_ = lean_box(0);
return v___x_505_;
}
}
}
else
{
lean_object* v_ks_506_; lean_object* v_vs_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v_ks_506_ = lean_ctor_get(v_x_485_, 0);
v_vs_507_ = lean_ctor_get(v_x_485_, 1);
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_ks_506_, v_vs_507_, v___x_508_, v_x_487_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg___boxed(lean_object* v_x_510_, lean_object* v_x_511_, lean_object* v_x_512_){
_start:
{
size_t v_x_26277__boxed_513_; lean_object* v_res_514_; 
v_x_26277__boxed_513_ = lean_unbox_usize(v_x_511_);
lean_dec(v_x_511_);
v_res_514_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_510_, v_x_26277__boxed_513_, v_x_512_);
lean_dec_ref(v_x_512_);
lean_dec_ref(v_x_510_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
size_t v___x_517_; size_t v___x_518_; size_t v___x_519_; uint64_t v___x_520_; size_t v___x_521_; lean_object* v___x_522_; 
v___x_517_ = lean_ptr_addr(v_x_516_);
v___x_518_ = ((size_t)3ULL);
v___x_519_ = lean_usize_shift_right(v___x_517_, v___x_518_);
v___x_520_ = lean_usize_to_uint64(v___x_519_);
v___x_521_ = lean_uint64_to_usize(v___x_520_);
v___x_522_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_515_, v___x_521_, v_x_516_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg___boxed(lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_x_523_, v_x_524_);
lean_dec_ref(v_x_524_);
lean_dec_ref(v_x_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17_spec__18___redArg(lean_object* v_m_526_, lean_object* v_query_527_, lean_object* v_x_528_, lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
lean_object* v_zero_531_; uint8_t v_isZero_532_; 
v_zero_531_ = lean_unsigned_to_nat(0u);
v_isZero_532_ = lean_nat_dec_eq(v_x_529_, v_zero_531_);
if (v_isZero_532_ == 1)
{
lean_dec(v_x_530_);
lean_dec(v_x_529_);
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v___x_533_; 
v___x_533_ = lean_box(2);
return v___x_533_;
}
else
{
lean_object* v_val_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
v_val_534_ = lean_ctor_get(v_x_528_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v_x_528_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v_x_528_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_val_534_);
lean_dec(v_x_528_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_val_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
lean_object* v_keyArray_542_; lean_object* v_valueArray_543_; lean_object* v___x_544_; uint8_t v_isSome_545_; 
v_keyArray_542_ = lean_ctor_get(v_m_526_, 1);
v_valueArray_543_ = lean_ctor_get(v_m_526_, 2);
v___x_544_ = lean_array_fget_borrowed(v_keyArray_542_, v_x_530_);
v_isSome_545_ = lean_noption_is_some(v___x_544_);
if (v_isSome_545_ == 0)
{
lean_dec(v_x_529_);
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v___x_546_; 
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v_x_530_);
return v___x_546_;
}
else
{
lean_object* v_val_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v_x_530_);
v_val_547_ = lean_ctor_get(v_x_528_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v_x_528_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v_x_528_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_val_547_);
lean_dec(v_x_528_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_val_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
lean_object* v_one_555_; lean_object* v_n_556_; lean_object* v___y_558_; 
v_one_555_ = lean_unsigned_to_nat(1u);
v_n_556_ = lean_nat_sub(v_x_529_, v_one_555_);
lean_dec(v_x_529_);
if (v_isSome_545_ == 0)
{
goto v___jp_564_;
}
else
{
lean_object* v___x_566_; uint8_t v_isSome_567_; 
v___x_566_ = lean_array_fget_borrowed(v_valueArray_543_, v_x_530_);
v_isSome_567_ = lean_noption_is_some(v___x_566_);
if (v_isSome_567_ == 0)
{
goto v___jp_564_;
}
else
{
lean_object* v_val_568_; lean_object* v_fst_569_; lean_object* v_snd_570_; lean_object* v_fst_571_; lean_object* v_snd_572_; lean_object* v_val_573_; uint8_t v___y_575_; size_t v___x_582_; size_t v___x_583_; uint8_t v___x_584_; 
lean_inc(v___x_544_);
v_val_568_ = lean_noption_get(v___x_544_);
v_fst_569_ = lean_ctor_get(v_val_568_, 0);
lean_inc(v_fst_569_);
v_snd_570_ = lean_ctor_get(v_val_568_, 1);
lean_inc(v_snd_570_);
v_fst_571_ = lean_ctor_get(v_query_527_, 0);
v_snd_572_ = lean_ctor_get(v_query_527_, 1);
lean_inc(v___x_566_);
v_val_573_ = lean_noption_get(v___x_566_);
v___x_582_ = lean_ptr_addr(v_fst_569_);
lean_dec(v_fst_569_);
v___x_583_ = lean_ptr_addr(v_fst_571_);
v___x_584_ = lean_usize_dec_eq(v___x_582_, v___x_583_);
if (v___x_584_ == 0)
{
lean_dec(v_snd_570_);
v___y_575_ = v___x_584_;
goto v___jp_574_;
}
else
{
uint8_t v___x_585_; 
v___x_585_ = lean_nat_dec_eq(v_snd_570_, v_snd_572_);
lean_dec(v_snd_570_);
v___y_575_ = v___x_585_;
goto v___jp_574_;
}
v___jp_574_:
{
if (v___y_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
lean_dec(v_val_573_);
lean_dec(v_val_568_);
v___x_576_ = lean_array_get_size(v_keyArray_542_);
v___x_577_ = lean_nat_add(v_x_530_, v_one_555_);
lean_dec(v_x_530_);
v___x_578_ = lean_nat_dec_lt(v___x_577_, v___x_576_);
if (v___x_578_ == 0)
{
lean_dec(v___x_577_);
v_x_529_ = v_n_556_;
v_x_530_ = v_zero_531_;
goto _start;
}
else
{
v_x_529_ = v_n_556_;
v_x_530_ = v___x_577_;
goto _start;
}
}
else
{
lean_object* v___x_581_; 
lean_dec(v_n_556_);
lean_dec(v_x_528_);
v___x_581_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_581_, 0, v_x_530_);
lean_ctor_set(v___x_581_, 1, v_val_568_);
lean_ctor_set(v___x_581_, 2, v_val_573_);
return v___x_581_;
}
}
}
}
v___jp_557_:
{
lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_559_ = lean_array_get_size(v_keyArray_542_);
v___x_560_ = lean_nat_add(v_x_530_, v_one_555_);
lean_dec(v_x_530_);
v___x_561_ = lean_nat_dec_lt(v___x_560_, v___x_559_);
if (v___x_561_ == 0)
{
lean_dec(v___x_560_);
v_x_528_ = v___y_558_;
v_x_529_ = v_n_556_;
v_x_530_ = v_zero_531_;
goto _start;
}
else
{
v_x_528_ = v___y_558_;
v_x_529_ = v_n_556_;
v_x_530_ = v___x_560_;
goto _start;
}
}
v___jp_564_:
{
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v___x_565_; 
lean_inc(v_x_530_);
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v_x_530_);
v___y_558_ = v___x_565_;
goto v___jp_557_;
}
else
{
v___y_558_ = v_x_528_;
goto v___jp_557_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17_spec__18___redArg___boxed(lean_object* v_m_586_, lean_object* v_query_587_, lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v_x_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17_spec__18___redArg(v_m_586_, v_query_587_, v_x_588_, v_x_589_, v_x_590_);
lean_dec_ref(v_query_587_);
lean_dec_ref(v_m_586_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17___redArg(lean_object* v_m_592_, lean_object* v_query_593_){
_start:
{
lean_object* v_keyArray_594_; lean_object* v_fst_595_; lean_object* v_snd_596_; lean_object* v___x_597_; size_t v___x_598_; size_t v___x_599_; size_t v___x_600_; uint64_t v___x_601_; uint64_t v___x_602_; uint64_t v___x_603_; uint64_t v___x_604_; uint64_t v___x_605_; uint64_t v_fold_606_; uint64_t v___x_607_; uint64_t v___x_608_; uint64_t v___x_609_; size_t v___x_610_; size_t v___x_611_; size_t v___x_612_; size_t v___x_613_; size_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_keyArray_594_ = lean_ctor_get(v_m_592_, 1);
v_fst_595_ = lean_ctor_get(v_query_593_, 0);
v_snd_596_ = lean_ctor_get(v_query_593_, 1);
v___x_597_ = lean_array_get_size(v_keyArray_594_);
v___x_598_ = lean_ptr_addr(v_fst_595_);
v___x_599_ = ((size_t)3ULL);
v___x_600_ = lean_usize_shift_right(v___x_598_, v___x_599_);
v___x_601_ = lean_usize_to_uint64(v___x_600_);
v___x_602_ = lean_uint64_of_nat(v_snd_596_);
v___x_603_ = lean_uint64_mix_hash(v___x_601_, v___x_602_);
v___x_604_ = 32ULL;
v___x_605_ = lean_uint64_shift_right(v___x_603_, v___x_604_);
v_fold_606_ = lean_uint64_xor(v___x_603_, v___x_605_);
v___x_607_ = 16ULL;
v___x_608_ = lean_uint64_shift_right(v_fold_606_, v___x_607_);
v___x_609_ = lean_uint64_xor(v_fold_606_, v___x_608_);
v___x_610_ = lean_uint64_to_usize(v___x_609_);
v___x_611_ = lean_usize_of_nat(v___x_597_);
v___x_612_ = ((size_t)1ULL);
v___x_613_ = lean_usize_sub(v___x_611_, v___x_612_);
v___x_614_ = lean_usize_land(v___x_610_, v___x_613_);
v___x_615_ = lean_usize_to_nat(v___x_614_);
v___x_616_ = lean_box(0);
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17_spec__18___redArg(v_m_592_, v_query_593_, v___x_616_, v___x_597_, v___x_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17___redArg___boxed(lean_object* v_m_618_, lean_object* v_query_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17___redArg(v_m_618_, v_query_619_);
lean_dec_ref(v_query_619_);
lean_dec_ref(v_m_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(lean_object* v_m_621_, lean_object* v_query_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17___redArg(v_m_621_, v_query_622_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_index_624_; lean_object* v_key_625_; lean_object* v_value_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
v_index_624_ = lean_ctor_get(v___x_623_, 0);
v_key_625_ = lean_ctor_get(v___x_623_, 1);
v_value_626_ = lean_ctor_get(v___x_623_, 2);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_623_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_value_626_);
lean_inc(v_key_625_);
lean_inc(v_index_624_);
lean_dec(v___x_623_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_index_624_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_key_625_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_value_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
else
{
lean_object* v___x_634_; 
lean_dec(v___x_623_);
v___x_634_ = lean_box(1);
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg___boxed(lean_object* v_m_635_, lean_object* v_query_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_m_635_, v_query_636_);
lean_dec_ref(v_query_636_);
lean_dec_ref(v_m_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(lean_object* v_m_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_m_638_, v_a_639_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_value_641_; lean_object* v___x_642_; 
v_value_641_ = lean_ctor_get(v___x_640_, 2);
lean_inc(v_value_641_);
lean_dec_ref_known(v___x_640_, 3);
v___x_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_642_, 0, v_value_641_);
return v___x_642_;
}
else
{
lean_object* v___x_643_; 
v___x_643_ = lean_box(0);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_m_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_m_644_, v_a_645_);
lean_dec_ref(v_a_645_);
lean_dec_ref(v_m_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(lean_object* v_x_647_, uint8_t v_bi_648_, lean_object* v_t_649_, lean_object* v_b_650_, lean_object* v___y_651_, uint8_t v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___y_656_; lean_object* v___y_657_; 
if (v___y_652_ == 0)
{
v___y_656_ = v___y_651_;
v___y_657_ = v___y_654_;
goto v___jp_655_;
}
else
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_649_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_681_; 
v_a_680_ = lean_ctor_get(v___x_679_, 1);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 2);
v___x_681_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_650_, v___y_652_, v___y_653_, v_a_680_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; 
v_a_682_ = lean_ctor_get(v___x_681_, 1);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_681_, 2);
v___y_656_ = v___y_651_;
v___y_657_ = v_a_682_;
goto v___jp_655_;
}
else
{
lean_object* v_a_683_; lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec_ref(v___y_651_);
lean_dec_ref(v_b_650_);
lean_dec_ref(v_t_649_);
lean_dec(v_x_647_);
v_a_683_ = lean_ctor_get(v___x_681_, 0);
v_a_684_ = lean_ctor_get(v___x_681_, 1);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_681_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_inc(v_a_683_);
lean_dec(v___x_681_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_683_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
else
{
lean_object* v_a_692_; lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v___y_651_);
lean_dec_ref(v_b_650_);
lean_dec_ref(v_t_649_);
lean_dec(v_x_647_);
v_a_692_ = lean_ctor_get(v___x_679_, 0);
v_a_693_ = lean_ctor_get(v___x_679_, 1);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_679_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_inc(v_a_692_);
lean_dec(v___x_679_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_692_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
v___jp_655_:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = l_Lean_Expr_forallE___override(v_x_647_, v_t_649_, v_b_650_, v_bi_648_);
v___x_659_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_658_, v___y_657_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_669_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_a_661_ = lean_ctor_get(v___x_659_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_669_ == 0)
{
v___x_663_ = v___x_659_;
v_isShared_664_ = v_isSharedCheck_669_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_669_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v_a_660_);
lean_ctor_set(v___x_665_, 1, v___y_656_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_665_);
v___x_667_ = v___x_663_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_a_661_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
else
{
lean_object* v_a_670_; lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref(v___y_656_);
v_a_670_ = lean_ctor_get(v___x_659_, 0);
v_a_671_ = lean_ctor_get(v___x_659_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_659_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_inc(v_a_670_);
lean_dec(v___x_659_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_670_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8___boxed(lean_object* v_x_701_, lean_object* v_bi_702_, lean_object* v_t_703_, lean_object* v_b_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
uint8_t v_bi_boxed_709_; uint8_t v___y_26530__boxed_710_; lean_object* v_res_711_; 
v_bi_boxed_709_ = lean_unbox(v_bi_702_);
v___y_26530__boxed_710_ = lean_unbox(v___y_706_);
v_res_711_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_x_701_, v_bi_boxed_709_, v_t_703_, v_b_704_, v___y_705_, v___y_26530__boxed_710_, v___y_707_, v___y_708_);
lean_dec_ref(v___y_707_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(lean_object* v_x_712_, uint8_t v_bi_713_, lean_object* v_t_714_, lean_object* v_b_715_, lean_object* v___y_716_, uint8_t v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___y_721_; lean_object* v___y_722_; 
if (v___y_717_ == 0)
{
v___y_721_ = v___y_716_;
v___y_722_ = v___y_719_;
goto v___jp_720_;
}
else
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_714_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_746_; 
v_a_745_ = lean_ctor_get(v___x_744_, 1);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 2);
v___x_746_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_715_, v___y_717_, v___y_718_, v_a_745_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; 
v_a_747_ = lean_ctor_get(v___x_746_, 1);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 2);
v___y_721_ = v___y_716_;
v___y_722_ = v_a_747_;
goto v___jp_720_;
}
else
{
lean_object* v_a_748_; lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec_ref(v___y_716_);
lean_dec_ref(v_b_715_);
lean_dec_ref(v_t_714_);
lean_dec(v_x_712_);
v_a_748_ = lean_ctor_get(v___x_746_, 0);
v_a_749_ = lean_ctor_get(v___x_746_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_746_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_inc(v_a_748_);
lean_dec(v___x_746_);
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
else
{
lean_object* v_a_757_; lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v___y_716_);
lean_dec_ref(v_b_715_);
lean_dec_ref(v_t_714_);
lean_dec(v_x_712_);
v_a_757_ = lean_ctor_get(v___x_744_, 0);
v_a_758_ = lean_ctor_get(v___x_744_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_744_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_inc(v_a_757_);
lean_dec(v___x_744_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_757_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
v___jp_720_:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = l_Lean_Expr_lam___override(v_x_712_, v_t_714_, v_b_715_, v_bi_713_);
v___x_724_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_723_, v___y_722_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_734_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_a_726_ = lean_ctor_get(v___x_724_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_734_ == 0)
{
v___x_728_ = v___x_724_;
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v_a_725_);
lean_ctor_set(v___x_730_, 1, v___y_721_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_730_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_a_726_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
else
{
lean_object* v_a_735_; lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec_ref(v___y_721_);
v_a_735_ = lean_ctor_get(v___x_724_, 0);
v_a_736_ = lean_ctor_get(v___x_724_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_724_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_inc(v_a_735_);
lean_dec(v___x_724_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_735_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7___boxed(lean_object* v_x_766_, lean_object* v_bi_767_, lean_object* v_t_768_, lean_object* v_b_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
uint8_t v_bi_boxed_774_; uint8_t v___y_26636__boxed_775_; lean_object* v_res_776_; 
v_bi_boxed_774_ = lean_unbox(v_bi_767_);
v___y_26636__boxed_775_ = lean_unbox(v___y_771_);
v_res_776_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_x_766_, v_bi_boxed_774_, v_t_768_, v_b_769_, v___y_770_, v___y_26636__boxed_775_, v___y_772_, v___y_773_);
lean_dec_ref(v___y_772_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(lean_object* v_x_777_, lean_object* v_t_778_, lean_object* v_v_779_, lean_object* v_b_780_, uint8_t v_nondep_781_, lean_object* v___y_782_, uint8_t v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___y_787_; lean_object* v___y_788_; 
if (v___y_783_ == 0)
{
v___y_787_ = v___y_782_;
v___y_788_ = v___y_785_;
goto v___jp_786_;
}
else
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_778_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_812_; 
v_a_811_ = lean_ctor_get(v___x_810_, 1);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 2);
v___x_812_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_779_, v___y_783_, v___y_784_, v_a_811_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_814_; 
v_a_813_ = lean_ctor_get(v___x_812_, 1);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_812_, 2);
v___x_814_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_780_, v___y_783_, v___y_784_, v_a_813_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; 
v_a_815_ = lean_ctor_get(v___x_814_, 1);
lean_inc(v_a_815_);
lean_dec_ref_known(v___x_814_, 2);
v___y_787_ = v___y_782_;
v___y_788_ = v_a_815_;
goto v___jp_786_;
}
else
{
lean_object* v_a_816_; lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v___y_782_);
lean_dec_ref(v_b_780_);
lean_dec_ref(v_v_779_);
lean_dec_ref(v_t_778_);
lean_dec(v_x_777_);
v_a_816_ = lean_ctor_get(v___x_814_, 0);
v_a_817_ = lean_ctor_get(v___x_814_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_814_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_inc(v_a_816_);
lean_dec(v___x_814_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_816_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
else
{
lean_object* v_a_825_; lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec_ref(v___y_782_);
lean_dec_ref(v_b_780_);
lean_dec_ref(v_v_779_);
lean_dec_ref(v_t_778_);
lean_dec(v_x_777_);
v_a_825_ = lean_ctor_get(v___x_812_, 0);
v_a_826_ = lean_ctor_get(v___x_812_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_812_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_inc(v_a_825_);
lean_dec(v___x_812_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_825_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
else
{
lean_object* v_a_834_; lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec_ref(v___y_782_);
lean_dec_ref(v_b_780_);
lean_dec_ref(v_v_779_);
lean_dec_ref(v_t_778_);
lean_dec(v_x_777_);
v_a_834_ = lean_ctor_get(v___x_810_, 0);
v_a_835_ = lean_ctor_get(v___x_810_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_810_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_inc(v_a_834_);
lean_dec(v___x_810_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_834_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
v___jp_786_:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = l_Lean_Expr_letE___override(v_x_777_, v_t_778_, v_v_779_, v_b_780_, v_nondep_781_);
v___x_790_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_789_, v___y_788_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_800_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_a_792_ = lean_ctor_get(v___x_790_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_800_ == 0)
{
v___x_794_ = v___x_790_;
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v_a_791_);
lean_ctor_set(v___x_796_, 1, v___y_787_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_796_);
v___x_798_ = v___x_794_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_a_792_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
else
{
lean_object* v_a_801_; lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v___y_787_);
v_a_801_ = lean_ctor_get(v___x_790_, 0);
v_a_802_ = lean_ctor_get(v___x_790_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_790_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_inc(v_a_801_);
lean_dec(v___x_790_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_801_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9___boxed(lean_object* v_x_843_, lean_object* v_t_844_, lean_object* v_v_845_, lean_object* v_b_846_, lean_object* v_nondep_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
uint8_t v_nondep_boxed_852_; uint8_t v___y_26742__boxed_853_; lean_object* v_res_854_; 
v_nondep_boxed_852_ = lean_unbox(v_nondep_847_);
v___y_26742__boxed_853_ = lean_unbox(v___y_849_);
v_res_854_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_x_843_, v_t_844_, v_v_845_, v_b_846_, v_nondep_boxed_852_, v___y_848_, v___y_26742__boxed_853_, v___y_850_, v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(lean_object* v_f_855_, lean_object* v_a_856_, lean_object* v___y_857_, uint8_t v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v___y_862_; lean_object* v___y_863_; 
if (v___y_858_ == 0)
{
v___y_862_ = v___y_857_;
v___y_863_ = v___y_860_;
goto v___jp_861_;
}
else
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_855_, v___y_858_, v___y_859_, v___y_860_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 1);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 2);
v___x_887_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_856_, v___y_858_, v___y_859_, v_a_886_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; 
v_a_888_ = lean_ctor_get(v___x_887_, 1);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 2);
v___y_862_ = v___y_857_;
v___y_863_ = v_a_888_;
goto v___jp_861_;
}
else
{
lean_object* v_a_889_; lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref(v___y_857_);
lean_dec_ref(v_a_856_);
lean_dec_ref(v_f_855_);
v_a_889_ = lean_ctor_get(v___x_887_, 0);
v_a_890_ = lean_ctor_get(v___x_887_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_887_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_inc(v_a_889_);
lean_dec(v___x_887_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_889_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_object* v_a_898_; lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec_ref(v___y_857_);
lean_dec_ref(v_a_856_);
lean_dec_ref(v_f_855_);
v_a_898_ = lean_ctor_get(v___x_885_, 0);
v_a_899_ = lean_ctor_get(v___x_885_, 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_885_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_inc(v_a_898_);
lean_dec(v___x_885_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_898_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
v___jp_861_:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = l_Lean_Expr_app___override(v_f_855_, v_a_856_);
v___x_865_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_864_, v___y_863_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_875_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_a_867_ = lean_ctor_get(v___x_865_, 1);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_875_ == 0)
{
v___x_869_ = v___x_865_;
v_isShared_870_ = v_isSharedCheck_875_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_875_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v_a_866_);
lean_ctor_set(v___x_871_, 1, v___y_862_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_871_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_a_867_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
else
{
lean_object* v_a_876_; lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec_ref(v___y_862_);
v_a_876_ = lean_ctor_get(v___x_865_, 0);
v_a_877_ = lean_ctor_get(v___x_865_, 1);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_865_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_inc(v_a_876_);
lean_dec(v___x_865_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_876_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6___boxed(lean_object* v_f_907_, lean_object* v_a_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
uint8_t v___y_26871__boxed_913_; lean_object* v_res_914_; 
v___y_26871__boxed_913_ = lean_unbox(v___y_910_);
v_res_914_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_f_907_, v_a_908_, v___y_909_, v___y_26871__boxed_913_, v___y_911_, v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_914_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_918_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__2));
v___x_919_ = lean_unsigned_to_nat(67u);
v___x_920_ = lean_unsigned_to_nat(35u);
v___x_921_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__1));
v___x_922_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__0));
v___x_923_ = l_mkPanicMessageWithDecl(v___x_922_, v___x_921_, v___x_920_, v___x_919_, v___x_918_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(lean_object* v_minIndex_924_, lean_object* v___x_925_, lean_object* v___x_926_, lean_object* v_start_927_, lean_object* v_xs_928_, lean_object* v___x_929_, lean_object* v_e_930_, lean_object* v_offset_931_, lean_object* v_a_932_, uint8_t v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
switch(lean_obj_tag(v_e_930_))
{
case 5:
{
lean_object* v_fn_936_; lean_object* v_arg_937_; lean_object* v___x_938_; 
v_fn_936_ = lean_ctor_get(v_e_930_, 0);
v_arg_937_ = lean_ctor_get(v_e_930_, 1);
lean_inc(v_offset_931_);
lean_inc_ref(v_fn_936_);
lean_inc_ref(v___x_925_);
v___x_938_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_924_, v___x_925_, v___x_926_, v_start_927_, v_xs_928_, v___x_929_, v_fn_936_, v_offset_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v_a_940_; lean_object* v_fst_941_; lean_object* v_snd_942_; lean_object* v___x_943_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
v_a_940_ = lean_ctor_get(v___x_938_, 1);
lean_inc(v_a_940_);
lean_dec_ref_known(v___x_938_, 2);
v_fst_941_ = lean_ctor_get(v_a_939_, 0);
lean_inc(v_fst_941_);
v_snd_942_ = lean_ctor_get(v_a_939_, 1);
lean_inc(v_snd_942_);
lean_dec(v_a_939_);
lean_inc_ref(v_arg_937_);
v___x_943_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_924_, v___x_925_, v___x_926_, v_start_927_, v_xs_928_, v___x_929_, v_arg_937_, v_offset_931_, v_snd_942_, v_a_933_, v_a_934_, v_a_940_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_970_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_a_945_ = lean_ctor_get(v___x_943_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_970_ == 0)
{
v___x_947_ = v___x_943_;
v_isShared_948_ = v_isSharedCheck_970_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_970_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_fst_949_; lean_object* v_snd_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_969_; 
v_fst_949_ = lean_ctor_get(v_a_944_, 0);
v_snd_950_ = lean_ctor_get(v_a_944_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_a_944_);
if (v_isSharedCheck_969_ == 0)
{
v___x_952_ = v_a_944_;
v_isShared_953_ = v_isSharedCheck_969_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_snd_950_);
lean_inc(v_fst_949_);
lean_dec(v_a_944_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_969_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
uint8_t v___y_955_; size_t v___x_963_; size_t v___x_964_; uint8_t v___x_965_; 
v___x_963_ = lean_ptr_addr(v_fn_936_);
v___x_964_ = lean_ptr_addr(v_fst_941_);
v___x_965_ = lean_usize_dec_eq(v___x_963_, v___x_964_);
if (v___x_965_ == 0)
{
v___y_955_ = v___x_965_;
goto v___jp_954_;
}
else
{
size_t v___x_966_; size_t v___x_967_; uint8_t v___x_968_; 
v___x_966_ = lean_ptr_addr(v_arg_937_);
v___x_967_ = lean_ptr_addr(v_fst_949_);
v___x_968_ = lean_usize_dec_eq(v___x_966_, v___x_967_);
v___y_955_ = v___x_968_;
goto v___jp_954_;
}
v___jp_954_:
{
if (v___y_955_ == 0)
{
lean_object* v___x_956_; 
lean_del_object(v___x_952_);
lean_del_object(v___x_947_);
lean_dec_ref_known(v_e_930_, 2);
v___x_956_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_fst_941_, v_fst_949_, v_snd_950_, v_a_933_, v_a_934_, v_a_945_);
return v___x_956_;
}
else
{
lean_object* v___x_958_; 
lean_dec(v_fst_949_);
lean_dec(v_fst_941_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v_e_930_);
v___x_958_ = v___x_952_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_e_930_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_snd_950_);
v___x_958_ = v_reuseFailAlloc_962_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_960_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_958_);
v___x_960_ = v___x_947_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_a_945_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_941_);
lean_dec_ref_known(v_e_930_, 2);
return v___x_943_;
}
}
else
{
lean_dec_ref_known(v_e_930_, 2);
lean_dec(v_offset_931_);
lean_dec_ref(v___x_925_);
return v___x_938_;
}
}
case 6:
{
lean_object* v_binderName_971_; lean_object* v_binderType_972_; lean_object* v_body_973_; uint8_t v_binderInfo_974_; lean_object* v___x_975_; 
v_binderName_971_ = lean_ctor_get(v_e_930_, 0);
v_binderType_972_ = lean_ctor_get(v_e_930_, 1);
v_body_973_ = lean_ctor_get(v_e_930_, 2);
v_binderInfo_974_ = lean_ctor_get_uint8(v_e_930_, sizeof(void*)*3 + 8);
lean_inc(v_offset_931_);
lean_inc_ref(v_binderType_972_);
lean_inc_ref(v___x_925_);
v___x_975_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_924_, v___x_925_, v___x_926_, v_start_927_, v_xs_928_, v___x_929_, v_binderType_972_, v_offset_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v_a_977_; lean_object* v_fst_978_; lean_object* v_snd_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
v_a_977_ = lean_ctor_get(v___x_975_, 1);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_975_, 2);
v_fst_978_ = lean_ctor_get(v_a_976_, 0);
lean_inc(v_fst_978_);
v_snd_979_ = lean_ctor_get(v_a_976_, 1);
lean_inc(v_snd_979_);
lean_dec(v_a_976_);
v___x_980_ = lean_unsigned_to_nat(1u);
v___x_981_ = lean_nat_add(v_offset_931_, v___x_980_);
lean_dec(v_offset_931_);
lean_inc_ref(v_body_973_);
v___x_982_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_924_, v___x_925_, v___x_926_, v_start_927_, v_xs_928_, v___x_929_, v_body_973_, v___x_981_, v_snd_979_, v_a_933_, v_a_934_, v_a_977_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1009_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_a_984_ = lean_ctor_get(v___x_982_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_986_ = v___x_982_;
v_isShared_987_ = v_isSharedCheck_1009_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1009_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v_fst_988_; lean_object* v_snd_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1008_; 
v_fst_988_ = lean_ctor_get(v_a_983_, 0);
v_snd_989_ = lean_ctor_get(v_a_983_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_a_983_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_991_ = v_a_983_;
v_isShared_992_ = v_isSharedCheck_1008_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_snd_989_);
lean_inc(v_fst_988_);
lean_dec(v_a_983_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1008_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
uint8_t v___y_994_; size_t v___x_1002_; size_t v___x_1003_; uint8_t v___x_1004_; 
v___x_1002_ = lean_ptr_addr(v_binderType_972_);
v___x_1003_ = lean_ptr_addr(v_fst_978_);
v___x_1004_ = lean_usize_dec_eq(v___x_1002_, v___x_1003_);
if (v___x_1004_ == 0)
{
v___y_994_ = v___x_1004_;
goto v___jp_993_;
}
else
{
size_t v___x_1005_; size_t v___x_1006_; uint8_t v___x_1007_; 
v___x_1005_ = lean_ptr_addr(v_body_973_);
v___x_1006_ = lean_ptr_addr(v_fst_988_);
v___x_1007_ = lean_usize_dec_eq(v___x_1005_, v___x_1006_);
v___y_994_ = v___x_1007_;
goto v___jp_993_;
}
v___jp_993_:
{
if (v___y_994_ == 0)
{
lean_object* v___x_995_; 
lean_inc(v_binderName_971_);
lean_del_object(v___x_991_);
lean_del_object(v___x_986_);
lean_dec_ref_known(v_e_930_, 3);
v___x_995_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_binderName_971_, v_binderInfo_974_, v_fst_978_, v_fst_988_, v_snd_989_, v_a_933_, v_a_934_, v_a_984_);
return v___x_995_;
}
else
{
lean_object* v___x_997_; 
lean_dec(v_fst_988_);
lean_dec(v_fst_978_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v_e_930_);
v___x_997_ = v___x_991_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_e_930_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_snd_989_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_999_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_997_);
v___x_999_ = v___x_986_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_a_984_);
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
lean_dec(v_fst_978_);
lean_dec_ref_known(v_e_930_, 3);
return v___x_982_;
}
}
else
{
lean_dec_ref_known(v_e_930_, 3);
lean_dec(v_offset_931_);
lean_dec_ref(v___x_925_);
return v___x_975_;
}
}
case 7:
{
lean_object* v_binderName_1010_; lean_object* v_binderType_1011_; lean_object* v_body_1012_; uint8_t v_binderInfo_1013_; lean_object* v___x_1014_; 
v_binderName_1010_ = lean_ctor_get(v_e_930_, 0);
v_binderType_1011_ = lean_ctor_get(v_e_930_, 1);
v_body_1012_ = lean_ctor_get(v_e_930_, 2);
v_binderInfo_1013_ = lean_ctor_get_uint8(v_e_930_, sizeof(void*)*3 + 8);
lean_inc(v_offset_931_);
lean_inc_ref(v_binderType_1011_);
lean_inc_ref(v___x_925_);
v___x_1014_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_924_, v___x_925_, v___x_926_, v_start_927_, v_xs_928_, v___x_929_, v_binderType_1011_, v_offset_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v_a_1016_; lean_object* v_fst_1017_; lean_object* v_snd_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
v_a_1016_ = lean_ctor_get(v___x_1014_, 1);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1014_, 2);
v_fst_1017_ = lean_ctor_get(v_a_1015_, 0);
lean_inc(v_fst_1017_);
v_snd_1018_ = lean_ctor_get(v_a_1015_, 1);
lean_inc(v_snd_1018_);
lean_dec(v_a_1015_);
v___x_1019_ = lean_unsigned_to_nat(1u);
v___x_1020_ = lean_nat_add(v_offset_931_, v___x_1019_);
lean_dec(v_offset_931_);
lean_inc_ref(v_body_1012_);
v___x_1021_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_924_, v___x_925_, v___x_926_, v_start_927_, v_xs_928_, v___x_929_, v_body_1012_, v___x_1020_, v_snd_1018_, v_a_933_, v_a_934_, v_a_1016_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1048_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_a_1023_ = lean_ctor_get(v___x_1021_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1025_ = v___x_1021_;
v_isShared_1026_ = v_isSharedCheck_1048_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1048_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_fst_1027_; lean_object* v_snd_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1047_; 
v_fst_1027_ = lean_ctor_get(v_a_1022_, 0);
v_snd_1028_ = lean_ctor_get(v_a_1022_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_a_1022_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1030_ = v_a_1022_;
v_isShared_1031_ = v_isSharedCheck_1047_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_snd_1028_);
lean_inc(v_fst_1027_);
lean_dec(v_a_1022_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1047_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
uint8_t v___y_1033_; size_t v___x_1041_; size_t v___x_1042_; uint8_t v___x_1043_; 
v___x_1041_ = lean_ptr_addr(v_binderType_1011_);
v___x_1042_ = lean_ptr_addr(v_fst_1017_);
v___x_1043_ = lean_usize_dec_eq(v___x_1041_, v___x_1042_);
if (v___x_1043_ == 0)
{
v___y_1033_ = v___x_1043_;
goto v___jp_1032_;
}
else
{
size_t v___x_1044_; size_t v___x_1045_; uint8_t v___x_1046_; 
v___x_1044_ = lean_ptr_addr(v_body_1012_);
v___x_1045_ = lean_ptr_addr(v_fst_1027_);
v___x_1046_ = lean_usize_dec_eq(v___x_1044_, v___x_1045_);
v___y_1033_ = v___x_1046_;
goto v___jp_1032_;
}
v___jp_1032_:
{
if (v___y_1033_ == 0)
{
lean_object* v___x_1034_; 
lean_inc(v_binderName_1010_);
lean_del_object(v___x_1030_);
lean_del_object(v___x_1025_);
lean_dec_ref_known(v_e_930_, 3);
v___x_1034_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_binderName_1010_, v_binderInfo_1013_, v_fst_1017_, v_fst_1027_, v_snd_1028_, v_a_933_, v_a_934_, v_a_1023_);
return v___x_1034_;
}
else
{
lean_object* v___x_1036_; 
lean_dec(v_fst_1027_);
lean_dec(v_fst_1017_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v_e_930_);
v___x_1036_ = v___x_1030_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_e_930_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_snd_1028_);
v___x_1036_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1036_);
v___x_1038_ = v___x_1025_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_a_1023_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1017_);
lean_dec_ref_known(v_e_930_, 3);
return v___x_1021_;
}
}
else
{
lean_dec_ref_known(v_e_930_, 3);
lean_dec(v_offset_931_);
lean_dec_ref(v___x_925_);
return v___x_1014_;
}
}
case 8:
{
lean_object* v_declName_1049_; lean_object* v_type_1050_; lean_object* v_value_1051_; lean_object* v_body_1052_; uint8_t v_nondep_1053_; lean_object* v___x_1054_; 
v_declName_1049_ = lean_ctor_get(v_e_930_, 0);
v_type_1050_ = lean_ctor_get(v_e_930_, 1);
v_value_1051_ = lean_ctor_get(v_e_930_, 2);
v_body_1052_ = lean_ctor_get(v_e_930_, 3);
v_nondep_1053_ = lean_ctor_get_uint8(v_e_930_, sizeof(void*)*4 + 8);
lean_inc(v_offset_931_);
lean_inc_ref(v_type_1050_);
lean_inc_ref(v___x_925_);
v___x_1054_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_924_, v___x_925_, v___x_926_, v_start_927_, v_xs_928_, v___x_929_, v_type_1050_, v_offset_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v_a_1056_; lean_object* v_fst_1057_; lean_object* v_snd_1058_; lean_object* v___x_1059_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
v_a_1056_ = lean_ctor_get(v___x_1054_, 1);
lean_inc(v_a_1056_);
lean_dec_ref_known(v___x_1054_, 2);
v_fst_1057_ = lean_ctor_get(v_a_1055_, 0);
lean_inc(v_fst_1057_);
v_snd_1058_ = lean_ctor_get(v_a_1055_, 1);
lean_inc(v_snd_1058_);
lean_dec(v_a_1055_);
lean_inc(v_offset_931_);
lean_inc_ref(v_value_1051_);
lean_inc_ref(v___x_925_);
v___x_1059_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_924_, v___x_925_, v___x_926_, v_start_927_, v_xs_928_, v___x_929_, v_value_1051_, v_offset_931_, v_snd_1058_, v_a_933_, v_a_934_, v_a_1056_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v_a_1061_; lean_object* v_fst_1062_; lean_object* v_snd_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
v_a_1061_ = lean_ctor_get(v___x_1059_, 1);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1059_, 2);
v_fst_1062_ = lean_ctor_get(v_a_1060_, 0);
lean_inc(v_fst_1062_);
v_snd_1063_ = lean_ctor_get(v_a_1060_, 1);
lean_inc(v_snd_1063_);
lean_dec(v_a_1060_);
v___x_1064_ = lean_unsigned_to_nat(1u);
v___x_1065_ = lean_nat_add(v_offset_931_, v___x_1064_);
lean_dec(v_offset_931_);
lean_inc_ref(v_body_1052_);
v___x_1066_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_924_, v___x_925_, v___x_926_, v_start_927_, v_xs_928_, v___x_929_, v_body_1052_, v___x_1065_, v_snd_1063_, v_a_933_, v_a_934_, v_a_1061_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1097_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_a_1068_ = lean_ctor_get(v___x_1066_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1070_ = v___x_1066_;
v_isShared_1071_ = v_isSharedCheck_1097_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1097_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v_fst_1072_; lean_object* v_snd_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1096_; 
v_fst_1072_ = lean_ctor_get(v_a_1067_, 0);
v_snd_1073_ = lean_ctor_get(v_a_1067_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_a_1067_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1075_ = v_a_1067_;
v_isShared_1076_ = v_isSharedCheck_1096_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_snd_1073_);
lean_inc(v_fst_1072_);
lean_dec(v_a_1067_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1096_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
uint8_t v___y_1078_; size_t v___x_1090_; size_t v___x_1091_; uint8_t v___x_1092_; 
v___x_1090_ = lean_ptr_addr(v_type_1050_);
v___x_1091_ = lean_ptr_addr(v_fst_1057_);
v___x_1092_ = lean_usize_dec_eq(v___x_1090_, v___x_1091_);
if (v___x_1092_ == 0)
{
v___y_1078_ = v___x_1092_;
goto v___jp_1077_;
}
else
{
size_t v___x_1093_; size_t v___x_1094_; uint8_t v___x_1095_; 
v___x_1093_ = lean_ptr_addr(v_value_1051_);
v___x_1094_ = lean_ptr_addr(v_fst_1062_);
v___x_1095_ = lean_usize_dec_eq(v___x_1093_, v___x_1094_);
v___y_1078_ = v___x_1095_;
goto v___jp_1077_;
}
v___jp_1077_:
{
if (v___y_1078_ == 0)
{
lean_object* v___x_1079_; 
lean_inc(v_declName_1049_);
lean_del_object(v___x_1075_);
lean_del_object(v___x_1070_);
lean_dec_ref_known(v_e_930_, 4);
v___x_1079_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_1049_, v_fst_1057_, v_fst_1062_, v_fst_1072_, v_nondep_1053_, v_snd_1073_, v_a_933_, v_a_934_, v_a_1068_);
return v___x_1079_;
}
else
{
size_t v___x_1080_; size_t v___x_1081_; uint8_t v___x_1082_; 
v___x_1080_ = lean_ptr_addr(v_body_1052_);
v___x_1081_ = lean_ptr_addr(v_fst_1072_);
v___x_1082_ = lean_usize_dec_eq(v___x_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; 
lean_inc(v_declName_1049_);
lean_del_object(v___x_1075_);
lean_del_object(v___x_1070_);
lean_dec_ref_known(v_e_930_, 4);
v___x_1083_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_1049_, v_fst_1057_, v_fst_1062_, v_fst_1072_, v_nondep_1053_, v_snd_1073_, v_a_933_, v_a_934_, v_a_1068_);
return v___x_1083_;
}
else
{
lean_object* v___x_1085_; 
lean_dec(v_fst_1072_);
lean_dec(v_fst_1062_);
lean_dec(v_fst_1057_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v_e_930_);
v___x_1085_ = v___x_1075_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_e_930_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_snd_1073_);
v___x_1085_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1087_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1085_);
v___x_1087_ = v___x_1070_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_a_1068_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
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
lean_dec(v_fst_1062_);
lean_dec(v_fst_1057_);
lean_dec_ref_known(v_e_930_, 4);
return v___x_1066_;
}
}
else
{
lean_dec(v_fst_1057_);
lean_dec_ref_known(v_e_930_, 4);
lean_dec(v_offset_931_);
lean_dec_ref(v___x_925_);
return v___x_1059_;
}
}
else
{
lean_dec_ref_known(v_e_930_, 4);
lean_dec(v_offset_931_);
lean_dec_ref(v___x_925_);
return v___x_1054_;
}
}
case 10:
{
lean_object* v_data_1098_; lean_object* v_expr_1099_; lean_object* v___x_1100_; 
v_data_1098_ = lean_ctor_get(v_e_930_, 0);
v_expr_1099_ = lean_ctor_get(v_e_930_, 1);
lean_inc_ref(v_expr_1099_);
v___x_1100_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_924_, v___x_925_, v___x_926_, v_start_927_, v_xs_928_, v___x_929_, v_expr_1099_, v_offset_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1122_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
v_a_1102_ = lean_ctor_get(v___x_1100_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1104_ = v___x_1100_;
v_isShared_1105_ = v_isSharedCheck_1122_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_inc(v_a_1101_);
lean_dec(v___x_1100_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1122_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v_fst_1106_; lean_object* v_snd_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1121_; 
v_fst_1106_ = lean_ctor_get(v_a_1101_, 0);
v_snd_1107_ = lean_ctor_get(v_a_1101_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_a_1101_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1109_ = v_a_1101_;
v_isShared_1110_ = v_isSharedCheck_1121_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_snd_1107_);
lean_inc(v_fst_1106_);
lean_dec(v_a_1101_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1121_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
size_t v___x_1111_; size_t v___x_1112_; uint8_t v___x_1113_; 
v___x_1111_ = lean_ptr_addr(v_expr_1099_);
v___x_1112_ = lean_ptr_addr(v_fst_1106_);
v___x_1113_ = lean_usize_dec_eq(v___x_1111_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; 
lean_inc(v_data_1098_);
lean_del_object(v___x_1109_);
lean_del_object(v___x_1104_);
lean_dec_ref_known(v_e_930_, 2);
v___x_1114_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(v_data_1098_, v_fst_1106_, v_snd_1107_, v_a_933_, v_a_934_, v_a_1102_);
return v___x_1114_;
}
else
{
lean_object* v___x_1116_; 
lean_dec(v_fst_1106_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v_e_930_);
v___x_1116_ = v___x_1109_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_e_930_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_snd_1107_);
v___x_1116_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1118_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1116_);
v___x_1118_ = v___x_1104_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_a_1102_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_930_, 2);
return v___x_1100_;
}
}
case 11:
{
lean_object* v_typeName_1123_; lean_object* v_idx_1124_; lean_object* v_struct_1125_; lean_object* v___x_1126_; 
v_typeName_1123_ = lean_ctor_get(v_e_930_, 0);
v_idx_1124_ = lean_ctor_get(v_e_930_, 1);
v_struct_1125_ = lean_ctor_get(v_e_930_, 2);
lean_inc_ref(v_struct_1125_);
v___x_1126_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_924_, v___x_925_, v___x_926_, v_start_927_, v_xs_928_, v___x_929_, v_struct_1125_, v_offset_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1148_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_a_1128_ = lean_ctor_get(v___x_1126_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1130_ = v___x_1126_;
v_isShared_1131_ = v_isSharedCheck_1148_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1148_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v_fst_1132_; lean_object* v_snd_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1147_; 
v_fst_1132_ = lean_ctor_get(v_a_1127_, 0);
v_snd_1133_ = lean_ctor_get(v_a_1127_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_a_1127_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1135_ = v_a_1127_;
v_isShared_1136_ = v_isSharedCheck_1147_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_snd_1133_);
lean_inc(v_fst_1132_);
lean_dec(v_a_1127_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1147_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
size_t v___x_1137_; size_t v___x_1138_; uint8_t v___x_1139_; 
v___x_1137_ = lean_ptr_addr(v_struct_1125_);
v___x_1138_ = lean_ptr_addr(v_fst_1132_);
v___x_1139_ = lean_usize_dec_eq(v___x_1137_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; 
lean_inc(v_idx_1124_);
lean_inc(v_typeName_1123_);
lean_del_object(v___x_1135_);
lean_del_object(v___x_1130_);
lean_dec_ref_known(v_e_930_, 3);
v___x_1140_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(v_typeName_1123_, v_idx_1124_, v_fst_1132_, v_snd_1133_, v_a_933_, v_a_934_, v_a_1128_);
return v___x_1140_;
}
else
{
lean_object* v___x_1142_; 
lean_dec(v_fst_1132_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v_e_930_);
v___x_1142_ = v___x_1135_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_e_930_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_snd_1133_);
v___x_1142_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1144_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1142_);
v___x_1144_ = v___x_1130_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_a_1128_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_930_, 3);
return v___x_1126_;
}
}
default: 
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec(v_offset_931_);
lean_dec_ref(v_e_930_);
lean_dec_ref(v___x_925_);
v___x_1149_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3);
v___x_1150_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(v___x_1149_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
return v___x_1150_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(lean_object* v_minIndex_1151_, lean_object* v___x_1152_, lean_object* v___x_1153_, lean_object* v_start_1154_, lean_object* v_xs_1155_, lean_object* v___x_1156_, lean_object* v_e_1157_, lean_object* v_offset_1158_, lean_object* v_a_1159_, uint8_t v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_key_1163_; lean_object* v_a_1165_; lean_object* v___y_1179_; lean_object* v___y_1184_; lean_object* v___x_1189_; 
lean_inc(v_offset_1158_);
lean_inc_ref(v_e_1157_);
v_key_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1163_, 0, v_e_1157_);
lean_ctor_set(v_key_1163_, 1, v_offset_1158_);
v___x_1189_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_a_1159_, v_key_1163_);
if (lean_obj_tag(v___x_1189_) == 1)
{
lean_object* v_val_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_dec_ref_known(v_key_1163_, 2);
lean_dec(v_offset_1158_);
lean_dec_ref(v_e_1157_);
lean_dec_ref(v___x_1152_);
v_val_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_val_1190_);
lean_dec_ref_known(v___x_1189_, 1);
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v_val_1190_);
lean_ctor_set(v___x_1191_, 1, v_a_1159_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v_a_1162_);
return v___x_1192_;
}
else
{
lean_dec(v___x_1189_);
switch(lean_obj_tag(v_e_1157_))
{
case 1:
{
lean_object* v_fvarId_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_dec_ref(v___x_1152_);
v_fvarId_1193_ = lean_ctor_get(v_e_1157_, 0);
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = lean_unsigned_to_nat(1u);
v___x_1196_ = lean_nat_sub(v___x_1153_, v___x_1195_);
v___x_1197_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_1154_, v_xs_1155_, v_fvarId_1193_, v___x_1194_, v___x_1196_);
if (lean_obj_tag(v___x_1197_) == 1)
{
lean_object* v_val_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec_ref_known(v_e_1157_, 1);
v_val_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_val_1198_);
lean_dec_ref_known(v___x_1197_, 1);
v___x_1199_ = lean_nat_add(v_offset_1158_, v_val_1198_);
lean_dec(v_val_1198_);
lean_dec(v_offset_1158_);
v___x_1200_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v___x_1199_, v_a_1162_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v_a_1202_; lean_object* v___x_1203_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
v_a_1202_ = lean_ctor_get(v___x_1200_, 1);
lean_inc(v_a_1202_);
lean_dec_ref_known(v___x_1200_, 2);
v___x_1203_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1163_, v_a_1201_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1202_);
return v___x_1203_;
}
else
{
lean_object* v_a_1204_; lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec_ref_known(v_key_1163_, 2);
lean_dec_ref(v_a_1159_);
v_a_1204_ = lean_ctor_get(v___x_1200_, 0);
v_a_1205_ = lean_ctor_get(v___x_1200_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1200_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_inc(v_a_1204_);
lean_dec(v___x_1200_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1204_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
else
{
lean_object* v___x_1213_; 
lean_dec(v___x_1197_);
lean_dec(v_offset_1158_);
v___x_1213_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1163_, v_e_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
return v___x_1213_;
}
}
case 9:
{
lean_object* v___x_1214_; 
lean_dec(v_offset_1158_);
lean_dec_ref(v___x_1152_);
v___x_1214_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1163_, v_e_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
return v___x_1214_;
}
case 2:
{
lean_object* v___x_1215_; 
lean_dec(v_offset_1158_);
lean_dec_ref(v___x_1152_);
v___x_1215_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1163_, v_e_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
return v___x_1215_;
}
case 0:
{
lean_object* v___x_1216_; 
lean_dec(v_offset_1158_);
lean_dec_ref(v___x_1152_);
v___x_1216_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1163_, v_e_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
return v___x_1216_;
}
case 4:
{
lean_object* v___x_1217_; 
lean_dec(v_offset_1158_);
lean_dec_ref(v___x_1152_);
v___x_1217_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1163_, v_e_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
return v___x_1217_;
}
case 3:
{
lean_object* v___x_1218_; 
lean_dec(v_offset_1158_);
lean_dec_ref(v___x_1152_);
v___x_1218_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1163_, v_e_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
return v___x_1218_;
}
default: 
{
uint8_t v___x_1219_; 
v___x_1219_ = l_Lean_Expr_hasFVar(v_e_1157_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; 
lean_dec(v_offset_1158_);
lean_dec_ref(v___x_1152_);
v___x_1220_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1163_, v_e_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
return v___x_1220_;
}
else
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v___x_1156_, v_e_1157_);
if (lean_obj_tag(v___x_1221_) == 1)
{
lean_object* v_val_1222_; 
v_val_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_val_1222_);
lean_dec_ref_known(v___x_1221_, 1);
if (lean_obj_tag(v_val_1222_) == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1224_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v___x_1223_);
v___y_1184_ = v___x_1224_;
goto v___jp_1183_;
}
else
{
lean_object* v_val_1225_; 
v_val_1225_ = lean_ctor_get(v_val_1222_, 0);
lean_inc(v_val_1225_);
lean_dec_ref_known(v_val_1222_, 1);
v___y_1184_ = v_val_1225_;
goto v___jp_1183_;
}
}
else
{
lean_dec(v___x_1221_);
v_a_1165_ = v_a_1162_;
goto v___jp_1164_;
}
}
}
}
}
v___jp_1164_:
{
switch(lean_obj_tag(v_e_1157_))
{
case 9:
{
lean_object* v___x_1166_; 
lean_dec(v_offset_1158_);
lean_dec_ref(v___x_1152_);
v___x_1166_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1163_, v_e_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1165_);
return v___x_1166_;
}
case 2:
{
lean_object* v___x_1167_; 
lean_dec(v_offset_1158_);
lean_dec_ref(v___x_1152_);
v___x_1167_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1163_, v_e_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1165_);
return v___x_1167_;
}
case 0:
{
lean_object* v___x_1168_; 
lean_dec(v_offset_1158_);
lean_dec_ref(v___x_1152_);
v___x_1168_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1163_, v_e_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1165_);
return v___x_1168_;
}
case 1:
{
lean_object* v___x_1169_; 
lean_dec(v_offset_1158_);
lean_dec_ref(v___x_1152_);
v___x_1169_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1163_, v_e_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1165_);
return v___x_1169_;
}
case 4:
{
lean_object* v___x_1170_; 
lean_dec(v_offset_1158_);
lean_dec_ref(v___x_1152_);
v___x_1170_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1163_, v_e_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1165_);
return v___x_1170_;
}
case 3:
{
lean_object* v___x_1171_; 
lean_dec(v_offset_1158_);
lean_dec_ref(v___x_1152_);
v___x_1171_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1163_, v_e_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1165_);
return v___x_1171_;
}
default: 
{
lean_object* v___x_1172_; 
v___x_1172_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v_minIndex_1151_, v___x_1152_, v___x_1153_, v_start_1154_, v_xs_1155_, v___x_1156_, v_e_1157_, v_offset_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1165_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v_a_1174_; lean_object* v_fst_1175_; lean_object* v_snd_1176_; lean_object* v___x_1177_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
v_a_1174_ = lean_ctor_get(v___x_1172_, 1);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___x_1172_, 2);
v_fst_1175_ = lean_ctor_get(v_a_1173_, 0);
lean_inc(v_fst_1175_);
v_snd_1176_ = lean_ctor_get(v_a_1173_, 1);
lean_inc(v_snd_1176_);
lean_dec(v_a_1173_);
v___x_1177_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1163_, v_fst_1175_, v_snd_1176_, v_a_1160_, v_a_1161_, v_a_1174_);
return v___x_1177_;
}
else
{
lean_dec_ref_known(v_key_1163_, 2);
return v___x_1172_;
}
}
}
}
v___jp_1178_:
{
lean_object* v_maxIndex_1180_; uint8_t v___x_1181_; 
v_maxIndex_1180_ = l_Lean_LocalDecl_index(v___y_1179_);
lean_dec_ref(v___y_1179_);
v___x_1181_ = lean_nat_dec_lt(v_maxIndex_1180_, v_minIndex_1151_);
lean_dec(v_maxIndex_1180_);
if (v___x_1181_ == 0)
{
v_a_1165_ = v_a_1162_;
goto v___jp_1164_;
}
else
{
lean_object* v___x_1182_; 
lean_dec(v_offset_1158_);
lean_dec_ref(v___x_1152_);
v___x_1182_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1163_, v_e_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
return v___x_1182_;
}
}
v___jp_1183_:
{
lean_object* v___x_1185_; 
lean_inc_ref(v___x_1152_);
v___x_1185_ = lean_local_ctx_find(v___x_1152_, v___y_1184_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1187_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1186_);
v___y_1179_ = v___x_1187_;
goto v___jp_1178_;
}
else
{
lean_object* v_val_1188_; 
v_val_1188_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_val_1188_);
lean_dec_ref_known(v___x_1185_, 1);
v___y_1179_ = v_val_1188_;
goto v___jp_1178_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5___boxed(lean_object* v_minIndex_1226_, lean_object* v___x_1227_, lean_object* v___x_1228_, lean_object* v_start_1229_, lean_object* v_xs_1230_, lean_object* v___x_1231_, lean_object* v_e_1232_, lean_object* v_offset_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
uint8_t v_a_boxed_1238_; lean_object* v_res_1239_; 
v_a_boxed_1238_ = lean_unbox(v_a_1235_);
v_res_1239_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_1226_, v___x_1227_, v___x_1228_, v_start_1229_, v_xs_1230_, v___x_1231_, v_e_1232_, v_offset_1233_, v_a_1234_, v_a_boxed_1238_, v_a_1236_, v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_xs_1230_);
lean_dec(v_start_1229_);
lean_dec(v___x_1228_);
lean_dec(v_minIndex_1226_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___boxed(lean_object* v_minIndex_1240_, lean_object* v___x_1241_, lean_object* v___x_1242_, lean_object* v_start_1243_, lean_object* v_xs_1244_, lean_object* v___x_1245_, lean_object* v_e_1246_, lean_object* v_offset_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
uint8_t v_a_boxed_1252_; lean_object* v_res_1253_; 
v_a_boxed_1252_ = lean_unbox(v_a_1249_);
v_res_1253_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v_minIndex_1240_, v___x_1241_, v___x_1242_, v_start_1243_, v_xs_1244_, v___x_1245_, v_e_1246_, v_offset_1247_, v_a_1248_, v_a_boxed_1252_, v_a_1250_, v_a_1251_);
lean_dec_ref(v_a_1250_);
lean_dec_ref(v___x_1245_);
lean_dec_ref(v_xs_1244_);
lean_dec(v_start_1243_);
lean_dec(v___x_1242_);
lean_dec(v_minIndex_1240_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___lam__0(lean_object* v_e_1254_, lean_object* v_lctx_1255_, lean_object* v___x_1256_, lean_object* v_start_1257_, lean_object* v_xs_1258_, lean_object* v_maxFVar_1259_, uint8_t v_debug_1260_, uint8_t v___x_1261_, lean_object* v___x_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1313_; lean_object* v___x_1334_; 
lean_inc_ref(v_lctx_1255_);
v___x_1334_ = lean_local_ctx_find(v_lctx_1255_, v___x_1262_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1336_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1335_);
v___y_1313_ = v___x_1336_;
goto v___jp_1312_;
}
else
{
lean_object* v_val_1337_; 
v_val_1337_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_val_1337_);
lean_dec_ref_known(v___x_1334_, 1);
v___y_1313_ = v_val_1337_;
goto v___jp_1312_;
}
v___jp_1265_:
{
switch(lean_obj_tag(v_e_1254_))
{
case 9:
{
lean_object* v___x_1268_; 
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v_lctx_1255_);
v___x_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1268_, 0, v_e_1254_);
lean_ctor_set(v___x_1268_, 1, v___y_1264_);
return v___x_1268_;
}
case 2:
{
lean_object* v___x_1269_; 
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v_lctx_1255_);
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v_e_1254_);
lean_ctor_set(v___x_1269_, 1, v___y_1264_);
return v___x_1269_;
}
case 0:
{
lean_object* v___x_1270_; 
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v_lctx_1255_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v_e_1254_);
lean_ctor_set(v___x_1270_, 1, v___y_1264_);
return v___x_1270_;
}
case 1:
{
lean_object* v___x_1271_; 
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v_lctx_1255_);
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v_e_1254_);
lean_ctor_set(v___x_1271_, 1, v___y_1264_);
return v___x_1271_;
}
case 4:
{
lean_object* v___x_1272_; 
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v_lctx_1255_);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v_e_1254_);
lean_ctor_set(v___x_1272_, 1, v___y_1264_);
return v___x_1272_;
}
case 3:
{
lean_object* v___x_1273_; 
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v_lctx_1255_);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v_e_1254_);
lean_ctor_set(v___x_1273_, 1, v___y_1264_);
return v___x_1273_;
}
default: 
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1274_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0);
v___x_1275_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1);
lean_inc(v___y_1266_);
v___x_1276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1276_, 0, v___y_1266_);
lean_ctor_set(v___x_1276_, 1, v___x_1274_);
lean_ctor_set(v___x_1276_, 2, v___x_1275_);
v___x_1277_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v___y_1267_, v_lctx_1255_, v___x_1256_, v_start_1257_, v_xs_1258_, v_maxFVar_1259_, v_e_1254_, v___y_1266_, v___x_1276_, v_debug_1260_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1267_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1287_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_a_1279_ = lean_ctor_get(v___x_1277_, 1);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1281_ = v___x_1277_;
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_fst_1283_; lean_object* v___x_1285_; 
v_fst_1283_ = lean_ctor_get(v_a_1278_, 0);
lean_inc(v_fst_1283_);
lean_dec(v_a_1278_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v_fst_1283_);
v___x_1285_ = v___x_1281_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_fst_1283_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_a_1279_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v_a_1288_ = lean_ctor_get(v___x_1277_, 0);
v_a_1289_ = lean_ctor_get(v___x_1277_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1277_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_inc(v_a_1288_);
lean_dec(v___x_1277_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1288_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
v___jp_1297_:
{
lean_object* v_maxIndex_1301_; uint8_t v___x_1302_; 
v_maxIndex_1301_ = l_Lean_LocalDecl_index(v___y_1300_);
lean_dec_ref(v___y_1300_);
v___x_1302_ = lean_nat_dec_lt(v_maxIndex_1301_, v___y_1299_);
lean_dec(v_maxIndex_1301_);
if (v___x_1302_ == 0)
{
v___y_1266_ = v___y_1298_;
v___y_1267_ = v___y_1299_;
goto v___jp_1265_;
}
else
{
lean_object* v___x_1303_; 
lean_dec(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v_lctx_1255_);
v___x_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1303_, 0, v_e_1254_);
lean_ctor_set(v___x_1303_, 1, v___y_1264_);
return v___x_1303_;
}
}
v___jp_1304_:
{
lean_object* v___x_1308_; 
lean_inc_ref(v_lctx_1255_);
v___x_1308_ = lean_local_ctx_find(v_lctx_1255_, v___y_1307_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1310_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1309_);
v___y_1298_ = v___y_1305_;
v___y_1299_ = v___y_1306_;
v___y_1300_ = v___x_1310_;
goto v___jp_1297_;
}
else
{
lean_object* v_val_1311_; 
v_val_1311_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_val_1311_);
lean_dec_ref_known(v___x_1308_, 1);
v___y_1298_ = v___y_1305_;
v___y_1299_ = v___y_1306_;
v___y_1300_ = v_val_1311_;
goto v___jp_1297_;
}
}
v___jp_1312_:
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1254_))
{
case 1:
{
lean_object* v_fvarId_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_dec_ref(v___y_1313_);
lean_dec_ref(v_lctx_1255_);
v_fvarId_1315_ = lean_ctor_get(v_e_1254_, 0);
v___x_1316_ = lean_unsigned_to_nat(1u);
v___x_1317_ = lean_nat_sub(v___x_1256_, v___x_1316_);
v___x_1318_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_1257_, v_xs_1258_, v_fvarId_1315_, v___x_1314_, v___x_1317_);
if (lean_obj_tag(v___x_1318_) == 1)
{
lean_object* v_val_1319_; lean_object* v___x_1320_; 
lean_dec_ref_known(v_e_1254_, 1);
v_val_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_val_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1320_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v_val_1319_, v___y_1264_);
return v___x_1320_;
}
else
{
lean_object* v___x_1321_; 
lean_dec(v___x_1318_);
v___x_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1321_, 0, v_e_1254_);
lean_ctor_set(v___x_1321_, 1, v___y_1264_);
return v___x_1321_;
}
}
case 9:
{
lean_object* v___x_1322_; 
lean_dec_ref(v___y_1313_);
lean_dec_ref(v_lctx_1255_);
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v_e_1254_);
lean_ctor_set(v___x_1322_, 1, v___y_1264_);
return v___x_1322_;
}
case 2:
{
lean_object* v___x_1323_; 
lean_dec_ref(v___y_1313_);
lean_dec_ref(v_lctx_1255_);
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_e_1254_);
lean_ctor_set(v___x_1323_, 1, v___y_1264_);
return v___x_1323_;
}
case 0:
{
lean_object* v___x_1324_; 
lean_dec_ref(v___y_1313_);
lean_dec_ref(v_lctx_1255_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v_e_1254_);
lean_ctor_set(v___x_1324_, 1, v___y_1264_);
return v___x_1324_;
}
case 4:
{
lean_object* v___x_1325_; 
lean_dec_ref(v___y_1313_);
lean_dec_ref(v_lctx_1255_);
v___x_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1325_, 0, v_e_1254_);
lean_ctor_set(v___x_1325_, 1, v___y_1264_);
return v___x_1325_;
}
case 3:
{
lean_object* v___x_1326_; 
lean_dec_ref(v___y_1313_);
lean_dec_ref(v_lctx_1255_);
v___x_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1326_, 0, v_e_1254_);
lean_ctor_set(v___x_1326_, 1, v___y_1264_);
return v___x_1326_;
}
default: 
{
if (v___x_1261_ == 0)
{
lean_object* v___x_1327_; 
lean_dec_ref(v___y_1313_);
lean_dec_ref(v_lctx_1255_);
v___x_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1327_, 0, v_e_1254_);
lean_ctor_set(v___x_1327_, 1, v___y_1264_);
return v___x_1327_;
}
else
{
lean_object* v_minIndex_1328_; lean_object* v___x_1329_; 
v_minIndex_1328_ = l_Lean_LocalDecl_index(v___y_1313_);
lean_dec_ref(v___y_1313_);
v___x_1329_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_maxFVar_1259_, v_e_1254_);
if (lean_obj_tag(v___x_1329_) == 1)
{
lean_object* v_val_1330_; 
v_val_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_val_1330_);
lean_dec_ref_known(v___x_1329_, 1);
if (lean_obj_tag(v_val_1330_) == 0)
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1332_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v___x_1331_);
v___y_1305_ = v___x_1314_;
v___y_1306_ = v_minIndex_1328_;
v___y_1307_ = v___x_1332_;
goto v___jp_1304_;
}
else
{
lean_object* v_val_1333_; 
v_val_1333_ = lean_ctor_get(v_val_1330_, 0);
lean_inc(v_val_1333_);
lean_dec_ref_known(v_val_1330_, 1);
v___y_1305_ = v___x_1314_;
v___y_1306_ = v_minIndex_1328_;
v___y_1307_ = v_val_1333_;
goto v___jp_1304_;
}
}
else
{
lean_dec(v___x_1329_);
v___y_1266_ = v___x_1314_;
v___y_1267_ = v_minIndex_1328_;
goto v___jp_1265_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___lam__0___boxed(lean_object* v_e_1338_, lean_object* v_lctx_1339_, lean_object* v___x_1340_, lean_object* v_start_1341_, lean_object* v_xs_1342_, lean_object* v_maxFVar_1343_, lean_object* v_debug_1344_, lean_object* v___x_1345_, lean_object* v___x_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
uint8_t v_debug_boxed_1349_; uint8_t v___x_27680__boxed_1350_; lean_object* v_res_1351_; 
v_debug_boxed_1349_ = lean_unbox(v_debug_1344_);
v___x_27680__boxed_1350_ = lean_unbox(v___x_1345_);
v_res_1351_ = l_Lean_Meta_Sym_abstractFVarsRange___lam__0(v_e_1338_, v_lctx_1339_, v___x_1340_, v_start_1341_, v_xs_1342_, v_maxFVar_1343_, v_debug_boxed_1349_, v___x_27680__boxed_1350_, v___x_1346_, v___y_1347_, v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec_ref(v_maxFVar_1343_);
lean_dec_ref(v_xs_1342_);
lean_dec(v_start_1341_);
lean_dec(v___x_1340_);
return v_res_1351_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_abstractFVarsRange___closed__2(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1354_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__2));
v___x_1355_ = lean_unsigned_to_nat(16u);
v___x_1356_ = lean_unsigned_to_nat(62u);
v___x_1357_ = ((lean_object*)(l_Lean_Meta_Sym_abstractFVarsRange___closed__1));
v___x_1358_ = ((lean_object*)(l_Lean_Meta_Sym_abstractFVarsRange___closed__0));
v___x_1359_ = l_mkPanicMessageWithDecl(v___x_1358_, v___x_1357_, v___x_1356_, v___x_1355_, v___x_1354_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange(lean_object* v_e_1360_, lean_object* v_start_1361_, lean_object* v_xs_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
uint8_t v___x_1370_; 
v___x_1370_ = l_Lean_Expr_hasFVar(v_e_1360_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; 
lean_dec_ref(v_xs_1362_);
lean_dec(v_start_1361_);
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_e_1360_);
return v___x_1371_;
}
else
{
lean_object* v___x_1372_; uint8_t v___x_1373_; 
v___x_1372_ = lean_array_get_size(v_xs_1362_);
v___x_1373_ = lean_nat_dec_lt(v_start_1361_, v___x_1372_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; 
lean_dec_ref(v_xs_1362_);
lean_dec(v_start_1361_);
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v_e_1360_);
return v___x_1374_;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v_lctx_1378_; lean_object* v_maxFVar_1379_; uint8_t v_debug_1380_; lean_object* v_env_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___f_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1375_ = lean_st_ref_get(v_a_1364_);
v___x_1376_ = lean_st_ref_get(v_a_1364_);
v___x_1377_ = lean_st_ref_get(v_a_1368_);
v_lctx_1378_ = lean_ctor_get(v_a_1365_, 2);
v_maxFVar_1379_ = lean_ctor_get(v___x_1375_, 1);
lean_inc_ref(v_maxFVar_1379_);
lean_dec(v___x_1375_);
v_debug_1380_ = lean_ctor_get_uint8(v___x_1376_, sizeof(void*)*11);
lean_dec(v___x_1376_);
v_env_1381_ = lean_ctor_get(v___x_1377_, 0);
lean_inc_ref(v_env_1381_);
lean_dec(v___x_1377_);
v___x_1382_ = 0;
v___x_1383_ = lean_array_fget_borrowed(v_xs_1362_, v_start_1361_);
v___x_1384_ = l_Lean_Expr_fvarId_x21(v___x_1383_);
v___x_1385_ = lean_box(v_debug_1380_);
v___x_1386_ = lean_box(v___x_1370_);
lean_inc_ref(v_lctx_1378_);
v___f_1387_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_abstractFVarsRange___lam__0___boxed), 11, 9);
lean_closure_set(v___f_1387_, 0, v_e_1360_);
lean_closure_set(v___f_1387_, 1, v_lctx_1378_);
lean_closure_set(v___f_1387_, 2, v___x_1372_);
lean_closure_set(v___f_1387_, 3, v_start_1361_);
lean_closure_set(v___f_1387_, 4, v_xs_1362_);
lean_closure_set(v___f_1387_, 5, v_maxFVar_1379_);
lean_closure_set(v___f_1387_, 6, v___x_1385_);
lean_closure_set(v___f_1387_, 7, v___x_1386_);
lean_closure_set(v___f_1387_, 8, v___x_1384_);
v___x_1388_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1388_, 0, v_env_1381_);
lean_ctor_set_uint8(v___x_1388_, sizeof(void*)*1, v___x_1382_);
lean_ctor_set_uint8(v___x_1388_, sizeof(void*)*1 + 1, v___x_1382_);
v___x_1389_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1387_, v___x_1388_, v_a_1364_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1400_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1400_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1400_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
if (lean_obj_tag(v_a_1390_) == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_dec_ref_known(v_a_1390_, 1);
lean_del_object(v___x_1392_);
v___x_1394_ = lean_obj_once(&l_Lean_Meta_Sym_abstractFVarsRange___closed__2, &l_Lean_Meta_Sym_abstractFVarsRange___closed__2_once, _init_l_Lean_Meta_Sym_abstractFVarsRange___closed__2);
v___x_1395_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v___x_1394_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
return v___x_1395_;
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; 
v_a_1396_ = lean_ctor_get(v_a_1390_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v_a_1390_, 1);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v_a_1396_);
v___x_1398_ = v___x_1392_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
v_a_1401_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1389_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1389_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___boxed(lean_object* v_e_1409_, lean_object* v_start_1410_, lean_object* v_xs_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1409_, v_start_1410_, v_xs_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_);
lean_dec(v_a_1417_);
lean_dec_ref(v_a_1416_);
lean_dec(v_a_1415_);
lean_dec_ref(v_a_1414_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(lean_object* v_00_u03b2_1420_, lean_object* v_x_1421_, lean_object* v_x_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_x_1421_, v_x_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___boxed(lean_object* v_00_u03b2_1424_, lean_object* v_x_1425_, lean_object* v_x_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(v_00_u03b2_1424_, v_x_1425_, v_x_1426_);
lean_dec_ref(v_x_1426_);
lean_dec_ref(v_x_1425_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2(lean_object* v_00_u03b2_1428_, lean_object* v_x_1429_, size_t v_x_1430_, lean_object* v_x_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_1429_, v_x_1430_, v_x_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_){
_start:
{
size_t v_x_27970__boxed_1437_; lean_object* v_res_1438_; 
v_x_27970__boxed_1437_ = lean_unbox_usize(v_x_1435_);
lean_dec(v_x_1435_);
v_res_1438_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2(v_00_u03b2_1433_, v_x_1434_, v_x_27970__boxed_1437_, v_x_1436_);
lean_dec_ref(v_x_1436_);
lean_dec_ref(v_x_1434_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_1439_, lean_object* v_keys_1440_, lean_object* v_vals_1441_, lean_object* v_heq_1442_, lean_object* v_i_1443_, lean_object* v_k_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_keys_1440_, v_vals_1441_, v_i_1443_, v_k_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1446_, lean_object* v_keys_1447_, lean_object* v_vals_1448_, lean_object* v_heq_1449_, lean_object* v_i_1450_, lean_object* v_k_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5(v_00_u03b2_1446_, v_keys_1447_, v_vals_1448_, v_heq_1449_, v_i_1450_, v_k_1451_);
lean_dec_ref(v_k_1451_);
lean_dec_ref(v_vals_1448_);
lean_dec_ref(v_keys_1447_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_1453_, lean_object* v_m_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_m_1454_, v_a_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1457_, lean_object* v_m_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8(v_00_u03b2_1457_, v_m_1458_, v_a_1459_);
lean_dec_ref(v_a_1459_);
lean_dec_ref(v_m_1458_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16(lean_object* v_00_u03b2_1461_, lean_object* v_m_1462_, lean_object* v_query_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_m_1462_, v_query_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___boxed(lean_object* v_00_u03b2_1465_, lean_object* v_m_1466_, lean_object* v_query_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16(v_00_u03b2_1465_, v_m_1466_, v_query_1467_);
lean_dec_ref(v_query_1467_);
lean_dec_ref(v_m_1466_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17(lean_object* v_00_u03b2_1469_, lean_object* v_m_1470_, lean_object* v_query_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17___redArg(v_m_1470_, v_query_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17___boxed(lean_object* v_00_u03b2_1473_, lean_object* v_m_1474_, lean_object* v_query_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17(v_00_u03b2_1473_, v_m_1474_, v_query_1475_);
lean_dec_ref(v_query_1475_);
lean_dec_ref(v_m_1474_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_1477_, lean_object* v_m_1478_, lean_object* v_query_1479_, lean_object* v_x_1480_, lean_object* v_x_1481_, lean_object* v_x_1482_, lean_object* v_x_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17_spec__18___redArg(v_m_1478_, v_query_1479_, v_x_1480_, v_x_1481_, v_x_1482_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17_spec__18___boxed(lean_object* v_00_u03b2_1485_, lean_object* v_m_1486_, lean_object* v_query_1487_, lean_object* v_x_1488_, lean_object* v_x_1489_, lean_object* v_x_1490_, lean_object* v_x_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16_spec__17_spec__18(v_00_u03b2_1485_, v_m_1486_, v_query_1487_, v_x_1488_, v_x_1489_, v_x_1490_, v_x_1491_);
lean_dec_ref(v_query_1487_);
lean_dec_ref(v_m_1486_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars(lean_object* v_e_1493_, lean_object* v_xs_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_unsigned_to_nat(0u);
v___x_1503_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1493_, v___x_1502_, v_xs_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___boxed(lean_object* v_e_1504_, lean_object* v_xs_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_Meta_Sym_abstractFVars(v_e_1504_, v_xs_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(lean_object* v_x_1514_, uint8_t v_bi_1515_, lean_object* v_t_1516_, lean_object* v_b_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v___y_1526_; lean_object* v___x_1529_; uint8_t v_debug_1530_; 
v___x_1529_ = lean_st_ref_get(v___y_1519_);
v_debug_1530_ = lean_ctor_get_uint8(v___x_1529_, sizeof(void*)*11);
lean_dec(v___x_1529_);
if (v_debug_1530_ == 0)
{
v___y_1526_ = v___y_1519_;
goto v___jp_1525_;
}
else
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1516_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v___x_1532_; 
lean_dec_ref_known(v___x_1531_, 1);
v___x_1532_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_dec_ref_known(v___x_1532_, 1);
v___y_1526_ = v___y_1519_;
goto v___jp_1525_;
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec_ref(v_b_1517_);
lean_dec_ref(v_t_1516_);
lean_dec(v_x_1514_);
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1532_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1532_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec_ref(v_b_1517_);
lean_dec_ref(v_t_1516_);
lean_dec(v_x_1514_);
v_a_1541_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1531_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1531_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
v___jp_1525_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = l_Lean_Expr_lam___override(v_x_1514_, v_t_1516_, v_b_1517_, v_bi_1515_);
v___x_1528_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1527_, v___y_1526_);
return v___x_1528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0___boxed(lean_object* v_x_1549_, lean_object* v_bi_1550_, lean_object* v_t_1551_, lean_object* v_b_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
uint8_t v_bi_boxed_1560_; lean_object* v_res_1561_; 
v_bi_boxed_1560_ = lean_unbox(v_bi_1550_);
v_res_1561_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v_x_1549_, v_bi_boxed_1560_, v_t_1551_, v_b_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(lean_object* v_xs_1562_, lean_object* v_i_1563_, lean_object* v_a_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_zero_1572_; uint8_t v_isZero_1573_; 
v_zero_1572_ = lean_unsigned_to_nat(0u);
v_isZero_1573_ = lean_nat_dec_eq(v_i_1563_, v_zero_1572_);
if (v_isZero_1573_ == 1)
{
lean_object* v___x_1574_; 
lean_dec(v_i_1563_);
lean_dec_ref(v_xs_1562_);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v_a_1564_);
return v___x_1574_;
}
else
{
lean_object* v_one_1575_; lean_object* v_n_1576_; lean_object* v___y_1578_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v_one_1575_ = lean_unsigned_to_nat(1u);
v_n_1576_ = lean_nat_sub(v_i_1563_, v_one_1575_);
lean_dec(v_i_1563_);
v___x_1581_ = lean_array_fget_borrowed(v_xs_1562_, v_n_1576_);
v___x_1582_ = l_Lean_Expr_fvarId_x21(v___x_1581_);
v___x_1583_ = l_Lean_FVarId_getDecl___redArg(v___x_1582_, v___y_1567_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
v___x_1585_ = l_Lean_LocalDecl_type(v_a_1584_);
lean_inc_ref(v_xs_1562_);
lean_inc(v_n_1576_);
v___x_1586_ = l_Lean_Meta_Sym_abstractFVarsRange(v___x_1585_, v_n_1576_, v_xs_1562_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; lean_object* v___x_1590_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1588_ = l_Lean_LocalDecl_userName(v_a_1584_);
v___x_1589_ = l_Lean_LocalDecl_binderInfo(v_a_1584_);
lean_dec(v_a_1584_);
v___x_1590_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v___x_1588_, v___x_1589_, v_a_1587_, v_a_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
v___y_1578_ = v___x_1590_;
goto v___jp_1577_;
}
else
{
lean_dec(v_a_1584_);
lean_dec_ref(v_a_1564_);
v___y_1578_ = v___x_1586_;
goto v___jp_1577_;
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec(v_n_1576_);
lean_dec_ref(v_a_1564_);
lean_dec_ref(v_xs_1562_);
v_a_1591_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1583_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1583_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
v___jp_1577_:
{
if (lean_obj_tag(v___y_1578_) == 0)
{
lean_object* v_a_1579_; 
v_a_1579_ = lean_ctor_get(v___y_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___y_1578_, 1);
v_i_1563_ = v_n_1576_;
v_a_1564_ = v_a_1579_;
goto _start;
}
else
{
lean_dec(v_n_1576_);
lean_dec_ref(v_xs_1562_);
return v___y_1578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg___boxed(lean_object* v_xs_1599_, lean_object* v_i_1600_, lean_object* v_a_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1599_, v_i_1600_, v_a_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS(lean_object* v_xs_1610_, lean_object* v_e_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_xs_1610_);
v___x_1620_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1611_, v___x_1619_, v_xs_1610_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v___x_1622_ = lean_array_get_size(v_xs_1610_);
v___x_1623_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1610_, v___x_1622_, v_a_1621_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
return v___x_1623_;
}
else
{
lean_dec_ref(v_xs_1610_);
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS___boxed(lean_object* v_xs_1624_, lean_object* v_e_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_1624_, v_e_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(lean_object* v_xs_1634_, lean_object* v_n_1635_, lean_object* v_i_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1634_, v_i_1636_, v_a_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___boxed(lean_object* v_xs_1647_, lean_object* v_n_1648_, lean_object* v_i_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(v_xs_1647_, v_n_1648_, v_i_1649_, v_a_1650_, v_a_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v_n_1648_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(lean_object* v_x_1660_, uint8_t v_bi_1661_, lean_object* v_t_1662_, lean_object* v_b_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v___y_1672_; lean_object* v___x_1675_; uint8_t v_debug_1676_; 
v___x_1675_ = lean_st_ref_get(v___y_1665_);
v_debug_1676_ = lean_ctor_get_uint8(v___x_1675_, sizeof(void*)*11);
lean_dec(v___x_1675_);
if (v_debug_1676_ == 0)
{
v___y_1672_ = v___y_1665_;
goto v___jp_1671_;
}
else
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1662_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v___x_1678_; 
lean_dec_ref_known(v___x_1677_, 1);
v___x_1678_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_dec_ref_known(v___x_1678_, 1);
v___y_1672_ = v___y_1665_;
goto v___jp_1671_;
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref(v_b_1663_);
lean_dec_ref(v_t_1662_);
lean_dec(v_x_1660_);
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec_ref(v_b_1663_);
lean_dec_ref(v_t_1662_);
lean_dec(v_x_1660_);
v_a_1687_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1677_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1677_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
v___jp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = l_Lean_Expr_forallE___override(v_x_1660_, v_t_1662_, v_b_1663_, v_bi_1661_);
v___x_1674_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1673_, v___y_1672_);
return v___x_1674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0___boxed(lean_object* v_x_1695_, lean_object* v_bi_1696_, lean_object* v_t_1697_, lean_object* v_b_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
uint8_t v_bi_boxed_1706_; lean_object* v_res_1707_; 
v_bi_boxed_1706_ = lean_unbox(v_bi_1696_);
v_res_1707_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v_x_1695_, v_bi_boxed_1706_, v_t_1697_, v_b_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(lean_object* v_xs_1708_, lean_object* v_i_1709_, lean_object* v_a_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_zero_1718_; uint8_t v_isZero_1719_; 
v_zero_1718_ = lean_unsigned_to_nat(0u);
v_isZero_1719_ = lean_nat_dec_eq(v_i_1709_, v_zero_1718_);
if (v_isZero_1719_ == 1)
{
lean_object* v___x_1720_; 
lean_dec(v_i_1709_);
lean_dec_ref(v_xs_1708_);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_a_1710_);
return v___x_1720_;
}
else
{
lean_object* v_one_1721_; lean_object* v_n_1722_; lean_object* v___y_1724_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v_one_1721_ = lean_unsigned_to_nat(1u);
v_n_1722_ = lean_nat_sub(v_i_1709_, v_one_1721_);
lean_dec(v_i_1709_);
v___x_1727_ = lean_array_fget_borrowed(v_xs_1708_, v_n_1722_);
v___x_1728_ = l_Lean_Expr_fvarId_x21(v___x_1727_);
v___x_1729_ = l_Lean_FVarId_getDecl___redArg(v___x_1728_, v___y_1713_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v___x_1731_ = l_Lean_LocalDecl_type(v_a_1730_);
lean_inc_ref(v_xs_1708_);
lean_inc(v_n_1722_);
v___x_1732_ = l_Lean_Meta_Sym_abstractFVarsRange(v___x_1731_, v_n_1722_, v_xs_1708_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1734_; uint8_t v___x_1735_; lean_object* v___x_1736_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1732_, 1);
v___x_1734_ = l_Lean_LocalDecl_userName(v_a_1730_);
v___x_1735_ = l_Lean_LocalDecl_binderInfo(v_a_1730_);
lean_dec(v_a_1730_);
v___x_1736_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v___x_1734_, v___x_1735_, v_a_1733_, v_a_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
v___y_1724_ = v___x_1736_;
goto v___jp_1723_;
}
else
{
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1710_);
v___y_1724_ = v___x_1732_;
goto v___jp_1723_;
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v_n_1722_);
lean_dec_ref(v_a_1710_);
lean_dec_ref(v_xs_1708_);
v_a_1737_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1729_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1729_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
v___jp_1723_:
{
if (lean_obj_tag(v___y_1724_) == 0)
{
lean_object* v_a_1725_; 
v_a_1725_ = lean_ctor_get(v___y_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___y_1724_, 1);
v_i_1709_ = v_n_1722_;
v_a_1710_ = v_a_1725_;
goto _start;
}
else
{
lean_dec(v_n_1722_);
lean_dec_ref(v_xs_1708_);
return v___y_1724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg___boxed(lean_object* v_xs_1745_, lean_object* v_i_1746_, lean_object* v_a_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1745_, v_i_1746_, v_a_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object* v_xs_1756_, lean_object* v_e_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_xs_1756_);
v___x_1766_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1757_, v___x_1765_, v_xs_1756_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = lean_array_get_size(v_xs_1756_);
v___x_1769_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1756_, v___x_1768_, v_a_1767_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_);
return v___x_1769_;
}
else
{
lean_dec_ref(v_xs_1756_);
return v___x_1766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS___boxed(lean_object* v_xs_1770_, lean_object* v_e_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lean_Meta_Sym_mkForallFVarsS(v_xs_1770_, v_e_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(lean_object* v_xs_1780_, lean_object* v_n_1781_, lean_object* v_i_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1780_, v_i_1782_, v_a_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___boxed(lean_object* v_xs_1793_, lean_object* v_n_1794_, lean_object* v_i_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(v_xs_1793_, v_n_1794_, v_i_1795_, v_a_1796_, v_a_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v_n_1794_);
return v_res_1805_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_AbstractS(builtin);
}
#ifdef __cplusplus
}
#endif
