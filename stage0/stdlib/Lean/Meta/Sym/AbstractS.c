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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
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
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_43_; lean_object* v___x_2596__overap_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_43_ = lean_nat_add(v_offset_19_, v_val_39_);
lean_dec(v_val_39_);
v___x_2596__overap_44_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v___x_13_, v___x_43_);
v___x_45_ = lean_box(v___y_20_);
lean_inc_ref(v___y_21_);
v___x_46_ = lean_apply_3(v___x_2596__overap_44_, v___x_45_, v___y_21_, v___y_22_);
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
uint8_t v___y_2691__boxed_105_; lean_object* v_res_106_; 
v___y_2691__boxed_105_ = lean_unbox(v___y_102_);
v_res_106_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(v_toDeBruijn_x3f_94_, v___x_95_, v_maxFVar_96_, v_minIndex_97_, v_lctx_98_, v___x_99_, v_e_100_, v_offset_101_, v___y_2691__boxed_105_, v___y_103_, v___y_104_);
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
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_box(0);
v___x_108_ = lean_unsigned_to_nat(16u);
v___x_109_ = lean_mk_array(v___x_108_, v___x_107_);
return v___x_109_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___x_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(lean_object* v_e_113_, lean_object* v_lctx_114_, lean_object* v_maxFVar_115_, lean_object* v_minFVarId_116_, lean_object* v_toDeBruijn_x3f_117_, uint8_t v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___y_124_; lean_object* v___x_225_; 
v___x_121_ = l_Lean_instInhabitedLocalDecl_default;
v___x_122_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
lean_inc_ref(v_lctx_114_);
v___x_225_ = lean_local_ctx_find(v_lctx_114_, v_minFVarId_116_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_227_ = l_panic___redArg(v___x_121_, v___x_226_);
v___y_124_ = v___x_227_;
goto v___jp_123_;
}
else
{
lean_object* v_val_228_; 
v_val_228_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_val_228_);
lean_dec_ref_known(v___x_225_, 1);
v___y_124_ = v_val_228_;
goto v___jp_123_;
}
v___jp_123_:
{
lean_object* v_minIndex_125_; lean_object* v___f_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_minIndex_125_ = l_Lean_LocalDecl_index(v___y_124_);
lean_dec_ref(v___y_124_);
lean_inc_ref(v_lctx_114_);
lean_inc(v_minIndex_125_);
lean_inc_ref(v_maxFVar_115_);
lean_inc_ref(v_toDeBruijn_x3f_117_);
v___f_126_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed), 11, 6);
lean_closure_set(v___f_126_, 0, v_toDeBruijn_x3f_117_);
lean_closure_set(v___f_126_, 1, v___x_122_);
lean_closure_set(v___f_126_, 2, v_maxFVar_115_);
lean_closure_set(v___f_126_, 3, v_minIndex_125_);
lean_closure_set(v___f_126_, 4, v_lctx_114_);
lean_closure_set(v___f_126_, 5, v___x_121_);
v___x_127_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_e_113_);
v___x_128_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(v_toDeBruijn_x3f_117_, v___x_122_, v_maxFVar_115_, v_minIndex_125_, v_lctx_114_, v___x_121_, v_e_113_, v___x_127_, v_a_118_, v_a_119_, v_a_120_);
lean_dec(v_minIndex_125_);
lean_dec_ref(v_maxFVar_115_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_a_129_);
if (lean_obj_tag(v_a_129_) == 1)
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_138_; 
lean_dec_ref(v___f_126_);
lean_dec_ref(v_e_113_);
v_a_130_ = lean_ctor_get(v___x_128_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_138_ == 0)
{
lean_object* v_unused_139_; 
v_unused_139_ = lean_ctor_get(v___x_128_, 0);
lean_dec(v_unused_139_);
v___x_132_ = v___x_128_;
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_128_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v_val_134_; lean_object* v___x_136_; 
v_val_134_ = lean_ctor_get(v_a_129_, 0);
lean_inc(v_val_134_);
lean_dec_ref_known(v_a_129_, 1);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v_val_134_);
v___x_136_ = v___x_132_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_val_134_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_a_130_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
else
{
lean_dec(v_a_129_);
switch(lean_obj_tag(v_e_113_))
{
case 9:
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
lean_dec_ref(v___f_126_);
v_a_140_ = lean_ctor_get(v___x_128_, 1);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; 
v_unused_148_ = lean_ctor_get(v___x_128_, 0);
lean_dec(v_unused_148_);
v___x_142_ = v___x_128_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_128_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v_e_113_);
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_e_113_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
case 2:
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
lean_dec_ref(v___f_126_);
v_a_149_ = lean_ctor_get(v___x_128_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_156_ == 0)
{
lean_object* v_unused_157_; 
v_unused_157_ = lean_ctor_get(v___x_128_, 0);
lean_dec(v_unused_157_);
v___x_151_ = v___x_128_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_128_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v_e_113_);
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_e_113_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
case 0:
{
lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
lean_dec_ref(v___f_126_);
v_a_158_ = lean_ctor_get(v___x_128_, 1);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_165_ == 0)
{
lean_object* v_unused_166_; 
v_unused_166_ = lean_ctor_get(v___x_128_, 0);
lean_dec(v_unused_166_);
v___x_160_ = v___x_128_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_128_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 0, v_e_113_);
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_e_113_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_a_158_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
case 1:
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
lean_dec_ref(v___f_126_);
v_a_167_ = lean_ctor_get(v___x_128_, 1);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; 
v_unused_175_ = lean_ctor_get(v___x_128_, 0);
lean_dec(v_unused_175_);
v___x_169_ = v___x_128_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_128_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v_e_113_);
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_e_113_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
case 4:
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
lean_dec_ref(v___f_126_);
v_a_176_ = lean_ctor_get(v___x_128_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v___x_128_, 0);
lean_dec(v_unused_184_);
v___x_178_ = v___x_128_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_128_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v_e_113_);
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_e_113_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
case 3:
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec_ref(v___f_126_);
v_a_185_ = lean_ctor_get(v___x_128_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_192_ == 0)
{
lean_object* v_unused_193_; 
v_unused_193_ = lean_ctor_get(v___x_128_, 0);
lean_dec(v_unused_193_);
v___x_187_ = v___x_128_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_128_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v_e_113_);
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_e_113_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
default: 
{
lean_object* v_a_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_a_194_ = lean_ctor_get(v___x_128_, 1);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_128_, 2);
v___x_195_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1);
v___x_196_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_113_, v___x_127_, v___f_126_, v___x_195_, v_a_118_, v_a_119_, v_a_194_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_206_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_a_198_ = lean_ctor_get(v___x_196_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_206_ == 0)
{
v___x_200_ = v___x_196_;
v_isShared_201_ = v_isSharedCheck_206_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_206_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v_fst_202_; lean_object* v___x_204_; 
v_fst_202_ = lean_ctor_get(v_a_197_, 0);
lean_inc(v_fst_202_);
lean_dec(v_a_197_);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v_fst_202_);
v___x_204_ = v___x_200_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_fst_202_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_a_198_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
else
{
lean_object* v_a_207_; lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
v_a_207_ = lean_ctor_get(v___x_196_, 0);
v_a_208_ = lean_ctor_get(v___x_196_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_196_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_inc(v_a_207_);
lean_dec(v___x_196_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_207_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_216_; lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_dec_ref(v___f_126_);
lean_dec_ref(v_e_113_);
v_a_216_ = lean_ctor_get(v___x_128_, 0);
v_a_217_ = lean_ctor_get(v___x_128_, 1);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_128_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_inc(v_a_216_);
lean_dec(v___x_128_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_216_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___boxed(lean_object* v_e_229_, lean_object* v_lctx_230_, lean_object* v_maxFVar_231_, lean_object* v_minFVarId_232_, lean_object* v_toDeBruijn_x3f_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
uint8_t v_a_boxed_237_; lean_object* v_res_238_; 
v_a_boxed_237_ = lean_unbox(v_a_234_);
v_res_238_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(v_e_229_, v_lctx_230_, v_maxFVar_231_, v_minFVarId_232_, v_toDeBruijn_x3f_233_, v_a_boxed_237_, v_a_235_, v_a_236_);
lean_dec_ref(v_a_235_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(lean_object* v_start_239_, lean_object* v_xs_240_, lean_object* v_fvarId_241_, lean_object* v_bidx_242_, lean_object* v_i_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_244_ = lean_array_fget_borrowed(v_xs_240_, v_i_243_);
v___x_245_ = l_Lean_Expr_fvarId_x21(v___x_244_);
v___x_246_ = l_Lean_instBEqFVarId_beq(v___x_245_, v_fvarId_241_);
lean_dec(v___x_245_);
if (v___x_246_ == 0)
{
uint8_t v___x_247_; 
v___x_247_ = lean_nat_dec_lt(v_start_239_, v_i_243_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
lean_dec(v_i_243_);
lean_dec(v_bidx_242_);
v___x_248_ = lean_box(0);
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = lean_nat_add(v_bidx_242_, v___x_249_);
lean_dec(v_bidx_242_);
v___x_251_ = lean_nat_sub(v_i_243_, v___x_249_);
lean_dec(v_i_243_);
v_bidx_242_ = v___x_250_;
v_i_243_ = v___x_251_;
goto _start;
}
}
else
{
lean_object* v___x_253_; 
lean_dec(v_i_243_);
v___x_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_253_, 0, v_bidx_242_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg___boxed(lean_object* v_start_254_, lean_object* v_xs_255_, lean_object* v_fvarId_256_, lean_object* v_bidx_257_, lean_object* v_i_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_254_, v_xs_255_, v_fvarId_256_, v_bidx_257_, v_i_258_);
lean_dec(v_fvarId_256_);
lean_dec_ref(v_xs_255_);
lean_dec(v_start_254_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(lean_object* v_start_260_, lean_object* v_xs_261_, lean_object* v_fvarId_262_, lean_object* v_bidx_263_, lean_object* v_i_264_, lean_object* v_h_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_260_, v_xs_261_, v_fvarId_262_, v_bidx_263_, v_i_264_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___boxed(lean_object* v_start_267_, lean_object* v_xs_268_, lean_object* v_fvarId_269_, lean_object* v_bidx_270_, lean_object* v_i_271_, lean_object* v_h_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(v_start_267_, v_xs_268_, v_fvarId_269_, v_bidx_270_, v_i_271_, v_h_272_);
lean_dec(v_fvarId_269_);
lean_dec_ref(v_xs_268_);
lean_dec(v_start_267_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(lean_object* v_msg_274_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = l_Lean_instInhabitedLocalDecl_default;
v___x_276_ = lean_panic_fn_borrowed(v___x_275_, v_msg_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(lean_object* v_idx_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = l_Lean_Expr_bvar___override(v_idx_277_);
v___x_280_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_279_, v___y_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(lean_object* v_idx_281_, uint8_t v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v_idx_281_, v___y_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___boxed(lean_object* v_idx_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
uint8_t v___y_25775__boxed_290_; lean_object* v_res_291_; 
v___y_25775__boxed_290_ = lean_unbox(v___y_287_);
v_res_291_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v_idx_286_, v___y_25775__boxed_290_, v___y_288_, v___y_289_);
lean_dec_ref(v___y_288_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(lean_object* v_msg_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_box(0);
v___x_294_ = lean_panic_fn_borrowed(v___x_293_, v_msg_292_);
return v___x_294_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0(void){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(lean_object* v_msg_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_2646__overap_305_; lean_object* v___x_306_; 
v___x_304_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0, &l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0);
v___x_2646__overap_305_ = lean_panic_fn_borrowed(v___x_304_, v_msg_296_);
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
lean_inc(v___y_300_);
lean_inc_ref(v___y_299_);
lean_inc(v___y_298_);
lean_inc_ref(v___y_297_);
v___x_306_ = lean_apply_7(v___x_2646__overap_305_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, lean_box(0));
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___boxed(lean_object* v_msg_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v_msg_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(lean_object* v_msg_323_, lean_object* v___y_324_, uint8_t v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___f_328_; lean_object* v___f_329_; lean_object* v___f_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___f_340_; lean_object* v___f_341_; lean_object* v___f_342_; lean_object* v___f_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_25272__overap_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___f_328_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__0));
v___f_329_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__1));
v___f_330_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__2));
v___x_331_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__3));
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___f_328_);
v___x_333_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__4));
v___x_334_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__5));
v___x_335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_335_, 0, v___x_332_);
lean_ctor_set(v___x_335_, 1, v___x_333_);
lean_ctor_set(v___x_335_, 2, v___f_329_);
lean_ctor_set(v___x_335_, 3, v___f_330_);
lean_ctor_set(v___x_335_, 4, v___x_334_);
v___x_336_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__6));
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_335_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = l_ReaderT_instMonad___redArg(v___x_337_);
v___x_339_ = l_ReaderT_instMonad___redArg(v___x_338_);
lean_inc_ref_n(v___x_339_, 6);
v___f_340_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_340_, 0, v___x_339_);
v___f_341_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_341_, 0, v___x_339_);
v___f_342_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_342_, 0, v___x_339_);
v___f_343_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_343_, 0, v___x_339_);
v___x_344_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_344_, 0, lean_box(0));
lean_closure_set(v___x_344_, 1, lean_box(0));
lean_closure_set(v___x_344_, 2, v___x_339_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___f_340_);
v___x_346_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_346_, 0, lean_box(0));
lean_closure_set(v___x_346_, 1, lean_box(0));
lean_closure_set(v___x_346_, 2, v___x_339_);
v___x_347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_347_, 0, v___x_345_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
lean_ctor_set(v___x_347_, 2, v___f_341_);
lean_ctor_set(v___x_347_, 3, v___f_342_);
lean_ctor_set(v___x_347_, 4, v___f_343_);
v___x_348_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_348_, 0, lean_box(0));
lean_closure_set(v___x_348_, 1, lean_box(0));
lean_closure_set(v___x_348_, 2, v___x_339_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_347_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = l_Lean_instInhabitedExpr;
v___x_351_ = l_instInhabitedOfMonad___redArg(v___x_349_, v___x_350_);
v___x_25272__overap_352_ = lean_panic_fn_borrowed(v___x_351_, v_msg_323_);
lean_dec(v___x_351_);
v___x_353_ = lean_box(v___y_325_);
lean_inc_ref(v___y_326_);
v___x_354_ = lean_apply_4(v___x_25272__overap_352_, v___y_324_, v___x_353_, v___y_326_, v___y_327_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___boxed(lean_object* v_msg_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
uint8_t v___y_25833__boxed_360_; lean_object* v_res_361_; 
v___y_25833__boxed_360_ = lean_unbox(v___y_357_);
v_res_361_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(v_msg_355_, v___y_356_, v___y_25833__boxed_360_, v___y_358_, v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(lean_object* v_structName_362_, lean_object* v_idx_363_, lean_object* v_struct_364_, lean_object* v___y_365_, uint8_t v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v___y_370_; lean_object* v___y_371_; 
if (v___y_366_ == 0)
{
v___y_370_ = v___y_365_;
v___y_371_ = v___y_368_;
goto v___jp_369_;
}
else
{
lean_object* v___x_393_; 
lean_inc_ref(v_struct_364_);
v___x_393_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_364_, v___y_366_, v___y_367_, v___y_368_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; 
v_a_394_ = lean_ctor_get(v___x_393_, 1);
lean_inc(v_a_394_);
lean_dec_ref_known(v___x_393_, 2);
v___y_370_ = v___y_365_;
v___y_371_ = v_a_394_;
goto v___jp_369_;
}
else
{
lean_object* v_a_395_; lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec_ref(v___y_365_);
lean_dec_ref(v_struct_364_);
lean_dec(v_idx_363_);
lean_dec(v_structName_362_);
v_a_395_ = lean_ctor_get(v___x_393_, 0);
v_a_396_ = lean_ctor_get(v___x_393_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_393_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_inc(v_a_395_);
lean_dec(v___x_393_);
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
v___jp_369_:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = l_Lean_Expr_proj___override(v_structName_362_, v_idx_363_, v_struct_364_);
v___x_373_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_372_, v___y_371_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_383_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_a_375_ = lean_ctor_get(v___x_373_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_383_ == 0)
{
v___x_377_ = v___x_373_;
v_isShared_378_ = v_isSharedCheck_383_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_383_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v_a_374_);
lean_ctor_set(v___x_379_, 1, v___y_370_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_379_);
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_a_375_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
else
{
lean_object* v_a_384_; lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec_ref(v___y_370_);
v_a_384_ = lean_ctor_get(v___x_373_, 0);
v_a_385_ = lean_ctor_get(v___x_373_, 1);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_373_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_inc(v_a_384_);
lean_dec(v___x_373_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_384_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11___boxed(lean_object* v_structName_404_, lean_object* v_idx_405_, lean_object* v_struct_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
uint8_t v___y_25904__boxed_411_; lean_object* v_res_412_; 
v___y_25904__boxed_411_ = lean_unbox(v___y_408_);
v_res_412_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(v_structName_404_, v_idx_405_, v_struct_406_, v___y_407_, v___y_25904__boxed_411_, v___y_409_, v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(lean_object* v_d_413_, lean_object* v_e_414_, lean_object* v___y_415_, uint8_t v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___y_420_; lean_object* v___y_421_; 
if (v___y_416_ == 0)
{
v___y_420_ = v___y_415_;
v___y_421_ = v___y_418_;
goto v___jp_419_;
}
else
{
lean_object* v___x_443_; 
lean_inc_ref(v_e_414_);
v___x_443_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_414_, v___y_416_, v___y_417_, v___y_418_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; 
v_a_444_ = lean_ctor_get(v___x_443_, 1);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 2);
v___y_420_ = v___y_415_;
v___y_421_ = v_a_444_;
goto v___jp_419_;
}
else
{
lean_object* v_a_445_; lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec_ref(v___y_415_);
lean_dec_ref(v_e_414_);
lean_dec(v_d_413_);
v_a_445_ = lean_ctor_get(v___x_443_, 0);
v_a_446_ = lean_ctor_get(v___x_443_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_443_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_inc(v_a_445_);
lean_dec(v___x_443_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_445_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
v___jp_419_:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = l_Lean_Expr_mdata___override(v_d_413_, v_e_414_);
v___x_423_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_422_, v___y_421_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_433_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_a_425_ = lean_ctor_get(v___x_423_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_433_ == 0)
{
v___x_427_ = v___x_423_;
v_isShared_428_ = v_isSharedCheck_433_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_433_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_a_424_);
lean_ctor_set(v___x_429_, 1, v___y_420_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_429_);
v___x_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_a_425_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
else
{
lean_object* v_a_434_; lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
lean_dec_ref(v___y_420_);
v_a_434_ = lean_ctor_get(v___x_423_, 0);
v_a_435_ = lean_ctor_get(v___x_423_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_423_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_inc(v_a_434_);
lean_dec(v___x_423_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_434_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10___boxed(lean_object* v_d_454_, lean_object* v_e_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
uint8_t v___y_25987__boxed_460_; lean_object* v_res_461_; 
v___y_25987__boxed_460_ = lean_unbox(v___y_457_);
v_res_461_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(v_d_454_, v_e_455_, v___y_456_, v___y_25987__boxed_460_, v___y_458_, v___y_459_);
lean_dec_ref(v___y_458_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(lean_object* v_keys_462_, lean_object* v_vals_463_, lean_object* v_i_464_, lean_object* v_k_465_){
_start:
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_array_get_size(v_keys_462_);
v___x_467_ = lean_nat_dec_lt(v_i_464_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
lean_dec(v_i_464_);
v___x_468_ = lean_box(0);
return v___x_468_;
}
else
{
lean_object* v_k_x27_469_; size_t v___x_470_; size_t v___x_471_; uint8_t v___x_472_; 
v_k_x27_469_ = lean_array_fget_borrowed(v_keys_462_, v_i_464_);
v___x_470_ = lean_ptr_addr(v_k_465_);
v___x_471_ = lean_ptr_addr(v_k_x27_469_);
v___x_472_ = lean_usize_dec_eq(v___x_470_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_unsigned_to_nat(1u);
v___x_474_ = lean_nat_add(v_i_464_, v___x_473_);
lean_dec(v_i_464_);
v_i_464_ = v___x_474_;
goto _start;
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_array_fget_borrowed(v_vals_463_, v_i_464_);
lean_dec(v_i_464_);
lean_inc(v___x_476_);
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_keys_478_, lean_object* v_vals_479_, lean_object* v_i_480_, lean_object* v_k_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_keys_478_, v_vals_479_, v_i_480_, v_k_481_);
lean_dec_ref(v_k_481_);
lean_dec_ref(v_vals_479_);
lean_dec_ref(v_keys_478_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(lean_object* v_x_483_, size_t v_x_484_, lean_object* v_x_485_){
_start:
{
if (lean_obj_tag(v_x_483_) == 0)
{
lean_object* v_es_486_; lean_object* v___x_487_; size_t v___x_488_; size_t v___x_489_; lean_object* v_j_490_; lean_object* v___x_491_; 
v_es_486_ = lean_ctor_get(v_x_483_, 0);
v___x_487_ = lean_box(2);
v___x_488_ = ((size_t)31ULL);
v___x_489_ = lean_usize_land(v_x_484_, v___x_488_);
v_j_490_ = lean_usize_to_nat(v___x_489_);
v___x_491_ = lean_array_get_borrowed(v___x_487_, v_es_486_, v_j_490_);
lean_dec(v_j_490_);
switch(lean_obj_tag(v___x_491_))
{
case 0:
{
lean_object* v_key_492_; lean_object* v_val_493_; size_t v___x_494_; size_t v___x_495_; uint8_t v___x_496_; 
v_key_492_ = lean_ctor_get(v___x_491_, 0);
v_val_493_ = lean_ctor_get(v___x_491_, 1);
v___x_494_ = lean_ptr_addr(v_x_485_);
v___x_495_ = lean_ptr_addr(v_key_492_);
v___x_496_ = lean_usize_dec_eq(v___x_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
v___x_497_ = lean_box(0);
return v___x_497_;
}
else
{
lean_object* v___x_498_; 
lean_inc(v_val_493_);
v___x_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_498_, 0, v_val_493_);
return v___x_498_;
}
}
case 1:
{
lean_object* v_node_499_; size_t v___x_500_; size_t v___x_501_; 
v_node_499_ = lean_ctor_get(v___x_491_, 0);
v___x_500_ = ((size_t)5ULL);
v___x_501_ = lean_usize_shift_right(v_x_484_, v___x_500_);
v_x_483_ = v_node_499_;
v_x_484_ = v___x_501_;
goto _start;
}
default: 
{
lean_object* v___x_503_; 
v___x_503_ = lean_box(0);
return v___x_503_;
}
}
}
else
{
lean_object* v_ks_504_; lean_object* v_vs_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_ks_504_ = lean_ctor_get(v_x_483_, 0);
v_vs_505_ = lean_ctor_get(v_x_483_, 1);
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_ks_504_, v_vs_505_, v___x_506_, v_x_485_);
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg___boxed(lean_object* v_x_508_, lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
size_t v_x_26092__boxed_511_; lean_object* v_res_512_; 
v_x_26092__boxed_511_ = lean_unbox_usize(v_x_509_);
lean_dec(v_x_509_);
v_res_512_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_508_, v_x_26092__boxed_511_, v_x_510_);
lean_dec_ref(v_x_510_);
lean_dec_ref(v_x_508_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(lean_object* v_x_513_, lean_object* v_x_514_){
_start:
{
size_t v___x_515_; size_t v___x_516_; size_t v___x_517_; uint64_t v___x_518_; size_t v___x_519_; lean_object* v___x_520_; 
v___x_515_ = lean_ptr_addr(v_x_514_);
v___x_516_ = ((size_t)3ULL);
v___x_517_ = lean_usize_shift_right(v___x_515_, v___x_516_);
v___x_518_ = lean_usize_to_uint64(v___x_517_);
v___x_519_ = lean_uint64_to_usize(v___x_518_);
v___x_520_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_513_, v___x_519_, v_x_514_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg___boxed(lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_x_521_, v_x_522_);
lean_dec_ref(v_x_522_);
lean_dec_ref(v_x_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(lean_object* v_a_524_, lean_object* v_x_525_){
_start:
{
if (lean_obj_tag(v_x_525_) == 0)
{
lean_object* v___x_526_; 
v___x_526_ = lean_box(0);
return v___x_526_;
}
else
{
lean_object* v_key_527_; lean_object* v_value_528_; lean_object* v_tail_529_; uint8_t v___y_531_; lean_object* v_fst_534_; lean_object* v_snd_535_; lean_object* v_fst_536_; lean_object* v_snd_537_; size_t v___x_538_; size_t v___x_539_; uint8_t v___x_540_; 
v_key_527_ = lean_ctor_get(v_x_525_, 0);
v_value_528_ = lean_ctor_get(v_x_525_, 1);
v_tail_529_ = lean_ctor_get(v_x_525_, 2);
v_fst_534_ = lean_ctor_get(v_key_527_, 0);
v_snd_535_ = lean_ctor_get(v_key_527_, 1);
v_fst_536_ = lean_ctor_get(v_a_524_, 0);
v_snd_537_ = lean_ctor_get(v_a_524_, 1);
v___x_538_ = lean_ptr_addr(v_fst_534_);
v___x_539_ = lean_ptr_addr(v_fst_536_);
v___x_540_ = lean_usize_dec_eq(v___x_538_, v___x_539_);
if (v___x_540_ == 0)
{
v___y_531_ = v___x_540_;
goto v___jp_530_;
}
else
{
uint8_t v___x_541_; 
v___x_541_ = lean_nat_dec_eq(v_snd_535_, v_snd_537_);
v___y_531_ = v___x_541_;
goto v___jp_530_;
}
v___jp_530_:
{
if (v___y_531_ == 0)
{
v_x_525_ = v_tail_529_;
goto _start;
}
else
{
lean_object* v___x_533_; 
lean_inc(v_value_528_);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v_value_528_);
return v___x_533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg___boxed(lean_object* v_a_542_, lean_object* v_x_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_a_542_, v_x_543_);
lean_dec(v_x_543_);
lean_dec_ref(v_a_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(lean_object* v_m_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_buckets_547_; lean_object* v_fst_548_; lean_object* v_snd_549_; lean_object* v___x_550_; size_t v___x_551_; size_t v___x_552_; size_t v___x_553_; uint64_t v___x_554_; uint64_t v___x_555_; uint64_t v___x_556_; uint64_t v___x_557_; uint64_t v___x_558_; uint64_t v_fold_559_; uint64_t v___x_560_; uint64_t v___x_561_; uint64_t v___x_562_; size_t v___x_563_; size_t v___x_564_; size_t v___x_565_; size_t v___x_566_; size_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_buckets_547_ = lean_ctor_get(v_m_545_, 1);
v_fst_548_ = lean_ctor_get(v_a_546_, 0);
v_snd_549_ = lean_ctor_get(v_a_546_, 1);
v___x_550_ = lean_array_get_size(v_buckets_547_);
v___x_551_ = lean_ptr_addr(v_fst_548_);
v___x_552_ = ((size_t)3ULL);
v___x_553_ = lean_usize_shift_right(v___x_551_, v___x_552_);
v___x_554_ = lean_usize_to_uint64(v___x_553_);
v___x_555_ = lean_uint64_of_nat(v_snd_549_);
v___x_556_ = lean_uint64_mix_hash(v___x_554_, v___x_555_);
v___x_557_ = 32ULL;
v___x_558_ = lean_uint64_shift_right(v___x_556_, v___x_557_);
v_fold_559_ = lean_uint64_xor(v___x_556_, v___x_558_);
v___x_560_ = 16ULL;
v___x_561_ = lean_uint64_shift_right(v_fold_559_, v___x_560_);
v___x_562_ = lean_uint64_xor(v_fold_559_, v___x_561_);
v___x_563_ = lean_uint64_to_usize(v___x_562_);
v___x_564_ = lean_usize_of_nat(v___x_550_);
v___x_565_ = ((size_t)1ULL);
v___x_566_ = lean_usize_sub(v___x_564_, v___x_565_);
v___x_567_ = lean_usize_land(v___x_563_, v___x_566_);
v___x_568_ = lean_array_uget_borrowed(v_buckets_547_, v___x_567_);
v___x_569_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_a_546_, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_m_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_m_570_, v_a_571_);
lean_dec_ref(v_a_571_);
lean_dec_ref(v_m_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(lean_object* v_x_573_, uint8_t v_bi_574_, lean_object* v_t_575_, lean_object* v_b_576_, lean_object* v___y_577_, uint8_t v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___y_582_; lean_object* v___y_583_; 
if (v___y_578_ == 0)
{
v___y_582_ = v___y_577_;
v___y_583_ = v___y_580_;
goto v___jp_581_;
}
else
{
lean_object* v___x_605_; 
lean_inc_ref(v_t_575_);
v___x_605_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_575_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_607_; 
v_a_606_ = lean_ctor_get(v___x_605_, 1);
lean_inc(v_a_606_);
lean_dec_ref_known(v___x_605_, 2);
lean_inc_ref(v_b_576_);
v___x_607_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_576_, v___y_578_, v___y_579_, v_a_606_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; 
v_a_608_ = lean_ctor_get(v___x_607_, 1);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 2);
v___y_582_ = v___y_577_;
v___y_583_ = v_a_608_;
goto v___jp_581_;
}
else
{
lean_object* v_a_609_; lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v___y_577_);
lean_dec_ref(v_b_576_);
lean_dec_ref(v_t_575_);
lean_dec(v_x_573_);
v_a_609_ = lean_ctor_get(v___x_607_, 0);
v_a_610_ = lean_ctor_get(v___x_607_, 1);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_607_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_inc(v_a_609_);
lean_dec(v___x_607_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
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
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_609_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_object* v_a_618_; lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec_ref(v___y_577_);
lean_dec_ref(v_b_576_);
lean_dec_ref(v_t_575_);
lean_dec(v_x_573_);
v_a_618_ = lean_ctor_get(v___x_605_, 0);
v_a_619_ = lean_ctor_get(v___x_605_, 1);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_605_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_inc(v_a_618_);
lean_dec(v___x_605_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_618_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
v___jp_581_:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = l_Lean_Expr_forallE___override(v_x_573_, v_t_575_, v_b_576_, v_bi_574_);
v___x_585_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_584_, v___y_583_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_595_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_a_587_ = lean_ctor_get(v___x_585_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_595_ == 0)
{
v___x_589_ = v___x_585_;
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v_a_586_);
lean_ctor_set(v___x_591_, 1, v___y_582_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_591_);
v___x_593_ = v___x_589_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_a_587_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
lean_object* v_a_596_; lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec_ref(v___y_582_);
v_a_596_ = lean_ctor_get(v___x_585_, 0);
v_a_597_ = lean_ctor_get(v___x_585_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_585_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_inc(v_a_596_);
lean_dec(v___x_585_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_596_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8___boxed(lean_object* v_x_627_, lean_object* v_bi_628_, lean_object* v_t_629_, lean_object* v_b_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
uint8_t v_bi_boxed_635_; uint8_t v___y_26240__boxed_636_; lean_object* v_res_637_; 
v_bi_boxed_635_ = lean_unbox(v_bi_628_);
v___y_26240__boxed_636_ = lean_unbox(v___y_632_);
v_res_637_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_x_627_, v_bi_boxed_635_, v_t_629_, v_b_630_, v___y_631_, v___y_26240__boxed_636_, v___y_633_, v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(lean_object* v_x_638_, uint8_t v_bi_639_, lean_object* v_t_640_, lean_object* v_b_641_, lean_object* v___y_642_, uint8_t v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___y_647_; lean_object* v___y_648_; 
if (v___y_643_ == 0)
{
v___y_647_ = v___y_642_;
v___y_648_ = v___y_645_;
goto v___jp_646_;
}
else
{
lean_object* v___x_670_; 
lean_inc_ref(v_t_640_);
v___x_670_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_640_, v___y_643_, v___y_644_, v___y_645_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_672_; 
v_a_671_ = lean_ctor_get(v___x_670_, 1);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 2);
lean_inc_ref(v_b_641_);
v___x_672_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_641_, v___y_643_, v___y_644_, v_a_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; 
v_a_673_ = lean_ctor_get(v___x_672_, 1);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 2);
v___y_647_ = v___y_642_;
v___y_648_ = v_a_673_;
goto v___jp_646_;
}
else
{
lean_object* v_a_674_; lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec_ref(v___y_642_);
lean_dec_ref(v_b_641_);
lean_dec_ref(v_t_640_);
lean_dec(v_x_638_);
v_a_674_ = lean_ctor_get(v___x_672_, 0);
v_a_675_ = lean_ctor_get(v___x_672_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_672_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_inc(v_a_674_);
lean_dec(v___x_672_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_674_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_object* v_a_683_; lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec_ref(v___y_642_);
lean_dec_ref(v_b_641_);
lean_dec_ref(v_t_640_);
lean_dec(v_x_638_);
v_a_683_ = lean_ctor_get(v___x_670_, 0);
v_a_684_ = lean_ctor_get(v___x_670_, 1);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_670_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_inc(v_a_683_);
lean_dec(v___x_670_);
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
v___jp_646_:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = l_Lean_Expr_lam___override(v_x_638_, v_t_640_, v_b_641_, v_bi_639_);
v___x_650_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_649_, v___y_648_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_a_652_ = lean_ctor_get(v___x_650_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_660_ == 0)
{
v___x_654_ = v___x_650_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v_a_651_);
lean_ctor_set(v___x_656_, 1, v___y_647_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_a_652_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
else
{
lean_object* v_a_661_; lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref(v___y_647_);
v_a_661_ = lean_ctor_get(v___x_650_, 0);
v_a_662_ = lean_ctor_get(v___x_650_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_650_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_inc(v_a_661_);
lean_dec(v___x_650_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_661_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7___boxed(lean_object* v_x_692_, lean_object* v_bi_693_, lean_object* v_t_694_, lean_object* v_b_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
uint8_t v_bi_boxed_700_; uint8_t v___y_26346__boxed_701_; lean_object* v_res_702_; 
v_bi_boxed_700_ = lean_unbox(v_bi_693_);
v___y_26346__boxed_701_ = lean_unbox(v___y_697_);
v_res_702_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_x_692_, v_bi_boxed_700_, v_t_694_, v_b_695_, v___y_696_, v___y_26346__boxed_701_, v___y_698_, v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(lean_object* v_x_703_, lean_object* v_t_704_, lean_object* v_v_705_, lean_object* v_b_706_, uint8_t v_nondep_707_, lean_object* v___y_708_, uint8_t v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___y_713_; lean_object* v___y_714_; 
if (v___y_709_ == 0)
{
v___y_713_ = v___y_708_;
v___y_714_ = v___y_711_;
goto v___jp_712_;
}
else
{
lean_object* v___x_736_; 
lean_inc_ref(v_t_704_);
v___x_736_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_704_, v___y_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; 
v_a_737_ = lean_ctor_get(v___x_736_, 1);
lean_inc(v_a_737_);
lean_dec_ref_known(v___x_736_, 2);
lean_inc_ref(v_v_705_);
v___x_738_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_705_, v___y_709_, v___y_710_, v_a_737_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 1);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 2);
lean_inc_ref(v_b_706_);
v___x_740_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_706_, v___y_709_, v___y_710_, v_a_739_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; 
v_a_741_ = lean_ctor_get(v___x_740_, 1);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 2);
v___y_713_ = v___y_708_;
v___y_714_ = v_a_741_;
goto v___jp_712_;
}
else
{
lean_object* v_a_742_; lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec_ref(v___y_708_);
lean_dec_ref(v_b_706_);
lean_dec_ref(v_v_705_);
lean_dec_ref(v_t_704_);
lean_dec(v_x_703_);
v_a_742_ = lean_ctor_get(v___x_740_, 0);
v_a_743_ = lean_ctor_get(v___x_740_, 1);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_740_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_inc(v_a_742_);
lean_dec(v___x_740_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_742_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec_ref(v___y_708_);
lean_dec_ref(v_b_706_);
lean_dec_ref(v_v_705_);
lean_dec_ref(v_t_704_);
lean_dec(v_x_703_);
v_a_751_ = lean_ctor_get(v___x_738_, 0);
v_a_752_ = lean_ctor_get(v___x_738_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_738_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_inc(v_a_751_);
lean_dec(v___x_738_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_751_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v___y_708_);
lean_dec_ref(v_b_706_);
lean_dec_ref(v_v_705_);
lean_dec_ref(v_t_704_);
lean_dec(v_x_703_);
v_a_760_ = lean_ctor_get(v___x_736_, 0);
v_a_761_ = lean_ctor_get(v___x_736_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_736_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_inc(v_a_760_);
lean_dec(v___x_736_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_760_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
v___jp_712_:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = l_Lean_Expr_letE___override(v_x_703_, v_t_704_, v_v_705_, v_b_706_, v_nondep_707_);
v___x_716_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_715_, v___y_714_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_726_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_a_718_ = lean_ctor_get(v___x_716_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_726_ == 0)
{
v___x_720_ = v___x_716_;
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v_a_717_);
lean_ctor_set(v___x_722_, 1, v___y_713_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_722_);
v___x_724_ = v___x_720_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_a_718_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v_a_727_; lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec_ref(v___y_713_);
v_a_727_ = lean_ctor_get(v___x_716_, 0);
v_a_728_ = lean_ctor_get(v___x_716_, 1);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_716_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_inc(v_a_727_);
lean_dec(v___x_716_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_727_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9___boxed(lean_object* v_x_769_, lean_object* v_t_770_, lean_object* v_v_771_, lean_object* v_b_772_, lean_object* v_nondep_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
uint8_t v_nondep_boxed_778_; uint8_t v___y_26452__boxed_779_; lean_object* v_res_780_; 
v_nondep_boxed_778_ = lean_unbox(v_nondep_773_);
v___y_26452__boxed_779_ = lean_unbox(v___y_775_);
v_res_780_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_x_769_, v_t_770_, v_v_771_, v_b_772_, v_nondep_boxed_778_, v___y_774_, v___y_26452__boxed_779_, v___y_776_, v___y_777_);
lean_dec_ref(v___y_776_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(lean_object* v_f_781_, lean_object* v_a_782_, lean_object* v___y_783_, uint8_t v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___y_788_; lean_object* v___y_789_; 
if (v___y_784_ == 0)
{
v___y_788_ = v___y_783_;
v___y_789_ = v___y_786_;
goto v___jp_787_;
}
else
{
lean_object* v___x_811_; 
lean_inc_ref(v_f_781_);
v___x_811_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_781_, v___y_784_, v___y_785_, v___y_786_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; 
v_a_812_ = lean_ctor_get(v___x_811_, 1);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_811_, 2);
lean_inc_ref(v_a_782_);
v___x_813_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_782_, v___y_784_, v___y_785_, v_a_812_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; 
v_a_814_ = lean_ctor_get(v___x_813_, 1);
lean_inc(v_a_814_);
lean_dec_ref_known(v___x_813_, 2);
v___y_788_ = v___y_783_;
v___y_789_ = v_a_814_;
goto v___jp_787_;
}
else
{
lean_object* v_a_815_; lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec_ref(v___y_783_);
lean_dec_ref(v_a_782_);
lean_dec_ref(v_f_781_);
v_a_815_ = lean_ctor_get(v___x_813_, 0);
v_a_816_ = lean_ctor_get(v___x_813_, 1);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_813_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_inc(v_a_815_);
lean_dec(v___x_813_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_815_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref(v___y_783_);
lean_dec_ref(v_a_782_);
lean_dec_ref(v_f_781_);
v_a_824_ = lean_ctor_get(v___x_811_, 0);
v_a_825_ = lean_ctor_get(v___x_811_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_811_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_inc(v_a_824_);
lean_dec(v___x_811_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_824_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
v___jp_787_:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = l_Lean_Expr_app___override(v_f_781_, v_a_782_);
v___x_791_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_790_, v___y_789_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_a_793_ = lean_ctor_get(v___x_791_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_801_ == 0)
{
v___x_795_ = v___x_791_;
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_a_792_);
lean_ctor_set(v___x_797_, 1, v___y_788_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_a_793_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
else
{
lean_object* v_a_802_; lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec_ref(v___y_788_);
v_a_802_ = lean_ctor_get(v___x_791_, 0);
v_a_803_ = lean_ctor_get(v___x_791_, 1);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_791_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_inc(v_a_802_);
lean_dec(v___x_791_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_802_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6___boxed(lean_object* v_f_833_, lean_object* v_a_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
uint8_t v___y_26581__boxed_839_; lean_object* v_res_840_; 
v___y_26581__boxed_839_ = lean_unbox(v___y_836_);
v_res_840_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_f_833_, v_a_834_, v___y_835_, v___y_26581__boxed_839_, v___y_837_, v___y_838_);
lean_dec_ref(v___y_837_);
return v_res_840_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_844_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__2));
v___x_845_ = lean_unsigned_to_nat(67u);
v___x_846_ = lean_unsigned_to_nat(35u);
v___x_847_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__1));
v___x_848_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__0));
v___x_849_ = l_mkPanicMessageWithDecl(v___x_848_, v___x_847_, v___x_846_, v___x_845_, v___x_844_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(lean_object* v_minIndex_850_, lean_object* v___x_851_, lean_object* v___x_852_, lean_object* v_start_853_, lean_object* v_xs_854_, lean_object* v___x_855_, lean_object* v_e_856_, lean_object* v_offset_857_, lean_object* v_a_858_, uint8_t v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
switch(lean_obj_tag(v_e_856_))
{
case 5:
{
lean_object* v_fn_862_; lean_object* v_arg_863_; lean_object* v___x_864_; 
v_fn_862_ = lean_ctor_get(v_e_856_, 0);
v_arg_863_ = lean_ctor_get(v_e_856_, 1);
lean_inc(v_offset_857_);
lean_inc_ref(v_fn_862_);
lean_inc_ref(v___x_851_);
v___x_864_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_850_, v___x_851_, v___x_852_, v_start_853_, v_xs_854_, v___x_855_, v_fn_862_, v_offset_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v_a_866_; lean_object* v_fst_867_; lean_object* v_snd_868_; lean_object* v___x_869_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
v_a_866_ = lean_ctor_get(v___x_864_, 1);
lean_inc(v_a_866_);
lean_dec_ref_known(v___x_864_, 2);
v_fst_867_ = lean_ctor_get(v_a_865_, 0);
lean_inc(v_fst_867_);
v_snd_868_ = lean_ctor_get(v_a_865_, 1);
lean_inc(v_snd_868_);
lean_dec(v_a_865_);
lean_inc_ref(v_arg_863_);
v___x_869_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_850_, v___x_851_, v___x_852_, v_start_853_, v_xs_854_, v___x_855_, v_arg_863_, v_offset_857_, v_snd_868_, v_a_859_, v_a_860_, v_a_866_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_896_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_a_871_ = lean_ctor_get(v___x_869_, 1);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_896_ == 0)
{
v___x_873_ = v___x_869_;
v_isShared_874_ = v_isSharedCheck_896_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_896_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v_fst_875_; lean_object* v_snd_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_895_; 
v_fst_875_ = lean_ctor_get(v_a_870_, 0);
v_snd_876_ = lean_ctor_get(v_a_870_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v_a_870_);
if (v_isSharedCheck_895_ == 0)
{
v___x_878_ = v_a_870_;
v_isShared_879_ = v_isSharedCheck_895_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_snd_876_);
lean_inc(v_fst_875_);
lean_dec(v_a_870_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_895_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
uint8_t v___y_881_; size_t v___x_889_; size_t v___x_890_; uint8_t v___x_891_; 
v___x_889_ = lean_ptr_addr(v_fn_862_);
v___x_890_ = lean_ptr_addr(v_fst_867_);
v___x_891_ = lean_usize_dec_eq(v___x_889_, v___x_890_);
if (v___x_891_ == 0)
{
v___y_881_ = v___x_891_;
goto v___jp_880_;
}
else
{
size_t v___x_892_; size_t v___x_893_; uint8_t v___x_894_; 
v___x_892_ = lean_ptr_addr(v_arg_863_);
v___x_893_ = lean_ptr_addr(v_fst_875_);
v___x_894_ = lean_usize_dec_eq(v___x_892_, v___x_893_);
v___y_881_ = v___x_894_;
goto v___jp_880_;
}
v___jp_880_:
{
if (v___y_881_ == 0)
{
lean_object* v___x_882_; 
lean_del_object(v___x_878_);
lean_del_object(v___x_873_);
lean_dec_ref_known(v_e_856_, 2);
v___x_882_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_fst_867_, v_fst_875_, v_snd_876_, v_a_859_, v_a_860_, v_a_871_);
return v___x_882_;
}
else
{
lean_object* v___x_884_; 
lean_dec(v_fst_875_);
lean_dec(v_fst_867_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v_e_856_);
v___x_884_ = v___x_878_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_e_856_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_snd_876_);
v___x_884_ = v_reuseFailAlloc_888_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_884_);
v___x_886_ = v___x_873_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_a_871_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_867_);
lean_dec_ref_known(v_e_856_, 2);
return v___x_869_;
}
}
else
{
lean_dec_ref_known(v_e_856_, 2);
lean_dec(v_offset_857_);
lean_dec_ref(v___x_851_);
return v___x_864_;
}
}
case 6:
{
lean_object* v_binderName_897_; lean_object* v_binderType_898_; lean_object* v_body_899_; uint8_t v_binderInfo_900_; lean_object* v___x_901_; 
v_binderName_897_ = lean_ctor_get(v_e_856_, 0);
v_binderType_898_ = lean_ctor_get(v_e_856_, 1);
v_body_899_ = lean_ctor_get(v_e_856_, 2);
v_binderInfo_900_ = lean_ctor_get_uint8(v_e_856_, sizeof(void*)*3 + 8);
lean_inc(v_offset_857_);
lean_inc_ref(v_binderType_898_);
lean_inc_ref(v___x_851_);
v___x_901_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_850_, v___x_851_, v___x_852_, v_start_853_, v_xs_854_, v___x_855_, v_binderType_898_, v_offset_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v_a_903_; lean_object* v_fst_904_; lean_object* v_snd_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
v_a_903_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_901_, 2);
v_fst_904_ = lean_ctor_get(v_a_902_, 0);
lean_inc(v_fst_904_);
v_snd_905_ = lean_ctor_get(v_a_902_, 1);
lean_inc(v_snd_905_);
lean_dec(v_a_902_);
v___x_906_ = lean_unsigned_to_nat(1u);
v___x_907_ = lean_nat_add(v_offset_857_, v___x_906_);
lean_dec(v_offset_857_);
lean_inc_ref(v_body_899_);
v___x_908_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_850_, v___x_851_, v___x_852_, v_start_853_, v_xs_854_, v___x_855_, v_body_899_, v___x_907_, v_snd_905_, v_a_859_, v_a_860_, v_a_903_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_935_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_a_910_ = lean_ctor_get(v___x_908_, 1);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_935_ == 0)
{
v___x_912_ = v___x_908_;
v_isShared_913_ = v_isSharedCheck_935_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_935_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_fst_914_; lean_object* v_snd_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_934_; 
v_fst_914_ = lean_ctor_get(v_a_909_, 0);
v_snd_915_ = lean_ctor_get(v_a_909_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_a_909_);
if (v_isSharedCheck_934_ == 0)
{
v___x_917_ = v_a_909_;
v_isShared_918_ = v_isSharedCheck_934_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_snd_915_);
lean_inc(v_fst_914_);
lean_dec(v_a_909_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_934_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
uint8_t v___y_920_; size_t v___x_928_; size_t v___x_929_; uint8_t v___x_930_; 
v___x_928_ = lean_ptr_addr(v_binderType_898_);
v___x_929_ = lean_ptr_addr(v_fst_904_);
v___x_930_ = lean_usize_dec_eq(v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
v___y_920_ = v___x_930_;
goto v___jp_919_;
}
else
{
size_t v___x_931_; size_t v___x_932_; uint8_t v___x_933_; 
v___x_931_ = lean_ptr_addr(v_body_899_);
v___x_932_ = lean_ptr_addr(v_fst_914_);
v___x_933_ = lean_usize_dec_eq(v___x_931_, v___x_932_);
v___y_920_ = v___x_933_;
goto v___jp_919_;
}
v___jp_919_:
{
if (v___y_920_ == 0)
{
lean_object* v___x_921_; 
lean_inc(v_binderName_897_);
lean_del_object(v___x_917_);
lean_del_object(v___x_912_);
lean_dec_ref_known(v_e_856_, 3);
v___x_921_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_binderName_897_, v_binderInfo_900_, v_fst_904_, v_fst_914_, v_snd_915_, v_a_859_, v_a_860_, v_a_910_);
return v___x_921_;
}
else
{
lean_object* v___x_923_; 
lean_dec(v_fst_914_);
lean_dec(v_fst_904_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v_e_856_);
v___x_923_ = v___x_917_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_e_856_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_snd_915_);
v___x_923_ = v_reuseFailAlloc_927_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_925_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_923_);
v___x_925_ = v___x_912_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_a_910_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_904_);
lean_dec_ref_known(v_e_856_, 3);
return v___x_908_;
}
}
else
{
lean_dec_ref_known(v_e_856_, 3);
lean_dec(v_offset_857_);
lean_dec_ref(v___x_851_);
return v___x_901_;
}
}
case 7:
{
lean_object* v_binderName_936_; lean_object* v_binderType_937_; lean_object* v_body_938_; uint8_t v_binderInfo_939_; lean_object* v___x_940_; 
v_binderName_936_ = lean_ctor_get(v_e_856_, 0);
v_binderType_937_ = lean_ctor_get(v_e_856_, 1);
v_body_938_ = lean_ctor_get(v_e_856_, 2);
v_binderInfo_939_ = lean_ctor_get_uint8(v_e_856_, sizeof(void*)*3 + 8);
lean_inc(v_offset_857_);
lean_inc_ref(v_binderType_937_);
lean_inc_ref(v___x_851_);
v___x_940_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_850_, v___x_851_, v___x_852_, v_start_853_, v_xs_854_, v___x_855_, v_binderType_937_, v_offset_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v_a_942_; lean_object* v_fst_943_; lean_object* v_snd_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
v_a_942_ = lean_ctor_get(v___x_940_, 1);
lean_inc(v_a_942_);
lean_dec_ref_known(v___x_940_, 2);
v_fst_943_ = lean_ctor_get(v_a_941_, 0);
lean_inc(v_fst_943_);
v_snd_944_ = lean_ctor_get(v_a_941_, 1);
lean_inc(v_snd_944_);
lean_dec(v_a_941_);
v___x_945_ = lean_unsigned_to_nat(1u);
v___x_946_ = lean_nat_add(v_offset_857_, v___x_945_);
lean_dec(v_offset_857_);
lean_inc_ref(v_body_938_);
v___x_947_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_850_, v___x_851_, v___x_852_, v_start_853_, v_xs_854_, v___x_855_, v_body_938_, v___x_946_, v_snd_944_, v_a_859_, v_a_860_, v_a_942_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_974_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
v_a_949_ = lean_ctor_get(v___x_947_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_974_ == 0)
{
v___x_951_ = v___x_947_;
v_isShared_952_ = v_isSharedCheck_974_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_inc(v_a_948_);
lean_dec(v___x_947_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_974_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v_fst_953_; lean_object* v_snd_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_973_; 
v_fst_953_ = lean_ctor_get(v_a_948_, 0);
v_snd_954_ = lean_ctor_get(v_a_948_, 1);
v_isSharedCheck_973_ = !lean_is_exclusive(v_a_948_);
if (v_isSharedCheck_973_ == 0)
{
v___x_956_ = v_a_948_;
v_isShared_957_ = v_isSharedCheck_973_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_snd_954_);
lean_inc(v_fst_953_);
lean_dec(v_a_948_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_973_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
uint8_t v___y_959_; size_t v___x_967_; size_t v___x_968_; uint8_t v___x_969_; 
v___x_967_ = lean_ptr_addr(v_binderType_937_);
v___x_968_ = lean_ptr_addr(v_fst_943_);
v___x_969_ = lean_usize_dec_eq(v___x_967_, v___x_968_);
if (v___x_969_ == 0)
{
v___y_959_ = v___x_969_;
goto v___jp_958_;
}
else
{
size_t v___x_970_; size_t v___x_971_; uint8_t v___x_972_; 
v___x_970_ = lean_ptr_addr(v_body_938_);
v___x_971_ = lean_ptr_addr(v_fst_953_);
v___x_972_ = lean_usize_dec_eq(v___x_970_, v___x_971_);
v___y_959_ = v___x_972_;
goto v___jp_958_;
}
v___jp_958_:
{
if (v___y_959_ == 0)
{
lean_object* v___x_960_; 
lean_inc(v_binderName_936_);
lean_del_object(v___x_956_);
lean_del_object(v___x_951_);
lean_dec_ref_known(v_e_856_, 3);
v___x_960_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_binderName_936_, v_binderInfo_939_, v_fst_943_, v_fst_953_, v_snd_954_, v_a_859_, v_a_860_, v_a_949_);
return v___x_960_;
}
else
{
lean_object* v___x_962_; 
lean_dec(v_fst_953_);
lean_dec(v_fst_943_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v_e_856_);
v___x_962_ = v___x_956_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_e_856_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_snd_954_);
v___x_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_964_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_962_);
v___x_964_ = v___x_951_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_a_949_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_943_);
lean_dec_ref_known(v_e_856_, 3);
return v___x_947_;
}
}
else
{
lean_dec_ref_known(v_e_856_, 3);
lean_dec(v_offset_857_);
lean_dec_ref(v___x_851_);
return v___x_940_;
}
}
case 8:
{
lean_object* v_declName_975_; lean_object* v_type_976_; lean_object* v_value_977_; lean_object* v_body_978_; uint8_t v_nondep_979_; lean_object* v___x_980_; 
v_declName_975_ = lean_ctor_get(v_e_856_, 0);
v_type_976_ = lean_ctor_get(v_e_856_, 1);
v_value_977_ = lean_ctor_get(v_e_856_, 2);
v_body_978_ = lean_ctor_get(v_e_856_, 3);
v_nondep_979_ = lean_ctor_get_uint8(v_e_856_, sizeof(void*)*4 + 8);
lean_inc(v_offset_857_);
lean_inc_ref(v_type_976_);
lean_inc_ref(v___x_851_);
v___x_980_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_850_, v___x_851_, v___x_852_, v_start_853_, v_xs_854_, v___x_855_, v_type_976_, v_offset_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v_a_982_; lean_object* v_fst_983_; lean_object* v_snd_984_; lean_object* v___x_985_; 
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
lean_inc(v_offset_857_);
lean_inc_ref(v_value_977_);
lean_inc_ref(v___x_851_);
v___x_985_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_850_, v___x_851_, v___x_852_, v_start_853_, v_xs_854_, v___x_855_, v_value_977_, v_offset_857_, v_snd_984_, v_a_859_, v_a_860_, v_a_982_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v_a_987_; lean_object* v_fst_988_; lean_object* v_snd_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
v_a_987_ = lean_ctor_get(v___x_985_, 1);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_985_, 2);
v_fst_988_ = lean_ctor_get(v_a_986_, 0);
lean_inc(v_fst_988_);
v_snd_989_ = lean_ctor_get(v_a_986_, 1);
lean_inc(v_snd_989_);
lean_dec(v_a_986_);
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_nat_add(v_offset_857_, v___x_990_);
lean_dec(v_offset_857_);
lean_inc_ref(v_body_978_);
v___x_992_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_850_, v___x_851_, v___x_852_, v_start_853_, v_xs_854_, v___x_855_, v_body_978_, v___x_991_, v_snd_989_, v_a_859_, v_a_860_, v_a_987_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1023_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_a_994_ = lean_ctor_get(v___x_992_, 1);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_996_ = v___x_992_;
v_isShared_997_ = v_isSharedCheck_1023_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1023_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_fst_998_; lean_object* v_snd_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1022_; 
v_fst_998_ = lean_ctor_get(v_a_993_, 0);
v_snd_999_ = lean_ctor_get(v_a_993_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_a_993_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1001_ = v_a_993_;
v_isShared_1002_ = v_isSharedCheck_1022_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_snd_999_);
lean_inc(v_fst_998_);
lean_dec(v_a_993_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1022_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
uint8_t v___y_1004_; size_t v___x_1016_; size_t v___x_1017_; uint8_t v___x_1018_; 
v___x_1016_ = lean_ptr_addr(v_type_976_);
v___x_1017_ = lean_ptr_addr(v_fst_983_);
v___x_1018_ = lean_usize_dec_eq(v___x_1016_, v___x_1017_);
if (v___x_1018_ == 0)
{
v___y_1004_ = v___x_1018_;
goto v___jp_1003_;
}
else
{
size_t v___x_1019_; size_t v___x_1020_; uint8_t v___x_1021_; 
v___x_1019_ = lean_ptr_addr(v_value_977_);
v___x_1020_ = lean_ptr_addr(v_fst_988_);
v___x_1021_ = lean_usize_dec_eq(v___x_1019_, v___x_1020_);
v___y_1004_ = v___x_1021_;
goto v___jp_1003_;
}
v___jp_1003_:
{
if (v___y_1004_ == 0)
{
lean_object* v___x_1005_; 
lean_inc(v_declName_975_);
lean_del_object(v___x_1001_);
lean_del_object(v___x_996_);
lean_dec_ref_known(v_e_856_, 4);
v___x_1005_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_975_, v_fst_983_, v_fst_988_, v_fst_998_, v_nondep_979_, v_snd_999_, v_a_859_, v_a_860_, v_a_994_);
return v___x_1005_;
}
else
{
size_t v___x_1006_; size_t v___x_1007_; uint8_t v___x_1008_; 
v___x_1006_ = lean_ptr_addr(v_body_978_);
v___x_1007_ = lean_ptr_addr(v_fst_998_);
v___x_1008_ = lean_usize_dec_eq(v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
lean_inc(v_declName_975_);
lean_del_object(v___x_1001_);
lean_del_object(v___x_996_);
lean_dec_ref_known(v_e_856_, 4);
v___x_1009_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_975_, v_fst_983_, v_fst_988_, v_fst_998_, v_nondep_979_, v_snd_999_, v_a_859_, v_a_860_, v_a_994_);
return v___x_1009_;
}
else
{
lean_object* v___x_1011_; 
lean_dec(v_fst_998_);
lean_dec(v_fst_988_);
lean_dec(v_fst_983_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v_e_856_);
v___x_1011_ = v___x_1001_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_e_856_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_snd_999_);
v___x_1011_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1013_; 
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1011_);
v___x_1013_ = v___x_996_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_a_994_);
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
}
}
}
else
{
lean_dec(v_fst_988_);
lean_dec(v_fst_983_);
lean_dec_ref_known(v_e_856_, 4);
return v___x_992_;
}
}
else
{
lean_dec(v_fst_983_);
lean_dec_ref_known(v_e_856_, 4);
lean_dec(v_offset_857_);
lean_dec_ref(v___x_851_);
return v___x_985_;
}
}
else
{
lean_dec_ref_known(v_e_856_, 4);
lean_dec(v_offset_857_);
lean_dec_ref(v___x_851_);
return v___x_980_;
}
}
case 10:
{
lean_object* v_data_1024_; lean_object* v_expr_1025_; lean_object* v___x_1026_; 
v_data_1024_ = lean_ctor_get(v_e_856_, 0);
v_expr_1025_ = lean_ctor_get(v_e_856_, 1);
lean_inc_ref(v_expr_1025_);
v___x_1026_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_850_, v___x_851_, v___x_852_, v_start_853_, v_xs_854_, v___x_855_, v_expr_1025_, v_offset_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1048_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_a_1028_ = lean_ctor_get(v___x_1026_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1030_ = v___x_1026_;
v_isShared_1031_ = v_isSharedCheck_1048_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1048_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_fst_1032_; lean_object* v_snd_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1047_; 
v_fst_1032_ = lean_ctor_get(v_a_1027_, 0);
v_snd_1033_ = lean_ctor_get(v_a_1027_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_a_1027_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1035_ = v_a_1027_;
v_isShared_1036_ = v_isSharedCheck_1047_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_snd_1033_);
lean_inc(v_fst_1032_);
lean_dec(v_a_1027_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1047_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
size_t v___x_1037_; size_t v___x_1038_; uint8_t v___x_1039_; 
v___x_1037_ = lean_ptr_addr(v_expr_1025_);
v___x_1038_ = lean_ptr_addr(v_fst_1032_);
v___x_1039_ = lean_usize_dec_eq(v___x_1037_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
lean_inc(v_data_1024_);
lean_del_object(v___x_1035_);
lean_del_object(v___x_1030_);
lean_dec_ref_known(v_e_856_, 2);
v___x_1040_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(v_data_1024_, v_fst_1032_, v_snd_1033_, v_a_859_, v_a_860_, v_a_1028_);
return v___x_1040_;
}
else
{
lean_object* v___x_1042_; 
lean_dec(v_fst_1032_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v_e_856_);
v___x_1042_ = v___x_1035_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_e_856_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_snd_1033_);
v___x_1042_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1044_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1042_);
v___x_1044_ = v___x_1030_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_a_1028_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_856_, 2);
return v___x_1026_;
}
}
case 11:
{
lean_object* v_typeName_1049_; lean_object* v_idx_1050_; lean_object* v_struct_1051_; lean_object* v___x_1052_; 
v_typeName_1049_ = lean_ctor_get(v_e_856_, 0);
v_idx_1050_ = lean_ctor_get(v_e_856_, 1);
v_struct_1051_ = lean_ctor_get(v_e_856_, 2);
lean_inc_ref(v_struct_1051_);
v___x_1052_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_850_, v___x_851_, v___x_852_, v_start_853_, v_xs_854_, v___x_855_, v_struct_1051_, v_offset_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1074_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_a_1054_ = lean_ctor_get(v___x_1052_, 1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1056_ = v___x_1052_;
v_isShared_1057_ = v_isSharedCheck_1074_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1074_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v_fst_1058_; lean_object* v_snd_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1073_; 
v_fst_1058_ = lean_ctor_get(v_a_1053_, 0);
v_snd_1059_ = lean_ctor_get(v_a_1053_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_a_1053_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1061_ = v_a_1053_;
v_isShared_1062_ = v_isSharedCheck_1073_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_snd_1059_);
lean_inc(v_fst_1058_);
lean_dec(v_a_1053_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1073_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
size_t v___x_1063_; size_t v___x_1064_; uint8_t v___x_1065_; 
v___x_1063_ = lean_ptr_addr(v_struct_1051_);
v___x_1064_ = lean_ptr_addr(v_fst_1058_);
v___x_1065_ = lean_usize_dec_eq(v___x_1063_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
lean_inc(v_idx_1050_);
lean_inc(v_typeName_1049_);
lean_del_object(v___x_1061_);
lean_del_object(v___x_1056_);
lean_dec_ref_known(v_e_856_, 3);
v___x_1066_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(v_typeName_1049_, v_idx_1050_, v_fst_1058_, v_snd_1059_, v_a_859_, v_a_860_, v_a_1054_);
return v___x_1066_;
}
else
{
lean_object* v___x_1068_; 
lean_dec(v_fst_1058_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v_e_856_);
v___x_1068_ = v___x_1061_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_e_856_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_snd_1059_);
v___x_1068_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1070_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1068_);
v___x_1070_ = v___x_1056_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_a_1054_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_856_, 3);
return v___x_1052_;
}
}
default: 
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec(v_offset_857_);
lean_dec_ref(v_e_856_);
lean_dec_ref(v___x_851_);
v___x_1075_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3);
v___x_1076_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(v___x_1075_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(lean_object* v_minIndex_1077_, lean_object* v___x_1078_, lean_object* v___x_1079_, lean_object* v_start_1080_, lean_object* v_xs_1081_, lean_object* v___x_1082_, lean_object* v_e_1083_, lean_object* v_offset_1084_, lean_object* v_a_1085_, uint8_t v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_key_1089_; lean_object* v_a_1091_; lean_object* v___y_1105_; lean_object* v___y_1110_; lean_object* v___x_1115_; 
lean_inc(v_offset_1084_);
lean_inc_ref(v_e_1083_);
v_key_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1089_, 0, v_e_1083_);
lean_ctor_set(v_key_1089_, 1, v_offset_1084_);
v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_a_1085_, v_key_1089_);
if (lean_obj_tag(v___x_1115_) == 1)
{
lean_object* v_val_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec_ref_known(v_key_1089_, 2);
lean_dec(v_offset_1084_);
lean_dec_ref(v_e_1083_);
lean_dec_ref(v___x_1078_);
v_val_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_val_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v_val_1116_);
lean_ctor_set(v___x_1117_, 1, v_a_1085_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v_a_1088_);
return v___x_1118_;
}
else
{
lean_dec(v___x_1115_);
switch(lean_obj_tag(v_e_1083_))
{
case 1:
{
lean_object* v_fvarId_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec_ref(v___x_1078_);
v_fvarId_1119_ = lean_ctor_get(v_e_1083_, 0);
v___x_1120_ = lean_unsigned_to_nat(0u);
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_nat_sub(v___x_1079_, v___x_1121_);
v___x_1123_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_1080_, v_xs_1081_, v_fvarId_1119_, v___x_1120_, v___x_1122_);
if (lean_obj_tag(v___x_1123_) == 1)
{
lean_object* v_val_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec_ref_known(v_e_1083_, 1);
v_val_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_val_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v___x_1125_ = lean_nat_add(v_offset_1084_, v_val_1124_);
lean_dec(v_val_1124_);
lean_dec(v_offset_1084_);
v___x_1126_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v___x_1125_, v_a_1088_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v_a_1128_; lean_object* v___x_1129_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
v_a_1128_ = lean_ctor_get(v___x_1126_, 1);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1126_, 2);
v___x_1129_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1089_, v_a_1127_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1128_);
return v___x_1129_;
}
else
{
lean_object* v_a_1130_; lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec_ref_known(v_key_1089_, 2);
lean_dec_ref(v_a_1085_);
v_a_1130_ = lean_ctor_get(v___x_1126_, 0);
v_a_1131_ = lean_ctor_get(v___x_1126_, 1);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1126_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_inc(v_a_1130_);
lean_dec(v___x_1126_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1130_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_a_1131_);
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
else
{
lean_object* v___x_1139_; 
lean_dec(v___x_1123_);
lean_dec(v_offset_1084_);
v___x_1139_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1089_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1139_;
}
}
case 9:
{
lean_object* v___x_1140_; 
lean_dec(v_offset_1084_);
lean_dec_ref(v___x_1078_);
v___x_1140_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1089_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1140_;
}
case 2:
{
lean_object* v___x_1141_; 
lean_dec(v_offset_1084_);
lean_dec_ref(v___x_1078_);
v___x_1141_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1089_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1141_;
}
case 0:
{
lean_object* v___x_1142_; 
lean_dec(v_offset_1084_);
lean_dec_ref(v___x_1078_);
v___x_1142_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1089_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1142_;
}
case 4:
{
lean_object* v___x_1143_; 
lean_dec(v_offset_1084_);
lean_dec_ref(v___x_1078_);
v___x_1143_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1089_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1143_;
}
case 3:
{
lean_object* v___x_1144_; 
lean_dec(v_offset_1084_);
lean_dec_ref(v___x_1078_);
v___x_1144_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1089_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1144_;
}
default: 
{
uint8_t v___x_1145_; 
v___x_1145_ = l_Lean_Expr_hasFVar(v_e_1083_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; 
lean_dec(v_offset_1084_);
lean_dec_ref(v___x_1078_);
v___x_1146_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1089_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v___x_1082_, v_e_1083_);
if (lean_obj_tag(v___x_1147_) == 1)
{
lean_object* v_val_1148_; 
v_val_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_val_1148_);
lean_dec_ref_known(v___x_1147_, 1);
if (lean_obj_tag(v_val_1148_) == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1150_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v___x_1149_);
v___y_1110_ = v___x_1150_;
goto v___jp_1109_;
}
else
{
lean_object* v_val_1151_; 
v_val_1151_ = lean_ctor_get(v_val_1148_, 0);
lean_inc(v_val_1151_);
lean_dec_ref_known(v_val_1148_, 1);
v___y_1110_ = v_val_1151_;
goto v___jp_1109_;
}
}
else
{
lean_dec(v___x_1147_);
v_a_1091_ = v_a_1088_;
goto v___jp_1090_;
}
}
}
}
}
v___jp_1090_:
{
switch(lean_obj_tag(v_e_1083_))
{
case 9:
{
lean_object* v___x_1092_; 
lean_dec(v_offset_1084_);
lean_dec_ref(v___x_1078_);
v___x_1092_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1089_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1091_);
return v___x_1092_;
}
case 2:
{
lean_object* v___x_1093_; 
lean_dec(v_offset_1084_);
lean_dec_ref(v___x_1078_);
v___x_1093_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1089_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1091_);
return v___x_1093_;
}
case 0:
{
lean_object* v___x_1094_; 
lean_dec(v_offset_1084_);
lean_dec_ref(v___x_1078_);
v___x_1094_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1089_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1091_);
return v___x_1094_;
}
case 1:
{
lean_object* v___x_1095_; 
lean_dec(v_offset_1084_);
lean_dec_ref(v___x_1078_);
v___x_1095_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1089_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1091_);
return v___x_1095_;
}
case 4:
{
lean_object* v___x_1096_; 
lean_dec(v_offset_1084_);
lean_dec_ref(v___x_1078_);
v___x_1096_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1089_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1091_);
return v___x_1096_;
}
case 3:
{
lean_object* v___x_1097_; 
lean_dec(v_offset_1084_);
lean_dec_ref(v___x_1078_);
v___x_1097_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1089_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1091_);
return v___x_1097_;
}
default: 
{
lean_object* v___x_1098_; 
v___x_1098_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v_minIndex_1077_, v___x_1078_, v___x_1079_, v_start_1080_, v_xs_1081_, v___x_1082_, v_e_1083_, v_offset_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1091_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v_a_1100_; lean_object* v_fst_1101_; lean_object* v_snd_1102_; lean_object* v___x_1103_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
v_a_1100_ = lean_ctor_get(v___x_1098_, 1);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1098_, 2);
v_fst_1101_ = lean_ctor_get(v_a_1099_, 0);
lean_inc(v_fst_1101_);
v_snd_1102_ = lean_ctor_get(v_a_1099_, 1);
lean_inc(v_snd_1102_);
lean_dec(v_a_1099_);
v___x_1103_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1089_, v_fst_1101_, v_snd_1102_, v_a_1086_, v_a_1087_, v_a_1100_);
return v___x_1103_;
}
else
{
lean_dec_ref_known(v_key_1089_, 2);
return v___x_1098_;
}
}
}
}
v___jp_1104_:
{
lean_object* v_maxIndex_1106_; uint8_t v___x_1107_; 
v_maxIndex_1106_ = l_Lean_LocalDecl_index(v___y_1105_);
lean_dec_ref(v___y_1105_);
v___x_1107_ = lean_nat_dec_lt(v_maxIndex_1106_, v_minIndex_1077_);
lean_dec(v_maxIndex_1106_);
if (v___x_1107_ == 0)
{
v_a_1091_ = v_a_1088_;
goto v___jp_1090_;
}
else
{
lean_object* v___x_1108_; 
lean_dec(v_offset_1084_);
lean_dec_ref(v___x_1078_);
v___x_1108_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1089_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1108_;
}
}
v___jp_1109_:
{
lean_object* v___x_1111_; 
lean_inc_ref(v___x_1078_);
v___x_1111_ = lean_local_ctx_find(v___x_1078_, v___y_1110_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1113_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1112_);
v___y_1105_ = v___x_1113_;
goto v___jp_1104_;
}
else
{
lean_object* v_val_1114_; 
v_val_1114_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_val_1114_);
lean_dec_ref_known(v___x_1111_, 1);
v___y_1105_ = v_val_1114_;
goto v___jp_1104_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5___boxed(lean_object* v_minIndex_1152_, lean_object* v___x_1153_, lean_object* v___x_1154_, lean_object* v_start_1155_, lean_object* v_xs_1156_, lean_object* v___x_1157_, lean_object* v_e_1158_, lean_object* v_offset_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
uint8_t v_a_boxed_1164_; lean_object* v_res_1165_; 
v_a_boxed_1164_ = lean_unbox(v_a_1161_);
v_res_1165_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_1152_, v___x_1153_, v___x_1154_, v_start_1155_, v_xs_1156_, v___x_1157_, v_e_1158_, v_offset_1159_, v_a_1160_, v_a_boxed_1164_, v_a_1162_, v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec_ref(v___x_1157_);
lean_dec_ref(v_xs_1156_);
lean_dec(v_start_1155_);
lean_dec(v___x_1154_);
lean_dec(v_minIndex_1152_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___boxed(lean_object* v_minIndex_1166_, lean_object* v___x_1167_, lean_object* v___x_1168_, lean_object* v_start_1169_, lean_object* v_xs_1170_, lean_object* v___x_1171_, lean_object* v_e_1172_, lean_object* v_offset_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
uint8_t v_a_boxed_1178_; lean_object* v_res_1179_; 
v_a_boxed_1178_ = lean_unbox(v_a_1175_);
v_res_1179_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v_minIndex_1166_, v___x_1167_, v___x_1168_, v_start_1169_, v_xs_1170_, v___x_1171_, v_e_1172_, v_offset_1173_, v_a_1174_, v_a_boxed_1178_, v_a_1176_, v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec_ref(v___x_1171_);
lean_dec_ref(v_xs_1170_);
lean_dec(v_start_1169_);
lean_dec(v___x_1168_);
lean_dec(v_minIndex_1166_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___lam__0(lean_object* v_e_1180_, lean_object* v_lctx_1181_, lean_object* v___x_1182_, lean_object* v_start_1183_, lean_object* v_xs_1184_, lean_object* v_maxFVar_1185_, uint8_t v_debug_1186_, uint8_t v___x_1187_, lean_object* v___x_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1238_; lean_object* v___x_1259_; 
lean_inc_ref(v_lctx_1181_);
v___x_1259_ = lean_local_ctx_find(v_lctx_1181_, v___x_1188_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1261_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1260_);
v___y_1238_ = v___x_1261_;
goto v___jp_1237_;
}
else
{
lean_object* v_val_1262_; 
v_val_1262_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_val_1262_);
lean_dec_ref_known(v___x_1259_, 1);
v___y_1238_ = v_val_1262_;
goto v___jp_1237_;
}
v___jp_1191_:
{
switch(lean_obj_tag(v_e_1180_))
{
case 9:
{
lean_object* v___x_1194_; 
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v_lctx_1181_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v_e_1180_);
lean_ctor_set(v___x_1194_, 1, v___y_1190_);
return v___x_1194_;
}
case 2:
{
lean_object* v___x_1195_; 
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v_lctx_1181_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v_e_1180_);
lean_ctor_set(v___x_1195_, 1, v___y_1190_);
return v___x_1195_;
}
case 0:
{
lean_object* v___x_1196_; 
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v_lctx_1181_);
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v_e_1180_);
lean_ctor_set(v___x_1196_, 1, v___y_1190_);
return v___x_1196_;
}
case 1:
{
lean_object* v___x_1197_; 
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v_lctx_1181_);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v_e_1180_);
lean_ctor_set(v___x_1197_, 1, v___y_1190_);
return v___x_1197_;
}
case 4:
{
lean_object* v___x_1198_; 
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v_lctx_1181_);
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v_e_1180_);
lean_ctor_set(v___x_1198_, 1, v___y_1190_);
return v___x_1198_;
}
case 3:
{
lean_object* v___x_1199_; 
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v_lctx_1181_);
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v_e_1180_);
lean_ctor_set(v___x_1199_, 1, v___y_1190_);
return v___x_1199_;
}
default: 
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0);
lean_inc(v___y_1192_);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___y_1192_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v___y_1193_, v_lctx_1181_, v___x_1182_, v_start_1183_, v_xs_1184_, v_maxFVar_1185_, v_e_1180_, v___y_1192_, v___x_1201_, v_debug_1186_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1193_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1212_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_a_1204_ = lean_ctor_get(v___x_1202_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1206_ = v___x_1202_;
v_isShared_1207_ = v_isSharedCheck_1212_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1212_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v_fst_1208_; lean_object* v___x_1210_; 
v_fst_1208_ = lean_ctor_get(v_a_1203_, 0);
lean_inc(v_fst_1208_);
lean_dec(v_a_1203_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v_fst_1208_);
v___x_1210_ = v___x_1206_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_fst_1208_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_a_1204_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
v_a_1213_ = lean_ctor_get(v___x_1202_, 0);
v_a_1214_ = lean_ctor_get(v___x_1202_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1202_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_inc(v_a_1213_);
lean_dec(v___x_1202_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1213_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
}
v___jp_1222_:
{
lean_object* v_maxIndex_1226_; uint8_t v___x_1227_; 
v_maxIndex_1226_ = l_Lean_LocalDecl_index(v___y_1225_);
lean_dec_ref(v___y_1225_);
v___x_1227_ = lean_nat_dec_lt(v_maxIndex_1226_, v___y_1224_);
lean_dec(v_maxIndex_1226_);
if (v___x_1227_ == 0)
{
v___y_1192_ = v___y_1223_;
v___y_1193_ = v___y_1224_;
goto v___jp_1191_;
}
else
{
lean_object* v___x_1228_; 
lean_dec(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v_lctx_1181_);
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_e_1180_);
lean_ctor_set(v___x_1228_, 1, v___y_1190_);
return v___x_1228_;
}
}
v___jp_1229_:
{
lean_object* v___x_1233_; 
lean_inc_ref(v_lctx_1181_);
v___x_1233_ = lean_local_ctx_find(v_lctx_1181_, v___y_1232_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1235_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1234_);
v___y_1223_ = v___y_1230_;
v___y_1224_ = v___y_1231_;
v___y_1225_ = v___x_1235_;
goto v___jp_1222_;
}
else
{
lean_object* v_val_1236_; 
v_val_1236_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_val_1236_);
lean_dec_ref_known(v___x_1233_, 1);
v___y_1223_ = v___y_1230_;
v___y_1224_ = v___y_1231_;
v___y_1225_ = v_val_1236_;
goto v___jp_1222_;
}
}
v___jp_1237_:
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1180_))
{
case 1:
{
lean_object* v_fvarId_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec_ref(v___y_1238_);
lean_dec_ref(v_lctx_1181_);
v_fvarId_1240_ = lean_ctor_get(v_e_1180_, 0);
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = lean_nat_sub(v___x_1182_, v___x_1241_);
v___x_1243_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_1183_, v_xs_1184_, v_fvarId_1240_, v___x_1239_, v___x_1242_);
if (lean_obj_tag(v___x_1243_) == 1)
{
lean_object* v_val_1244_; lean_object* v___x_1245_; 
lean_dec_ref_known(v_e_1180_, 1);
v_val_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1244_);
lean_dec_ref_known(v___x_1243_, 1);
v___x_1245_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v_val_1244_, v___y_1190_);
return v___x_1245_;
}
else
{
lean_object* v___x_1246_; 
lean_dec(v___x_1243_);
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_e_1180_);
lean_ctor_set(v___x_1246_, 1, v___y_1190_);
return v___x_1246_;
}
}
case 9:
{
lean_object* v___x_1247_; 
lean_dec_ref(v___y_1238_);
lean_dec_ref(v_lctx_1181_);
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_e_1180_);
lean_ctor_set(v___x_1247_, 1, v___y_1190_);
return v___x_1247_;
}
case 2:
{
lean_object* v___x_1248_; 
lean_dec_ref(v___y_1238_);
lean_dec_ref(v_lctx_1181_);
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v_e_1180_);
lean_ctor_set(v___x_1248_, 1, v___y_1190_);
return v___x_1248_;
}
case 0:
{
lean_object* v___x_1249_; 
lean_dec_ref(v___y_1238_);
lean_dec_ref(v_lctx_1181_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v_e_1180_);
lean_ctor_set(v___x_1249_, 1, v___y_1190_);
return v___x_1249_;
}
case 4:
{
lean_object* v___x_1250_; 
lean_dec_ref(v___y_1238_);
lean_dec_ref(v_lctx_1181_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v_e_1180_);
lean_ctor_set(v___x_1250_, 1, v___y_1190_);
return v___x_1250_;
}
case 3:
{
lean_object* v___x_1251_; 
lean_dec_ref(v___y_1238_);
lean_dec_ref(v_lctx_1181_);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_e_1180_);
lean_ctor_set(v___x_1251_, 1, v___y_1190_);
return v___x_1251_;
}
default: 
{
if (v___x_1187_ == 0)
{
lean_object* v___x_1252_; 
lean_dec_ref(v___y_1238_);
lean_dec_ref(v_lctx_1181_);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_e_1180_);
lean_ctor_set(v___x_1252_, 1, v___y_1190_);
return v___x_1252_;
}
else
{
lean_object* v_minIndex_1253_; lean_object* v___x_1254_; 
v_minIndex_1253_ = l_Lean_LocalDecl_index(v___y_1238_);
lean_dec_ref(v___y_1238_);
v___x_1254_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_maxFVar_1185_, v_e_1180_);
if (lean_obj_tag(v___x_1254_) == 1)
{
lean_object* v_val_1255_; 
v_val_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_val_1255_);
lean_dec_ref_known(v___x_1254_, 1);
if (lean_obj_tag(v_val_1255_) == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1257_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v___x_1256_);
v___y_1230_ = v___x_1239_;
v___y_1231_ = v_minIndex_1253_;
v___y_1232_ = v___x_1257_;
goto v___jp_1229_;
}
else
{
lean_object* v_val_1258_; 
v_val_1258_ = lean_ctor_get(v_val_1255_, 0);
lean_inc(v_val_1258_);
lean_dec_ref_known(v_val_1255_, 1);
v___y_1230_ = v___x_1239_;
v___y_1231_ = v_minIndex_1253_;
v___y_1232_ = v_val_1258_;
goto v___jp_1229_;
}
}
else
{
lean_dec(v___x_1254_);
v___y_1192_ = v___x_1239_;
v___y_1193_ = v_minIndex_1253_;
goto v___jp_1191_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___lam__0___boxed(lean_object* v_e_1263_, lean_object* v_lctx_1264_, lean_object* v___x_1265_, lean_object* v_start_1266_, lean_object* v_xs_1267_, lean_object* v_maxFVar_1268_, lean_object* v_debug_1269_, lean_object* v___x_1270_, lean_object* v___x_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
uint8_t v_debug_boxed_1274_; uint8_t v___x_27391__boxed_1275_; lean_object* v_res_1276_; 
v_debug_boxed_1274_ = lean_unbox(v_debug_1269_);
v___x_27391__boxed_1275_ = lean_unbox(v___x_1270_);
v_res_1276_ = l_Lean_Meta_Sym_abstractFVarsRange___lam__0(v_e_1263_, v_lctx_1264_, v___x_1265_, v_start_1266_, v_xs_1267_, v_maxFVar_1268_, v_debug_boxed_1274_, v___x_27391__boxed_1275_, v___x_1271_, v___y_1272_, v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec_ref(v_maxFVar_1268_);
lean_dec_ref(v_xs_1267_);
lean_dec(v_start_1266_);
lean_dec(v___x_1265_);
return v_res_1276_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_abstractFVarsRange___closed__2(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1279_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__2));
v___x_1280_ = lean_unsigned_to_nat(16u);
v___x_1281_ = lean_unsigned_to_nat(62u);
v___x_1282_ = ((lean_object*)(l_Lean_Meta_Sym_abstractFVarsRange___closed__1));
v___x_1283_ = ((lean_object*)(l_Lean_Meta_Sym_abstractFVarsRange___closed__0));
v___x_1284_ = l_mkPanicMessageWithDecl(v___x_1283_, v___x_1282_, v___x_1281_, v___x_1280_, v___x_1279_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange(lean_object* v_e_1285_, lean_object* v_start_1286_, lean_object* v_xs_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
uint8_t v___x_1295_; 
v___x_1295_ = l_Lean_Expr_hasFVar(v_e_1285_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; 
lean_dec_ref(v_xs_1287_);
lean_dec(v_start_1286_);
v___x_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1296_, 0, v_e_1285_);
return v___x_1296_;
}
else
{
lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = lean_array_get_size(v_xs_1287_);
v___x_1298_ = lean_nat_dec_lt(v_start_1286_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; 
lean_dec_ref(v_xs_1287_);
lean_dec(v_start_1286_);
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v_e_1285_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v_lctx_1303_; lean_object* v_maxFVar_1304_; uint8_t v_debug_1305_; lean_object* v_env_1306_; uint8_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___f_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1300_ = lean_st_ref_get(v_a_1289_);
v___x_1301_ = lean_st_ref_get(v_a_1289_);
v___x_1302_ = lean_st_ref_get(v_a_1293_);
v_lctx_1303_ = lean_ctor_get(v_a_1290_, 2);
v_maxFVar_1304_ = lean_ctor_get(v___x_1300_, 1);
lean_inc_ref(v_maxFVar_1304_);
lean_dec(v___x_1300_);
v_debug_1305_ = lean_ctor_get_uint8(v___x_1301_, sizeof(void*)*11);
lean_dec(v___x_1301_);
v_env_1306_ = lean_ctor_get(v___x_1302_, 0);
lean_inc_ref(v_env_1306_);
lean_dec(v___x_1302_);
v___x_1307_ = 0;
v___x_1308_ = lean_array_fget_borrowed(v_xs_1287_, v_start_1286_);
v___x_1309_ = l_Lean_Expr_fvarId_x21(v___x_1308_);
v___x_1310_ = lean_box(v_debug_1305_);
v___x_1311_ = lean_box(v___x_1295_);
lean_inc_ref(v_lctx_1303_);
v___f_1312_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_abstractFVarsRange___lam__0___boxed), 11, 9);
lean_closure_set(v___f_1312_, 0, v_e_1285_);
lean_closure_set(v___f_1312_, 1, v_lctx_1303_);
lean_closure_set(v___f_1312_, 2, v___x_1297_);
lean_closure_set(v___f_1312_, 3, v_start_1286_);
lean_closure_set(v___f_1312_, 4, v_xs_1287_);
lean_closure_set(v___f_1312_, 5, v_maxFVar_1304_);
lean_closure_set(v___f_1312_, 6, v___x_1310_);
lean_closure_set(v___f_1312_, 7, v___x_1311_);
lean_closure_set(v___f_1312_, 8, v___x_1309_);
v___x_1313_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1313_, 0, v_env_1306_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*1, v___x_1307_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*1 + 1, v___x_1307_);
v___x_1314_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1312_, v___x_1313_, v_a_1289_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1325_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1317_ = v___x_1314_;
v_isShared_1318_ = v_isSharedCheck_1325_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1325_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
if (lean_obj_tag(v_a_1315_) == 0)
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
lean_dec_ref_known(v_a_1315_, 1);
lean_del_object(v___x_1317_);
v___x_1319_ = lean_obj_once(&l_Lean_Meta_Sym_abstractFVarsRange___closed__2, &l_Lean_Meta_Sym_abstractFVarsRange___closed__2_once, _init_l_Lean_Meta_Sym_abstractFVarsRange___closed__2);
v___x_1320_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v___x_1319_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
return v___x_1320_;
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; 
v_a_1321_ = lean_ctor_get(v_a_1315_, 0);
lean_inc(v_a_1321_);
lean_dec_ref_known(v_a_1315_, 1);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v_a_1321_);
v___x_1323_ = v___x_1317_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
v_a_1326_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1314_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1314_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___boxed(lean_object* v_e_1334_, lean_object* v_start_1335_, lean_object* v_xs_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1334_, v_start_1335_, v_xs_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(lean_object* v_00_u03b2_1345_, lean_object* v_x_1346_, lean_object* v_x_1347_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_x_1346_, v_x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___boxed(lean_object* v_00_u03b2_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(v_00_u03b2_1349_, v_x_1350_, v_x_1351_);
lean_dec_ref(v_x_1351_);
lean_dec_ref(v_x_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2(lean_object* v_00_u03b2_1353_, lean_object* v_x_1354_, size_t v_x_1355_, lean_object* v_x_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_1354_, v_x_1355_, v_x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1358_, lean_object* v_x_1359_, lean_object* v_x_1360_, lean_object* v_x_1361_){
_start:
{
size_t v_x_27681__boxed_1362_; lean_object* v_res_1363_; 
v_x_27681__boxed_1362_ = lean_unbox_usize(v_x_1360_);
lean_dec(v_x_1360_);
v_res_1363_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2(v_00_u03b2_1358_, v_x_1359_, v_x_27681__boxed_1362_, v_x_1361_);
lean_dec_ref(v_x_1361_);
lean_dec_ref(v_x_1359_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_1364_, lean_object* v_keys_1365_, lean_object* v_vals_1366_, lean_object* v_heq_1367_, lean_object* v_i_1368_, lean_object* v_k_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_keys_1365_, v_vals_1366_, v_i_1368_, v_k_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1371_, lean_object* v_keys_1372_, lean_object* v_vals_1373_, lean_object* v_heq_1374_, lean_object* v_i_1375_, lean_object* v_k_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5(v_00_u03b2_1371_, v_keys_1372_, v_vals_1373_, v_heq_1374_, v_i_1375_, v_k_1376_);
lean_dec_ref(v_k_1376_);
lean_dec_ref(v_vals_1373_);
lean_dec_ref(v_keys_1372_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_1378_, lean_object* v_m_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_m_1379_, v_a_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1382_, lean_object* v_m_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8(v_00_u03b2_1382_, v_m_1383_, v_a_1384_);
lean_dec_ref(v_a_1384_);
lean_dec_ref(v_m_1383_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16(lean_object* v_00_u03b2_1386_, lean_object* v_a_1387_, lean_object* v_x_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_a_1387_, v_x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___boxed(lean_object* v_00_u03b2_1390_, lean_object* v_a_1391_, lean_object* v_x_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16(v_00_u03b2_1390_, v_a_1391_, v_x_1392_);
lean_dec(v_x_1392_);
lean_dec_ref(v_a_1391_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars(lean_object* v_e_1394_, lean_object* v_xs_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1404_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1394_, v___x_1403_, v_xs_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___boxed(lean_object* v_e_1405_, lean_object* v_xs_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_Meta_Sym_abstractFVars(v_e_1405_, v_xs_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(lean_object* v_x_1415_, uint8_t v_bi_1416_, lean_object* v_t_1417_, lean_object* v_b_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___y_1427_; lean_object* v___x_1430_; uint8_t v_debug_1431_; 
v___x_1430_ = lean_st_ref_get(v___y_1420_);
v_debug_1431_ = lean_ctor_get_uint8(v___x_1430_, sizeof(void*)*11);
lean_dec(v___x_1430_);
if (v_debug_1431_ == 0)
{
v___y_1427_ = v___y_1420_;
goto v___jp_1426_;
}
else
{
lean_object* v___x_1432_; 
lean_inc_ref(v_t_1417_);
v___x_1432_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1417_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v___x_1433_; 
lean_dec_ref_known(v___x_1432_, 1);
lean_inc_ref(v_b_1418_);
v___x_1433_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_dec_ref_known(v___x_1433_, 1);
v___y_1427_ = v___y_1420_;
goto v___jp_1426_;
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec_ref(v_b_1418_);
lean_dec_ref(v_t_1417_);
lean_dec(v_x_1415_);
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec_ref(v_b_1418_);
lean_dec_ref(v_t_1417_);
lean_dec(v_x_1415_);
v_a_1442_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1432_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1432_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
v___jp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = l_Lean_Expr_lam___override(v_x_1415_, v_t_1417_, v_b_1418_, v_bi_1416_);
v___x_1429_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1428_, v___y_1427_);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0___boxed(lean_object* v_x_1450_, lean_object* v_bi_1451_, lean_object* v_t_1452_, lean_object* v_b_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
uint8_t v_bi_boxed_1461_; lean_object* v_res_1462_; 
v_bi_boxed_1461_ = lean_unbox(v_bi_1451_);
v_res_1462_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v_x_1450_, v_bi_boxed_1461_, v_t_1452_, v_b_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(lean_object* v_xs_1463_, lean_object* v_i_1464_, lean_object* v_a_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_zero_1473_; uint8_t v_isZero_1474_; 
v_zero_1473_ = lean_unsigned_to_nat(0u);
v_isZero_1474_ = lean_nat_dec_eq(v_i_1464_, v_zero_1473_);
if (v_isZero_1474_ == 1)
{
lean_object* v___x_1475_; 
lean_dec(v_i_1464_);
lean_dec_ref(v_xs_1463_);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_a_1465_);
return v___x_1475_;
}
else
{
lean_object* v_one_1476_; lean_object* v_n_1477_; lean_object* v___y_1479_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_one_1476_ = lean_unsigned_to_nat(1u);
v_n_1477_ = lean_nat_sub(v_i_1464_, v_one_1476_);
lean_dec(v_i_1464_);
v___x_1482_ = lean_array_fget_borrowed(v_xs_1463_, v_n_1477_);
v___x_1483_ = l_Lean_Expr_fvarId_x21(v___x_1482_);
v___x_1484_ = l_Lean_FVarId_getDecl___redArg(v___x_1483_, v___y_1468_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref_known(v___x_1484_, 1);
v___x_1486_ = l_Lean_LocalDecl_type(v_a_1485_);
lean_inc_ref(v_xs_1463_);
lean_inc(v_n_1477_);
v___x_1487_ = l_Lean_Meta_Sym_abstractFVarsRange(v___x_1486_, v_n_1477_, v_xs_1463_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref_known(v___x_1487_, 1);
v___x_1489_ = l_Lean_LocalDecl_userName(v_a_1485_);
v___x_1490_ = l_Lean_LocalDecl_binderInfo(v_a_1485_);
lean_dec(v_a_1485_);
v___x_1491_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v___x_1489_, v___x_1490_, v_a_1488_, v_a_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
v___y_1479_ = v___x_1491_;
goto v___jp_1478_;
}
else
{
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1465_);
v___y_1479_ = v___x_1487_;
goto v___jp_1478_;
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec(v_n_1477_);
lean_dec_ref(v_a_1465_);
lean_dec_ref(v_xs_1463_);
v_a_1492_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1484_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1484_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
v___jp_1478_:
{
if (lean_obj_tag(v___y_1479_) == 0)
{
lean_object* v_a_1480_; 
v_a_1480_ = lean_ctor_get(v___y_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v___y_1479_, 1);
v_i_1464_ = v_n_1477_;
v_a_1465_ = v_a_1480_;
goto _start;
}
else
{
lean_dec(v_n_1477_);
lean_dec_ref(v_xs_1463_);
return v___y_1479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg___boxed(lean_object* v_xs_1500_, lean_object* v_i_1501_, lean_object* v_a_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1500_, v_i_1501_, v_a_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS(lean_object* v_xs_1511_, lean_object* v_e_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_xs_1511_);
v___x_1521_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1512_, v___x_1520_, v_xs_1511_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v___x_1523_ = lean_array_get_size(v_xs_1511_);
v___x_1524_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1511_, v___x_1523_, v_a_1522_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1524_;
}
else
{
lean_dec_ref(v_xs_1511_);
return v___x_1521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS___boxed(lean_object* v_xs_1525_, lean_object* v_e_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_1525_, v_e_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(lean_object* v_xs_1535_, lean_object* v_n_1536_, lean_object* v_i_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1535_, v_i_1537_, v_a_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___boxed(lean_object* v_xs_1548_, lean_object* v_n_1549_, lean_object* v_i_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(v_xs_1548_, v_n_1549_, v_i_1550_, v_a_1551_, v_a_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v_n_1549_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(lean_object* v_x_1561_, uint8_t v_bi_1562_, lean_object* v_t_1563_, lean_object* v_b_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v___y_1573_; lean_object* v___x_1576_; uint8_t v_debug_1577_; 
v___x_1576_ = lean_st_ref_get(v___y_1566_);
v_debug_1577_ = lean_ctor_get_uint8(v___x_1576_, sizeof(void*)*11);
lean_dec(v___x_1576_);
if (v_debug_1577_ == 0)
{
v___y_1573_ = v___y_1566_;
goto v___jp_1572_;
}
else
{
lean_object* v___x_1578_; 
lean_inc_ref(v_t_1563_);
v___x_1578_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1563_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v___x_1579_; 
lean_dec_ref_known(v___x_1578_, 1);
lean_inc_ref(v_b_1564_);
v___x_1579_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_dec_ref_known(v___x_1579_, 1);
v___y_1573_ = v___y_1566_;
goto v___jp_1572_;
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec_ref(v_b_1564_);
lean_dec_ref(v_t_1563_);
lean_dec(v_x_1561_);
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec_ref(v_b_1564_);
lean_dec_ref(v_t_1563_);
lean_dec(v_x_1561_);
v_a_1588_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1578_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1578_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
v___jp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = l_Lean_Expr_forallE___override(v_x_1561_, v_t_1563_, v_b_1564_, v_bi_1562_);
v___x_1575_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1574_, v___y_1573_);
return v___x_1575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0___boxed(lean_object* v_x_1596_, lean_object* v_bi_1597_, lean_object* v_t_1598_, lean_object* v_b_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
uint8_t v_bi_boxed_1607_; lean_object* v_res_1608_; 
v_bi_boxed_1607_ = lean_unbox(v_bi_1597_);
v_res_1608_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v_x_1596_, v_bi_boxed_1607_, v_t_1598_, v_b_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(lean_object* v_xs_1609_, lean_object* v_i_1610_, lean_object* v_a_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_zero_1619_; uint8_t v_isZero_1620_; 
v_zero_1619_ = lean_unsigned_to_nat(0u);
v_isZero_1620_ = lean_nat_dec_eq(v_i_1610_, v_zero_1619_);
if (v_isZero_1620_ == 1)
{
lean_object* v___x_1621_; 
lean_dec(v_i_1610_);
lean_dec_ref(v_xs_1609_);
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v_a_1611_);
return v___x_1621_;
}
else
{
lean_object* v_one_1622_; lean_object* v_n_1623_; lean_object* v___y_1625_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v_one_1622_ = lean_unsigned_to_nat(1u);
v_n_1623_ = lean_nat_sub(v_i_1610_, v_one_1622_);
lean_dec(v_i_1610_);
v___x_1628_ = lean_array_fget_borrowed(v_xs_1609_, v_n_1623_);
v___x_1629_ = l_Lean_Expr_fvarId_x21(v___x_1628_);
v___x_1630_ = l_Lean_FVarId_getDecl___redArg(v___x_1629_, v___y_1614_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
v___x_1632_ = l_Lean_LocalDecl_type(v_a_1631_);
lean_inc_ref(v_xs_1609_);
lean_inc(v_n_1623_);
v___x_1633_ = l_Lean_Meta_Sym_abstractFVarsRange(v___x_1632_, v_n_1623_, v_xs_1609_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1635_ = l_Lean_LocalDecl_userName(v_a_1631_);
v___x_1636_ = l_Lean_LocalDecl_binderInfo(v_a_1631_);
lean_dec(v_a_1631_);
v___x_1637_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v___x_1635_, v___x_1636_, v_a_1634_, v_a_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
v___y_1625_ = v___x_1637_;
goto v___jp_1624_;
}
else
{
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1611_);
v___y_1625_ = v___x_1633_;
goto v___jp_1624_;
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec(v_n_1623_);
lean_dec_ref(v_a_1611_);
lean_dec_ref(v_xs_1609_);
v_a_1638_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1630_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1630_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
v___jp_1624_:
{
if (lean_obj_tag(v___y_1625_) == 0)
{
lean_object* v_a_1626_; 
v_a_1626_ = lean_ctor_get(v___y_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___y_1625_, 1);
v_i_1610_ = v_n_1623_;
v_a_1611_ = v_a_1626_;
goto _start;
}
else
{
lean_dec(v_n_1623_);
lean_dec_ref(v_xs_1609_);
return v___y_1625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg___boxed(lean_object* v_xs_1646_, lean_object* v_i_1647_, lean_object* v_a_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1646_, v_i_1647_, v_a_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object* v_xs_1657_, lean_object* v_e_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_xs_1657_);
v___x_1667_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1658_, v___x_1666_, v_xs_1657_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
v___x_1669_ = lean_array_get_size(v_xs_1657_);
v___x_1670_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1657_, v___x_1669_, v_a_1668_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
return v___x_1670_;
}
else
{
lean_dec_ref(v_xs_1657_);
return v___x_1667_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS___boxed(lean_object* v_xs_1671_, lean_object* v_e_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_Meta_Sym_mkForallFVarsS(v_xs_1671_, v_e_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(lean_object* v_xs_1681_, lean_object* v_n_1682_, lean_object* v_i_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1681_, v_i_1683_, v_a_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___boxed(lean_object* v_xs_1694_, lean_object* v_n_1695_, lean_object* v_i_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(v_xs_1694_, v_n_1695_, v_i_1696_, v_a_1697_, v_a_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v_n_1695_);
return v_res_1706_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
