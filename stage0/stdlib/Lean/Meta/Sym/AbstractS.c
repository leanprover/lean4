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
lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__3;
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsPrefix___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsPrefix___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(lean_object* v_toDeBruijn_x3f_10_, lean_object* v___x_11_, lean_object* v___f_12_, lean_object* v___f_13_, lean_object* v_maxFVar_14_, lean_object* v_minIndex_15_, lean_object* v_lctx_16_, lean_object* v___x_17_, lean_object* v___x_18_, lean_object* v_e_19_, lean_object* v_offset_20_, uint8_t v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___y_25_; lean_object* v___y_33_; 
switch(lean_obj_tag(v_e_19_))
{
case 1:
{
lean_object* v_fvarId_38_; lean_object* v___x_39_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___f_13_);
lean_dec_ref(v___f_12_);
v_fvarId_38_ = lean_ctor_get(v_e_19_, 0);
lean_inc(v_fvarId_38_);
v___x_39_ = lean_apply_1(v_toDeBruijn_x3f_10_, v_fvarId_38_);
if (lean_obj_tag(v___x_39_) == 1)
{
lean_object* v_val_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_69_; 
lean_dec_ref_known(v_e_19_, 1);
v_val_40_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_69_ == 0)
{
v___x_42_ = v___x_39_;
v_isShared_43_ = v_isSharedCheck_69_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_val_40_);
lean_dec(v___x_39_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_69_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; lean_object* v___x_2511__overap_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_44_ = lean_nat_add(v_offset_20_, v_val_40_);
lean_dec(v_val_40_);
v___x_2511__overap_45_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v___x_11_, v___x_44_);
v___x_46_ = lean_box(v___y_21_);
lean_inc_ref(v___y_22_);
v___x_47_ = lean_apply_3(v___x_2511__overap_45_, v___x_46_, v___y_22_, v___y_23_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_59_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
v_a_49_ = lean_ctor_get(v___x_47_, 1);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_59_ == 0)
{
v___x_51_ = v___x_47_;
v_isShared_52_ = v_isSharedCheck_59_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_inc(v_a_48_);
lean_dec(v___x_47_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_59_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_54_; 
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 0, v_a_48_);
v___x_54_ = v___x_42_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_a_48_);
v___x_54_ = v_reuseFailAlloc_58_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_56_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___x_54_);
v___x_56_ = v___x_51_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v___x_54_);
lean_ctor_set(v_reuseFailAlloc_57_, 1, v_a_49_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
}
else
{
lean_object* v_a_60_; lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
lean_del_object(v___x_42_);
v_a_60_ = lean_ctor_get(v___x_47_, 0);
v_a_61_ = lean_ctor_get(v___x_47_, 1);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_68_ == 0)
{
v___x_63_ = v___x_47_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_inc(v_a_60_);
lean_dec(v___x_47_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_a_60_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_a_61_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec(v___x_39_);
lean_dec_ref(v___x_11_);
v___x_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_70_, 0, v_e_19_);
v___x_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___y_23_);
return v___x_71_;
}
}
case 9:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___f_13_);
lean_dec_ref(v___f_12_);
lean_dec_ref(v___x_11_);
lean_dec_ref(v_toDeBruijn_x3f_10_);
v___x_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_72_, 0, v_e_19_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___y_23_);
return v___x_73_;
}
case 2:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___f_13_);
lean_dec_ref(v___f_12_);
lean_dec_ref(v___x_11_);
lean_dec_ref(v_toDeBruijn_x3f_10_);
v___x_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_74_, 0, v_e_19_);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v___y_23_);
return v___x_75_;
}
case 0:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___f_13_);
lean_dec_ref(v___f_12_);
lean_dec_ref(v___x_11_);
lean_dec_ref(v_toDeBruijn_x3f_10_);
v___x_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_76_, 0, v_e_19_);
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___y_23_);
return v___x_77_;
}
case 4:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___f_13_);
lean_dec_ref(v___f_12_);
lean_dec_ref(v___x_11_);
lean_dec_ref(v_toDeBruijn_x3f_10_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v_e_19_);
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___y_23_);
return v___x_79_;
}
case 3:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___f_13_);
lean_dec_ref(v___f_12_);
lean_dec_ref(v___x_11_);
lean_dec_ref(v_toDeBruijn_x3f_10_);
v___x_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_80_, 0, v_e_19_);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___y_23_);
return v___x_81_;
}
default: 
{
uint8_t v___x_82_; 
lean_dec_ref(v___x_11_);
lean_dec_ref(v_toDeBruijn_x3f_10_);
v___x_82_ = l_Lean_Expr_hasFVar(v_e_19_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___f_13_);
lean_dec_ref(v___f_12_);
v___x_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_83_, 0, v_e_19_);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v___y_23_);
return v___x_84_;
}
else
{
lean_object* v___x_85_; 
lean_inc_ref(v_e_19_);
v___x_85_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_12_, v___f_13_, v_maxFVar_14_, v_e_19_);
if (lean_obj_tag(v___x_85_) == 1)
{
lean_object* v_val_86_; 
v_val_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc(v_val_86_);
lean_dec_ref_known(v___x_85_, 1);
if (lean_obj_tag(v_val_86_) == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_88_ = l_panic___redArg(v___x_18_, v___x_87_);
v___y_33_ = v___x_88_;
goto v___jp_32_;
}
else
{
lean_object* v_val_89_; 
v_val_89_ = lean_ctor_get(v_val_86_, 0);
lean_inc(v_val_89_);
lean_dec_ref_known(v_val_86_, 1);
v___y_33_ = v_val_89_;
goto v___jp_32_;
}
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec(v___x_85_);
lean_dec_ref(v_e_19_);
lean_dec_ref(v_lctx_16_);
v___x_90_ = lean_box(0);
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___y_23_);
return v___x_91_;
}
}
}
}
v___jp_24_:
{
lean_object* v_maxIndex_26_; uint8_t v___x_27_; 
v_maxIndex_26_ = l_Lean_LocalDecl_index(v___y_25_);
lean_dec_ref(v___y_25_);
v___x_27_ = lean_nat_dec_lt(v_maxIndex_26_, v_minIndex_15_);
lean_dec(v_maxIndex_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; lean_object* v___x_29_; 
lean_dec_ref(v_e_19_);
v___x_28_ = lean_box(0);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___y_23_);
return v___x_29_;
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_30_, 0, v_e_19_);
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
lean_ctor_set(v___x_31_, 1, v___y_23_);
return v___x_31_;
}
}
v___jp_32_:
{
lean_object* v___x_34_; 
v___x_34_ = lean_local_ctx_find(v_lctx_16_, v___y_33_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_36_ = l_panic___redArg(v___x_17_, v___x_35_);
v___y_25_ = v___x_36_;
goto v___jp_24_;
}
else
{
lean_object* v_val_37_; 
v_val_37_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_val_37_);
lean_dec_ref_known(v___x_34_, 1);
v___y_25_ = v_val_37_;
goto v___jp_24_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed(lean_object* v_toDeBruijn_x3f_92_, lean_object* v___x_93_, lean_object* v___f_94_, lean_object* v___f_95_, lean_object* v_maxFVar_96_, lean_object* v_minIndex_97_, lean_object* v_lctx_98_, lean_object* v___x_99_, lean_object* v___x_100_, lean_object* v_e_101_, lean_object* v_offset_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
uint8_t v___y_2602__boxed_106_; lean_object* v_res_107_; 
v___y_2602__boxed_106_ = lean_unbox(v___y_103_);
v_res_107_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(v_toDeBruijn_x3f_92_, v___x_93_, v___f_94_, v___f_95_, v_maxFVar_96_, v_minIndex_97_, v_lctx_98_, v___x_99_, v___x_100_, v_e_101_, v_offset_102_, v___y_2602__boxed_106_, v___y_104_, v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v_offset_102_);
lean_dec(v___x_100_);
lean_dec_ref(v___x_99_);
lean_dec(v_minIndex_97_);
lean_dec_ref(v_maxFVar_96_);
return v_res_107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_box(0);
v___x_111_ = lean_unsigned_to_nat(16u);
v___x_112_ = lean_mk_array(v___x_111_, v___x_110_);
return v___x_112_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__3(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2);
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(lean_object* v_e_116_, lean_object* v_lctx_117_, lean_object* v_maxFVar_118_, lean_object* v_minFVarId_119_, lean_object* v_toDeBruijn_x3f_120_, uint8_t v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___f_127_; lean_object* v___f_128_; lean_object* v___y_130_; lean_object* v___x_231_; 
v___x_124_ = l_Lean_instInhabitedLocalDecl_default;
v___x_125_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
v___x_126_ = lean_box(0);
v___f_127_ = ((lean_object*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0));
v___f_128_ = ((lean_object*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1));
lean_inc_ref(v_lctx_117_);
v___x_231_ = lean_local_ctx_find(v_lctx_117_, v_minFVarId_119_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_233_ = l_panic___redArg(v___x_124_, v___x_232_);
v___y_130_ = v___x_233_;
goto v___jp_129_;
}
else
{
lean_object* v_val_234_; 
v_val_234_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_231_, 1);
v___y_130_ = v_val_234_;
goto v___jp_129_;
}
v___jp_129_:
{
lean_object* v_minIndex_131_; lean_object* v___f_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_minIndex_131_ = l_Lean_LocalDecl_index(v___y_130_);
lean_dec_ref(v___y_130_);
lean_inc_ref(v_lctx_117_);
lean_inc(v_minIndex_131_);
lean_inc_ref(v_maxFVar_118_);
lean_inc_ref(v_toDeBruijn_x3f_120_);
v___f_132_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed), 14, 9);
lean_closure_set(v___f_132_, 0, v_toDeBruijn_x3f_120_);
lean_closure_set(v___f_132_, 1, v___x_125_);
lean_closure_set(v___f_132_, 2, v___f_127_);
lean_closure_set(v___f_132_, 3, v___f_128_);
lean_closure_set(v___f_132_, 4, v_maxFVar_118_);
lean_closure_set(v___f_132_, 5, v_minIndex_131_);
lean_closure_set(v___f_132_, 6, v_lctx_117_);
lean_closure_set(v___f_132_, 7, v___x_124_);
lean_closure_set(v___f_132_, 8, v___x_126_);
v___x_133_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_e_116_);
v___x_134_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(v_toDeBruijn_x3f_120_, v___x_125_, v___f_127_, v___f_128_, v_maxFVar_118_, v_minIndex_131_, v_lctx_117_, v___x_124_, v___x_126_, v_e_116_, v___x_133_, v_a_121_, v_a_122_, v_a_123_);
lean_dec(v_minIndex_131_);
lean_dec_ref(v_maxFVar_118_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
if (lean_obj_tag(v_a_135_) == 1)
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_144_; 
lean_inc_ref(v_a_135_);
lean_dec_ref(v___f_132_);
lean_dec_ref(v_e_116_);
v_a_136_ = lean_ctor_get(v___x_134_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_144_ == 0)
{
lean_object* v_unused_145_; 
v_unused_145_ = lean_ctor_get(v___x_134_, 0);
lean_dec(v_unused_145_);
v___x_138_ = v___x_134_;
v_isShared_139_ = v_isSharedCheck_144_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_134_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_144_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v_val_140_; lean_object* v___x_142_; 
v_val_140_ = lean_ctor_get(v_a_135_, 0);
lean_inc(v_val_140_);
lean_dec_ref_known(v_a_135_, 1);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v_val_140_);
v___x_142_ = v___x_138_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_val_140_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_a_136_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
else
{
switch(lean_obj_tag(v_e_116_))
{
case 9:
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec_ref(v___f_132_);
v_a_146_ = lean_ctor_get(v___x_134_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_153_ == 0)
{
lean_object* v_unused_154_; 
v_unused_154_ = lean_ctor_get(v___x_134_, 0);
lean_dec(v_unused_154_);
v___x_148_ = v___x_134_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_134_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v_e_116_);
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_e_116_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
case 2:
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
lean_dec_ref(v___f_132_);
v_a_155_ = lean_ctor_get(v___x_134_, 1);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; 
v_unused_163_ = lean_ctor_get(v___x_134_, 0);
lean_dec(v_unused_163_);
v___x_157_ = v___x_134_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_134_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v_e_116_);
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_e_116_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
case 0:
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec_ref(v___f_132_);
v_a_164_ = lean_ctor_get(v___x_134_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_171_ == 0)
{
lean_object* v_unused_172_; 
v_unused_172_ = lean_ctor_get(v___x_134_, 0);
lean_dec(v_unused_172_);
v___x_166_ = v___x_134_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_134_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v_e_116_);
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_e_116_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
case 1:
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec_ref(v___f_132_);
v_a_173_ = lean_ctor_get(v___x_134_, 1);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; 
v_unused_181_ = lean_ctor_get(v___x_134_, 0);
lean_dec(v_unused_181_);
v___x_175_ = v___x_134_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_134_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v_e_116_);
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_e_116_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
case 4:
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec_ref(v___f_132_);
v_a_182_ = lean_ctor_get(v___x_134_, 1);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; 
v_unused_190_ = lean_ctor_get(v___x_134_, 0);
lean_dec(v_unused_190_);
v___x_184_ = v___x_134_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_134_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v_e_116_);
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_e_116_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
case 3:
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_dec_ref(v___f_132_);
v_a_191_ = lean_ctor_get(v___x_134_, 1);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; 
v_unused_199_ = lean_ctor_get(v___x_134_, 0);
lean_dec(v_unused_199_);
v___x_193_ = v___x_134_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_134_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v_e_116_);
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_e_116_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
default: 
{
lean_object* v_a_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_a_200_ = lean_ctor_get(v___x_134_, 1);
lean_inc(v_a_200_);
lean_dec_ref_known(v___x_134_, 2);
v___x_201_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__3);
v___x_202_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_116_, v___x_133_, v___f_132_, v___x_201_, v_a_121_, v_a_122_, v_a_200_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_212_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
v_a_204_ = lean_ctor_get(v___x_202_, 1);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_212_ == 0)
{
v___x_206_ = v___x_202_;
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_inc(v_a_203_);
lean_dec(v___x_202_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v_fst_208_; lean_object* v___x_210_; 
v_fst_208_ = lean_ctor_get(v_a_203_, 0);
lean_inc(v_fst_208_);
lean_dec(v_a_203_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v_fst_208_);
v___x_210_ = v___x_206_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_fst_208_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_a_204_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
else
{
lean_object* v_a_213_; lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
v_a_213_ = lean_ctor_get(v___x_202_, 0);
v_a_214_ = lean_ctor_get(v___x_202_, 1);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_202_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_inc(v_a_213_);
lean_dec(v___x_202_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_213_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_222_; lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
lean_dec_ref(v___f_132_);
lean_dec_ref(v_e_116_);
v_a_222_ = lean_ctor_get(v___x_134_, 0);
v_a_223_ = lean_ctor_get(v___x_134_, 1);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_134_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_inc(v_a_222_);
lean_dec(v___x_134_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_222_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___boxed(lean_object* v_e_235_, lean_object* v_lctx_236_, lean_object* v_maxFVar_237_, lean_object* v_minFVarId_238_, lean_object* v_toDeBruijn_x3f_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
uint8_t v_a_boxed_243_; lean_object* v_res_244_; 
v_a_boxed_243_ = lean_unbox(v_a_240_);
v_res_244_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(v_e_235_, v_lctx_236_, v_maxFVar_237_, v_minFVarId_238_, v_toDeBruijn_x3f_239_, v_a_boxed_243_, v_a_241_, v_a_242_);
lean_dec_ref(v_a_241_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(lean_object* v_start_245_, lean_object* v_xs_246_, lean_object* v_fvarId_247_, lean_object* v_bidx_248_, lean_object* v_i_249_){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_250_ = lean_array_fget_borrowed(v_xs_246_, v_i_249_);
v___x_251_ = l_Lean_Expr_fvarId_x21(v___x_250_);
v___x_252_ = l_Lean_instBEqFVarId_beq(v___x_251_, v_fvarId_247_);
lean_dec(v___x_251_);
if (v___x_252_ == 0)
{
uint8_t v___x_253_; 
v___x_253_ = lean_nat_dec_lt(v_start_245_, v_i_249_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_dec(v_i_249_);
lean_dec(v_bidx_248_);
v___x_254_ = lean_box(0);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_nat_add(v_bidx_248_, v___x_255_);
lean_dec(v_bidx_248_);
v___x_257_ = lean_nat_sub(v_i_249_, v___x_255_);
lean_dec(v_i_249_);
v_bidx_248_ = v___x_256_;
v_i_249_ = v___x_257_;
goto _start;
}
}
else
{
lean_object* v___x_259_; 
lean_dec(v_i_249_);
v___x_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_259_, 0, v_bidx_248_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg___boxed(lean_object* v_start_260_, lean_object* v_xs_261_, lean_object* v_fvarId_262_, lean_object* v_bidx_263_, lean_object* v_i_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_260_, v_xs_261_, v_fvarId_262_, v_bidx_263_, v_i_264_);
lean_dec(v_fvarId_262_);
lean_dec_ref(v_xs_261_);
lean_dec(v_start_260_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(lean_object* v_start_266_, lean_object* v_xs_267_, lean_object* v_fvarId_268_, lean_object* v_bidx_269_, lean_object* v_i_270_, lean_object* v_h_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_266_, v_xs_267_, v_fvarId_268_, v_bidx_269_, v_i_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___boxed(lean_object* v_start_273_, lean_object* v_xs_274_, lean_object* v_fvarId_275_, lean_object* v_bidx_276_, lean_object* v_i_277_, lean_object* v_h_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(v_start_273_, v_xs_274_, v_fvarId_275_, v_bidx_276_, v_i_277_, v_h_278_);
lean_dec(v_fvarId_275_);
lean_dec_ref(v_xs_274_);
lean_dec(v_start_273_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(lean_object* v_msg_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = l_Lean_instInhabitedLocalDecl_default;
v___x_282_ = lean_panic_fn_borrowed(v___x_281_, v_msg_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(lean_object* v_idx_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = l_Lean_Expr_bvar___override(v_idx_283_);
v___x_286_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_285_, v___y_284_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(lean_object* v_idx_287_, uint8_t v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v_idx_287_, v___y_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___boxed(lean_object* v_idx_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
uint8_t v___y_25614__boxed_296_; lean_object* v_res_297_; 
v___y_25614__boxed_296_ = lean_unbox(v___y_293_);
v_res_297_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v_idx_292_, v___y_25614__boxed_296_, v___y_294_, v___y_295_);
lean_dec_ref(v___y_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(lean_object* v_msg_298_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_box(0);
v___x_300_ = lean_panic_fn_borrowed(v___x_299_, v_msg_298_);
return v___x_300_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0(void){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(lean_object* v_msg_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_2413__overap_311_; lean_object* v___x_312_; 
v___x_310_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0, &l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0);
v___x_2413__overap_311_ = lean_panic_fn_borrowed(v___x_310_, v_msg_302_);
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
lean_inc(v___y_304_);
lean_inc_ref(v___y_303_);
v___x_312_ = lean_apply_7(v___x_2413__overap_311_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, lean_box(0));
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___boxed(lean_object* v_msg_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v_msg_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(lean_object* v_msg_329_, lean_object* v___y_330_, uint8_t v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v___f_334_; lean_object* v___f_335_; lean_object* v___f_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___f_346_; lean_object* v___f_347_; lean_object* v___f_348_; lean_object* v___f_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_25037__overap_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___f_334_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__0));
v___f_335_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__1));
v___f_336_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__2));
v___x_337_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__3));
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___f_334_);
v___x_339_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__4));
v___x_340_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__5));
v___x_341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_341_, 0, v___x_338_);
lean_ctor_set(v___x_341_, 1, v___x_339_);
lean_ctor_set(v___x_341_, 2, v___f_335_);
lean_ctor_set(v___x_341_, 3, v___f_336_);
lean_ctor_set(v___x_341_, 4, v___x_340_);
v___x_342_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__6));
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = l_ReaderT_instMonad___redArg(v___x_343_);
v___x_345_ = l_ReaderT_instMonad___redArg(v___x_344_);
lean_inc_ref_n(v___x_345_, 6);
v___f_346_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_346_, 0, v___x_345_);
v___f_347_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_347_, 0, v___x_345_);
v___f_348_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_348_, 0, v___x_345_);
v___f_349_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_349_, 0, v___x_345_);
v___x_350_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_350_, 0, lean_box(0));
lean_closure_set(v___x_350_, 1, lean_box(0));
lean_closure_set(v___x_350_, 2, v___x_345_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___f_346_);
v___x_352_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_352_, 0, lean_box(0));
lean_closure_set(v___x_352_, 1, lean_box(0));
lean_closure_set(v___x_352_, 2, v___x_345_);
v___x_353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_353_, 0, v___x_351_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
lean_ctor_set(v___x_353_, 2, v___f_347_);
lean_ctor_set(v___x_353_, 3, v___f_348_);
lean_ctor_set(v___x_353_, 4, v___f_349_);
v___x_354_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_354_, 0, lean_box(0));
lean_closure_set(v___x_354_, 1, lean_box(0));
lean_closure_set(v___x_354_, 2, v___x_345_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_353_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = l_Lean_instInhabitedExpr;
v___x_357_ = l_instInhabitedOfMonad___redArg(v___x_355_, v___x_356_);
v___x_25037__overap_358_ = lean_panic_fn_borrowed(v___x_357_, v_msg_329_);
lean_dec(v___x_357_);
v___x_359_ = lean_box(v___y_331_);
lean_inc_ref(v___y_332_);
v___x_360_ = lean_apply_4(v___x_25037__overap_358_, v___y_330_, v___x_359_, v___y_332_, v___y_333_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___boxed(lean_object* v_msg_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
uint8_t v___y_25672__boxed_366_; lean_object* v_res_367_; 
v___y_25672__boxed_366_ = lean_unbox(v___y_363_);
v_res_367_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(v_msg_361_, v___y_362_, v___y_25672__boxed_366_, v___y_364_, v___y_365_);
lean_dec_ref(v___y_364_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(lean_object* v_structName_368_, lean_object* v_idx_369_, lean_object* v_struct_370_, lean_object* v___y_371_, uint8_t v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___y_376_; lean_object* v___y_377_; 
if (v___y_372_ == 0)
{
v___y_376_ = v___y_371_;
v___y_377_ = v___y_374_;
goto v___jp_375_;
}
else
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_370_, v___y_372_, v___y_373_, v___y_374_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; 
v_a_400_ = lean_ctor_get(v___x_399_, 1);
lean_inc(v_a_400_);
lean_dec_ref_known(v___x_399_, 2);
v___y_376_ = v___y_371_;
v___y_377_ = v_a_400_;
goto v___jp_375_;
}
else
{
lean_object* v_a_401_; lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec_ref(v___y_371_);
lean_dec_ref(v_struct_370_);
lean_dec(v_idx_369_);
lean_dec(v_structName_368_);
v_a_401_ = lean_ctor_get(v___x_399_, 0);
v_a_402_ = lean_ctor_get(v___x_399_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_399_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_inc(v_a_401_);
lean_dec(v___x_399_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_401_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
v___jp_375_:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = l_Lean_Expr_proj___override(v_structName_368_, v_idx_369_, v_struct_370_);
v___x_379_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_378_, v___y_377_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_389_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_a_381_ = lean_ctor_get(v___x_379_, 1);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_389_ == 0)
{
v___x_383_ = v___x_379_;
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_a_380_);
lean_ctor_set(v___x_385_, 1, v___y_376_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_385_);
v___x_387_ = v___x_383_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_a_381_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
else
{
lean_object* v_a_390_; lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec_ref(v___y_376_);
v_a_390_ = lean_ctor_get(v___x_379_, 0);
v_a_391_ = lean_ctor_get(v___x_379_, 1);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_379_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_inc(v_a_390_);
lean_dec(v___x_379_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11___boxed(lean_object* v_structName_410_, lean_object* v_idx_411_, lean_object* v_struct_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
uint8_t v___y_25743__boxed_417_; lean_object* v_res_418_; 
v___y_25743__boxed_417_ = lean_unbox(v___y_414_);
v_res_418_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(v_structName_410_, v_idx_411_, v_struct_412_, v___y_413_, v___y_25743__boxed_417_, v___y_415_, v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(lean_object* v_d_419_, lean_object* v_e_420_, lean_object* v___y_421_, uint8_t v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v___y_426_; lean_object* v___y_427_; 
if (v___y_422_ == 0)
{
v___y_426_ = v___y_421_;
v___y_427_ = v___y_424_;
goto v___jp_425_;
}
else
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_420_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; 
v_a_450_ = lean_ctor_get(v___x_449_, 1);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_449_, 2);
v___y_426_ = v___y_421_;
v___y_427_ = v_a_450_;
goto v___jp_425_;
}
else
{
lean_object* v_a_451_; lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec_ref(v___y_421_);
lean_dec_ref(v_e_420_);
lean_dec(v_d_419_);
v_a_451_ = lean_ctor_get(v___x_449_, 0);
v_a_452_ = lean_ctor_get(v___x_449_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_449_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_inc(v_a_451_);
lean_dec(v___x_449_);
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
v___jp_425_:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = l_Lean_Expr_mdata___override(v_d_419_, v_e_420_);
v___x_429_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_428_, v___y_427_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_439_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_a_431_ = lean_ctor_get(v___x_429_, 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_439_ == 0)
{
v___x_433_ = v___x_429_;
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v_a_430_);
lean_ctor_set(v___x_435_, 1, v___y_426_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_a_431_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_object* v_a_440_; lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec_ref(v___y_426_);
v_a_440_ = lean_ctor_get(v___x_429_, 0);
v_a_441_ = lean_ctor_get(v___x_429_, 1);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_429_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_inc(v_a_440_);
lean_dec(v___x_429_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_440_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10___boxed(lean_object* v_d_460_, lean_object* v_e_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
uint8_t v___y_25826__boxed_466_; lean_object* v_res_467_; 
v___y_25826__boxed_466_ = lean_unbox(v___y_463_);
v_res_467_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(v_d_460_, v_e_461_, v___y_462_, v___y_25826__boxed_466_, v___y_464_, v___y_465_);
lean_dec_ref(v___y_464_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(lean_object* v_keys_468_, lean_object* v_vals_469_, lean_object* v_i_470_, lean_object* v_k_471_){
_start:
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = lean_array_get_size(v_keys_468_);
v___x_473_ = lean_nat_dec_lt(v_i_470_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
lean_dec(v_i_470_);
v___x_474_ = lean_box(0);
return v___x_474_;
}
else
{
lean_object* v_k_x27_475_; size_t v___x_476_; size_t v___x_477_; uint8_t v___x_478_; 
v_k_x27_475_ = lean_array_fget_borrowed(v_keys_468_, v_i_470_);
v___x_476_ = lean_ptr_addr(v_k_471_);
v___x_477_ = lean_ptr_addr(v_k_x27_475_);
v___x_478_ = lean_usize_dec_eq(v___x_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = lean_nat_add(v_i_470_, v___x_479_);
lean_dec(v_i_470_);
v_i_470_ = v___x_480_;
goto _start;
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_array_fget_borrowed(v_vals_469_, v_i_470_);
lean_dec(v_i_470_);
lean_inc(v___x_482_);
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_keys_484_, lean_object* v_vals_485_, lean_object* v_i_486_, lean_object* v_k_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_keys_484_, v_vals_485_, v_i_486_, v_k_487_);
lean_dec_ref(v_k_487_);
lean_dec_ref(v_vals_485_);
lean_dec_ref(v_keys_484_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(lean_object* v_x_489_, size_t v_x_490_, lean_object* v_x_491_){
_start:
{
if (lean_obj_tag(v_x_489_) == 0)
{
lean_object* v_es_492_; lean_object* v___x_493_; size_t v___x_494_; size_t v___x_495_; lean_object* v_j_496_; lean_object* v___x_497_; 
v_es_492_ = lean_ctor_get(v_x_489_, 0);
v___x_493_ = lean_box(2);
v___x_494_ = ((size_t)31ULL);
v___x_495_ = lean_usize_land(v_x_490_, v___x_494_);
v_j_496_ = lean_usize_to_nat(v___x_495_);
v___x_497_ = lean_array_get_borrowed(v___x_493_, v_es_492_, v_j_496_);
lean_dec(v_j_496_);
switch(lean_obj_tag(v___x_497_))
{
case 0:
{
lean_object* v_key_498_; lean_object* v_val_499_; size_t v___x_500_; size_t v___x_501_; uint8_t v___x_502_; 
v_key_498_ = lean_ctor_get(v___x_497_, 0);
v_val_499_ = lean_ctor_get(v___x_497_, 1);
v___x_500_ = lean_ptr_addr(v_x_491_);
v___x_501_ = lean_ptr_addr(v_key_498_);
v___x_502_ = lean_usize_dec_eq(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
v___x_503_ = lean_box(0);
return v___x_503_;
}
else
{
lean_object* v___x_504_; 
lean_inc(v_val_499_);
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v_val_499_);
return v___x_504_;
}
}
case 1:
{
lean_object* v_node_505_; size_t v___x_506_; size_t v___x_507_; 
v_node_505_ = lean_ctor_get(v___x_497_, 0);
v___x_506_ = ((size_t)5ULL);
v___x_507_ = lean_usize_shift_right(v_x_490_, v___x_506_);
v_x_489_ = v_node_505_;
v_x_490_ = v___x_507_;
goto _start;
}
default: 
{
lean_object* v___x_509_; 
v___x_509_ = lean_box(0);
return v___x_509_;
}
}
}
else
{
lean_object* v_ks_510_; lean_object* v_vs_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_ks_510_ = lean_ctor_get(v_x_489_, 0);
v_vs_511_ = lean_ctor_get(v_x_489_, 1);
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_ks_510_, v_vs_511_, v___x_512_, v_x_491_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg___boxed(lean_object* v_x_514_, lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
size_t v_x_25931__boxed_517_; lean_object* v_res_518_; 
v_x_25931__boxed_517_ = lean_unbox_usize(v_x_515_);
lean_dec(v_x_515_);
v_res_518_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_514_, v_x_25931__boxed_517_, v_x_516_);
lean_dec_ref(v_x_516_);
lean_dec_ref(v_x_514_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
size_t v___x_521_; size_t v___x_522_; size_t v___x_523_; uint64_t v___x_524_; size_t v___x_525_; lean_object* v___x_526_; 
v___x_521_ = lean_ptr_addr(v_x_520_);
v___x_522_ = ((size_t)3ULL);
v___x_523_ = lean_usize_shift_right(v___x_521_, v___x_522_);
v___x_524_ = lean_usize_to_uint64(v___x_523_);
v___x_525_ = lean_uint64_to_usize(v___x_524_);
v___x_526_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_519_, v___x_525_, v_x_520_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg___boxed(lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_x_527_, v_x_528_);
lean_dec_ref(v_x_528_);
lean_dec_ref(v_x_527_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(lean_object* v_a_530_, lean_object* v_x_531_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
lean_object* v___x_532_; 
v___x_532_ = lean_box(0);
return v___x_532_;
}
else
{
lean_object* v_key_533_; lean_object* v_value_534_; lean_object* v_tail_535_; lean_object* v_fst_536_; lean_object* v_snd_537_; lean_object* v_fst_538_; lean_object* v_snd_539_; size_t v___x_540_; size_t v___x_541_; uint8_t v___x_542_; 
v_key_533_ = lean_ctor_get(v_x_531_, 0);
v_value_534_ = lean_ctor_get(v_x_531_, 1);
v_tail_535_ = lean_ctor_get(v_x_531_, 2);
v_fst_536_ = lean_ctor_get(v_key_533_, 0);
v_snd_537_ = lean_ctor_get(v_key_533_, 1);
v_fst_538_ = lean_ctor_get(v_a_530_, 0);
v_snd_539_ = lean_ctor_get(v_a_530_, 1);
v___x_540_ = lean_ptr_addr(v_fst_536_);
v___x_541_ = lean_ptr_addr(v_fst_538_);
v___x_542_ = lean_usize_dec_eq(v___x_540_, v___x_541_);
if (v___x_542_ == 0)
{
v_x_531_ = v_tail_535_;
goto _start;
}
else
{
uint8_t v___x_544_; 
v___x_544_ = lean_nat_dec_eq(v_snd_537_, v_snd_539_);
if (v___x_544_ == 0)
{
v_x_531_ = v_tail_535_;
goto _start;
}
else
{
lean_object* v___x_546_; 
lean_inc(v_value_534_);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v_value_534_);
return v___x_546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg___boxed(lean_object* v_a_547_, lean_object* v_x_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_a_547_, v_x_548_);
lean_dec(v_x_548_);
lean_dec_ref(v_a_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(lean_object* v_m_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_buckets_552_; lean_object* v_fst_553_; lean_object* v_snd_554_; lean_object* v___x_555_; size_t v___x_556_; size_t v___x_557_; size_t v___x_558_; uint64_t v___x_559_; uint64_t v___x_560_; uint64_t v___x_561_; uint64_t v___x_562_; uint64_t v___x_563_; uint64_t v_fold_564_; uint64_t v___x_565_; uint64_t v___x_566_; uint64_t v___x_567_; size_t v___x_568_; size_t v___x_569_; size_t v___x_570_; size_t v___x_571_; size_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_buckets_552_ = lean_ctor_get(v_m_550_, 1);
v_fst_553_ = lean_ctor_get(v_a_551_, 0);
v_snd_554_ = lean_ctor_get(v_a_551_, 1);
v___x_555_ = lean_array_get_size(v_buckets_552_);
v___x_556_ = lean_ptr_addr(v_fst_553_);
v___x_557_ = ((size_t)3ULL);
v___x_558_ = lean_usize_shift_right(v___x_556_, v___x_557_);
v___x_559_ = lean_usize_to_uint64(v___x_558_);
v___x_560_ = lean_uint64_of_nat(v_snd_554_);
v___x_561_ = lean_uint64_mix_hash(v___x_559_, v___x_560_);
v___x_562_ = 32ULL;
v___x_563_ = lean_uint64_shift_right(v___x_561_, v___x_562_);
v_fold_564_ = lean_uint64_xor(v___x_561_, v___x_563_);
v___x_565_ = 16ULL;
v___x_566_ = lean_uint64_shift_right(v_fold_564_, v___x_565_);
v___x_567_ = lean_uint64_xor(v_fold_564_, v___x_566_);
v___x_568_ = lean_uint64_to_usize(v___x_567_);
v___x_569_ = lean_usize_of_nat(v___x_555_);
v___x_570_ = ((size_t)1ULL);
v___x_571_ = lean_usize_sub(v___x_569_, v___x_570_);
v___x_572_ = lean_usize_land(v___x_568_, v___x_571_);
v___x_573_ = lean_array_uget_borrowed(v_buckets_552_, v___x_572_);
v___x_574_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_a_551_, v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_m_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_m_575_, v_a_576_);
lean_dec_ref(v_a_576_);
lean_dec_ref(v_m_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(lean_object* v_x_578_, uint8_t v_bi_579_, lean_object* v_t_580_, lean_object* v_b_581_, lean_object* v___y_582_, uint8_t v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___y_587_; lean_object* v___y_588_; 
if (v___y_583_ == 0)
{
v___y_587_ = v___y_582_;
v___y_588_ = v___y_585_;
goto v___jp_586_;
}
else
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_580_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_612_; 
v_a_611_ = lean_ctor_get(v___x_610_, 1);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 2);
v___x_612_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_581_, v___y_583_, v___y_584_, v_a_611_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; 
v_a_613_ = lean_ctor_get(v___x_612_, 1);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 2);
v___y_587_ = v___y_582_;
v___y_588_ = v_a_613_;
goto v___jp_586_;
}
else
{
lean_object* v_a_614_; lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec_ref(v___y_582_);
lean_dec_ref(v_b_581_);
lean_dec_ref(v_t_580_);
lean_dec(v_x_578_);
v_a_614_ = lean_ctor_get(v___x_612_, 0);
v_a_615_ = lean_ctor_get(v___x_612_, 1);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_612_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_inc(v_a_614_);
lean_dec(v___x_612_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_614_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v_a_623_; lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v___y_582_);
lean_dec_ref(v_b_581_);
lean_dec_ref(v_t_580_);
lean_dec(v_x_578_);
v_a_623_ = lean_ctor_get(v___x_610_, 0);
v_a_624_ = lean_ctor_get(v___x_610_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_610_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_inc(v_a_623_);
lean_dec(v___x_610_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_623_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
v___jp_586_:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = l_Lean_Expr_forallE___override(v_x_578_, v_t_580_, v_b_581_, v_bi_579_);
v___x_590_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_589_, v___y_588_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_600_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_a_592_ = lean_ctor_get(v___x_590_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_600_ == 0)
{
v___x_594_ = v___x_590_;
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v_a_591_);
lean_ctor_set(v___x_596_, 1, v___y_587_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_a_592_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
else
{
lean_object* v_a_601_; lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec_ref(v___y_587_);
v_a_601_ = lean_ctor_get(v___x_590_, 0);
v_a_602_ = lean_ctor_get(v___x_590_, 1);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_590_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_inc(v_a_601_);
lean_dec(v___x_590_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_601_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8___boxed(lean_object* v_x_632_, lean_object* v_bi_633_, lean_object* v_t_634_, lean_object* v_b_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
uint8_t v_bi_boxed_640_; uint8_t v___y_26077__boxed_641_; lean_object* v_res_642_; 
v_bi_boxed_640_ = lean_unbox(v_bi_633_);
v___y_26077__boxed_641_ = lean_unbox(v___y_637_);
v_res_642_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_x_632_, v_bi_boxed_640_, v_t_634_, v_b_635_, v___y_636_, v___y_26077__boxed_641_, v___y_638_, v___y_639_);
lean_dec_ref(v___y_638_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(lean_object* v_x_643_, uint8_t v_bi_644_, lean_object* v_t_645_, lean_object* v_b_646_, lean_object* v___y_647_, uint8_t v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___y_652_; lean_object* v___y_653_; 
if (v___y_648_ == 0)
{
v___y_652_ = v___y_647_;
v___y_653_ = v___y_650_;
goto v___jp_651_;
}
else
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_645_, v___y_648_, v___y_649_, v___y_650_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_677_; 
v_a_676_ = lean_ctor_get(v___x_675_, 1);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 2);
v___x_677_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_646_, v___y_648_, v___y_649_, v_a_676_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; 
v_a_678_ = lean_ctor_get(v___x_677_, 1);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_677_, 2);
v___y_652_ = v___y_647_;
v___y_653_ = v_a_678_;
goto v___jp_651_;
}
else
{
lean_object* v_a_679_; lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec_ref(v___y_647_);
lean_dec_ref(v_b_646_);
lean_dec_ref(v_t_645_);
lean_dec(v_x_643_);
v_a_679_ = lean_ctor_get(v___x_677_, 0);
v_a_680_ = lean_ctor_get(v___x_677_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_677_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_inc(v_a_679_);
lean_dec(v___x_677_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_679_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec_ref(v___y_647_);
lean_dec_ref(v_b_646_);
lean_dec_ref(v_t_645_);
lean_dec(v_x_643_);
v_a_688_ = lean_ctor_get(v___x_675_, 0);
v_a_689_ = lean_ctor_get(v___x_675_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_675_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_inc(v_a_688_);
lean_dec(v___x_675_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_688_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
v___jp_651_:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = l_Lean_Expr_lam___override(v_x_643_, v_t_645_, v_b_646_, v_bi_644_);
v___x_655_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_654_, v___y_653_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_665_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_a_657_ = lean_ctor_get(v___x_655_, 1);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_665_ == 0)
{
v___x_659_ = v___x_655_;
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v_a_656_);
lean_ctor_set(v___x_661_, 1, v___y_652_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_661_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_a_657_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
lean_object* v_a_666_; lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v___y_652_);
v_a_666_ = lean_ctor_get(v___x_655_, 0);
v_a_667_ = lean_ctor_get(v___x_655_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_655_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_inc(v_a_666_);
lean_dec(v___x_655_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_666_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7___boxed(lean_object* v_x_697_, lean_object* v_bi_698_, lean_object* v_t_699_, lean_object* v_b_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
uint8_t v_bi_boxed_705_; uint8_t v___y_26183__boxed_706_; lean_object* v_res_707_; 
v_bi_boxed_705_ = lean_unbox(v_bi_698_);
v___y_26183__boxed_706_ = lean_unbox(v___y_702_);
v_res_707_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_x_697_, v_bi_boxed_705_, v_t_699_, v_b_700_, v___y_701_, v___y_26183__boxed_706_, v___y_703_, v___y_704_);
lean_dec_ref(v___y_703_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(lean_object* v_x_708_, lean_object* v_t_709_, lean_object* v_v_710_, lean_object* v_b_711_, uint8_t v_nondep_712_, lean_object* v___y_713_, uint8_t v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___y_718_; lean_object* v___y_719_; 
if (v___y_714_ == 0)
{
v___y_718_ = v___y_713_;
v___y_719_ = v___y_716_;
goto v___jp_717_;
}
else
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_709_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_743_; 
v_a_742_ = lean_ctor_get(v___x_741_, 1);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 2);
v___x_743_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_710_, v___y_714_, v___y_715_, v_a_742_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_745_; 
v_a_744_ = lean_ctor_get(v___x_743_, 1);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_743_, 2);
v___x_745_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_711_, v___y_714_, v___y_715_, v_a_744_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; 
v_a_746_ = lean_ctor_get(v___x_745_, 1);
lean_inc(v_a_746_);
lean_dec_ref_known(v___x_745_, 2);
v___y_718_ = v___y_713_;
v___y_719_ = v_a_746_;
goto v___jp_717_;
}
else
{
lean_object* v_a_747_; lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec_ref(v___y_713_);
lean_dec_ref(v_b_711_);
lean_dec_ref(v_v_710_);
lean_dec_ref(v_t_709_);
lean_dec(v_x_708_);
v_a_747_ = lean_ctor_get(v___x_745_, 0);
v_a_748_ = lean_ctor_get(v___x_745_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_745_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_inc(v_a_747_);
lean_dec(v___x_745_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_747_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec_ref(v___y_713_);
lean_dec_ref(v_b_711_);
lean_dec_ref(v_v_710_);
lean_dec_ref(v_t_709_);
lean_dec(v_x_708_);
v_a_756_ = lean_ctor_get(v___x_743_, 0);
v_a_757_ = lean_ctor_get(v___x_743_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_743_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_inc(v_a_756_);
lean_dec(v___x_743_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_756_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
else
{
lean_object* v_a_765_; lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref(v___y_713_);
lean_dec_ref(v_b_711_);
lean_dec_ref(v_v_710_);
lean_dec_ref(v_t_709_);
lean_dec(v_x_708_);
v_a_765_ = lean_ctor_get(v___x_741_, 0);
v_a_766_ = lean_ctor_get(v___x_741_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_741_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_inc(v_a_765_);
lean_dec(v___x_741_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_765_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
v___jp_717_:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = l_Lean_Expr_letE___override(v_x_708_, v_t_709_, v_v_710_, v_b_711_, v_nondep_712_);
v___x_721_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_720_, v___y_719_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_731_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_a_723_ = lean_ctor_get(v___x_721_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_731_ == 0)
{
v___x_725_ = v___x_721_;
v_isShared_726_ = v_isSharedCheck_731_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_731_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v_a_722_);
lean_ctor_set(v___x_727_, 1, v___y_718_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_727_);
v___x_729_ = v___x_725_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_a_723_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
else
{
lean_object* v_a_732_; lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec_ref(v___y_718_);
v_a_732_ = lean_ctor_get(v___x_721_, 0);
v_a_733_ = lean_ctor_get(v___x_721_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_721_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_inc(v_a_732_);
lean_dec(v___x_721_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
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
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_732_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9___boxed(lean_object* v_x_774_, lean_object* v_t_775_, lean_object* v_v_776_, lean_object* v_b_777_, lean_object* v_nondep_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
uint8_t v_nondep_boxed_783_; uint8_t v___y_26289__boxed_784_; lean_object* v_res_785_; 
v_nondep_boxed_783_ = lean_unbox(v_nondep_778_);
v___y_26289__boxed_784_ = lean_unbox(v___y_780_);
v_res_785_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_x_774_, v_t_775_, v_v_776_, v_b_777_, v_nondep_boxed_783_, v___y_779_, v___y_26289__boxed_784_, v___y_781_, v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(lean_object* v_f_786_, lean_object* v_a_787_, lean_object* v___y_788_, uint8_t v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___y_793_; lean_object* v___y_794_; 
if (v___y_789_ == 0)
{
v___y_793_ = v___y_788_;
v___y_794_ = v___y_791_;
goto v___jp_792_;
}
else
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_786_, v___y_789_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 1);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 2);
v___x_818_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_787_, v___y_789_, v___y_790_, v_a_817_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; 
v_a_819_ = lean_ctor_get(v___x_818_, 1);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 2);
v___y_793_ = v___y_788_;
v___y_794_ = v_a_819_;
goto v___jp_792_;
}
else
{
lean_object* v_a_820_; lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec_ref(v___y_788_);
lean_dec_ref(v_a_787_);
lean_dec_ref(v_f_786_);
v_a_820_ = lean_ctor_get(v___x_818_, 0);
v_a_821_ = lean_ctor_get(v___x_818_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_818_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_inc(v_a_820_);
lean_dec(v___x_818_);
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
else
{
lean_object* v_a_829_; lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v___y_788_);
lean_dec_ref(v_a_787_);
lean_dec_ref(v_f_786_);
v_a_829_ = lean_ctor_get(v___x_816_, 0);
v_a_830_ = lean_ctor_get(v___x_816_, 1);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_816_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_inc(v_a_829_);
lean_dec(v___x_816_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_829_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
v___jp_792_:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = l_Lean_Expr_app___override(v_f_786_, v_a_787_);
v___x_796_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_795_, v___y_794_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_806_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_a_798_ = lean_ctor_get(v___x_796_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_806_ == 0)
{
v___x_800_ = v___x_796_;
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v_a_797_);
lean_ctor_set(v___x_802_, 1, v___y_793_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_802_);
v___x_804_ = v___x_800_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_a_798_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
else
{
lean_object* v_a_807_; lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v___y_793_);
v_a_807_ = lean_ctor_get(v___x_796_, 0);
v_a_808_ = lean_ctor_get(v___x_796_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_796_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_inc(v_a_807_);
lean_dec(v___x_796_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_807_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6___boxed(lean_object* v_f_838_, lean_object* v_a_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
uint8_t v___y_26418__boxed_844_; lean_object* v_res_845_; 
v___y_26418__boxed_844_ = lean_unbox(v___y_841_);
v_res_845_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_f_838_, v_a_839_, v___y_840_, v___y_26418__boxed_844_, v___y_842_, v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_845_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_849_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__2));
v___x_850_ = lean_unsigned_to_nat(67u);
v___x_851_ = lean_unsigned_to_nat(35u);
v___x_852_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__1));
v___x_853_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__0));
v___x_854_ = l_mkPanicMessageWithDecl(v___x_853_, v___x_852_, v___x_851_, v___x_850_, v___x_849_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(lean_object* v_minIndex_855_, lean_object* v___x_856_, lean_object* v___x_857_, lean_object* v_start_858_, lean_object* v_xs_859_, lean_object* v___x_860_, lean_object* v_e_861_, lean_object* v_offset_862_, lean_object* v_a_863_, uint8_t v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
switch(lean_obj_tag(v_e_861_))
{
case 5:
{
lean_object* v_fn_867_; lean_object* v_arg_868_; lean_object* v___x_869_; 
v_fn_867_ = lean_ctor_get(v_e_861_, 0);
v_arg_868_ = lean_ctor_get(v_e_861_, 1);
lean_inc(v_offset_862_);
lean_inc_ref(v_fn_867_);
lean_inc_ref(v___x_856_);
v___x_869_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_855_, v___x_856_, v___x_857_, v_start_858_, v_xs_859_, v___x_860_, v_fn_867_, v_offset_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v_a_871_; lean_object* v_fst_872_; lean_object* v_snd_873_; lean_object* v___x_874_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
v_a_871_ = lean_ctor_get(v___x_869_, 1);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_869_, 2);
v_fst_872_ = lean_ctor_get(v_a_870_, 0);
lean_inc(v_fst_872_);
v_snd_873_ = lean_ctor_get(v_a_870_, 1);
lean_inc(v_snd_873_);
lean_dec(v_a_870_);
lean_inc_ref(v_arg_868_);
v___x_874_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_855_, v___x_856_, v___x_857_, v_start_858_, v_xs_859_, v___x_860_, v_arg_868_, v_offset_862_, v_snd_873_, v_a_864_, v_a_865_, v_a_871_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_900_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_a_876_ = lean_ctor_get(v___x_874_, 1);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_900_ == 0)
{
v___x_878_ = v___x_874_;
v_isShared_879_ = v_isSharedCheck_900_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_900_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_fst_880_; lean_object* v_snd_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_899_; 
v_fst_880_ = lean_ctor_get(v_a_875_, 0);
v_snd_881_ = lean_ctor_get(v_a_875_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_a_875_);
if (v_isSharedCheck_899_ == 0)
{
v___x_883_ = v_a_875_;
v_isShared_884_ = v_isSharedCheck_899_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_snd_881_);
lean_inc(v_fst_880_);
lean_dec(v_a_875_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_899_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
size_t v___x_885_; size_t v___x_886_; uint8_t v___x_887_; 
v___x_885_ = lean_ptr_addr(v_fn_867_);
v___x_886_ = lean_ptr_addr(v_fst_872_);
v___x_887_ = lean_usize_dec_eq(v___x_885_, v___x_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; 
lean_del_object(v___x_883_);
lean_del_object(v___x_878_);
lean_dec_ref_known(v_e_861_, 2);
v___x_888_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_fst_872_, v_fst_880_, v_snd_881_, v_a_864_, v_a_865_, v_a_876_);
return v___x_888_;
}
else
{
size_t v___x_889_; size_t v___x_890_; uint8_t v___x_891_; 
v___x_889_ = lean_ptr_addr(v_arg_868_);
v___x_890_ = lean_ptr_addr(v_fst_880_);
v___x_891_ = lean_usize_dec_eq(v___x_889_, v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
lean_del_object(v___x_883_);
lean_del_object(v___x_878_);
lean_dec_ref_known(v_e_861_, 2);
v___x_892_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_fst_872_, v_fst_880_, v_snd_881_, v_a_864_, v_a_865_, v_a_876_);
return v___x_892_;
}
else
{
lean_object* v___x_894_; 
lean_dec(v_fst_880_);
lean_dec(v_fst_872_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v_e_861_);
v___x_894_ = v___x_883_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_e_861_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_snd_881_);
v___x_894_ = v_reuseFailAlloc_898_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_894_);
v___x_896_ = v___x_878_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_a_876_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_872_);
lean_dec_ref_known(v_e_861_, 2);
return v___x_874_;
}
}
else
{
lean_dec_ref_known(v_e_861_, 2);
lean_dec(v_offset_862_);
lean_dec_ref(v___x_856_);
return v___x_869_;
}
}
case 6:
{
lean_object* v_binderName_901_; lean_object* v_binderType_902_; lean_object* v_body_903_; uint8_t v_binderInfo_904_; lean_object* v___x_905_; 
v_binderName_901_ = lean_ctor_get(v_e_861_, 0);
v_binderType_902_ = lean_ctor_get(v_e_861_, 1);
v_body_903_ = lean_ctor_get(v_e_861_, 2);
v_binderInfo_904_ = lean_ctor_get_uint8(v_e_861_, sizeof(void*)*3 + 8);
lean_inc(v_offset_862_);
lean_inc_ref(v_binderType_902_);
lean_inc_ref(v___x_856_);
v___x_905_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_855_, v___x_856_, v___x_857_, v_start_858_, v_xs_859_, v___x_860_, v_binderType_902_, v_offset_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v_a_907_; lean_object* v_fst_908_; lean_object* v_snd_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
v_a_907_ = lean_ctor_get(v___x_905_, 1);
lean_inc(v_a_907_);
lean_dec_ref_known(v___x_905_, 2);
v_fst_908_ = lean_ctor_get(v_a_906_, 0);
lean_inc(v_fst_908_);
v_snd_909_ = lean_ctor_get(v_a_906_, 1);
lean_inc(v_snd_909_);
lean_dec(v_a_906_);
v___x_910_ = lean_unsigned_to_nat(1u);
v___x_911_ = lean_nat_add(v_offset_862_, v___x_910_);
lean_dec(v_offset_862_);
lean_inc_ref(v_body_903_);
v___x_912_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_855_, v___x_856_, v___x_857_, v_start_858_, v_xs_859_, v___x_860_, v_body_903_, v___x_911_, v_snd_909_, v_a_864_, v_a_865_, v_a_907_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_938_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_a_914_ = lean_ctor_get(v___x_912_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_938_ == 0)
{
v___x_916_ = v___x_912_;
v_isShared_917_ = v_isSharedCheck_938_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_938_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v_fst_918_; lean_object* v_snd_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_937_; 
v_fst_918_ = lean_ctor_get(v_a_913_, 0);
v_snd_919_ = lean_ctor_get(v_a_913_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v_a_913_);
if (v_isSharedCheck_937_ == 0)
{
v___x_921_ = v_a_913_;
v_isShared_922_ = v_isSharedCheck_937_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_snd_919_);
lean_inc(v_fst_918_);
lean_dec(v_a_913_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_937_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
size_t v___x_923_; size_t v___x_924_; uint8_t v___x_925_; 
v___x_923_ = lean_ptr_addr(v_binderType_902_);
v___x_924_ = lean_ptr_addr(v_fst_908_);
v___x_925_ = lean_usize_dec_eq(v___x_923_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; 
lean_inc(v_binderName_901_);
lean_del_object(v___x_921_);
lean_del_object(v___x_916_);
lean_dec_ref_known(v_e_861_, 3);
v___x_926_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_binderName_901_, v_binderInfo_904_, v_fst_908_, v_fst_918_, v_snd_919_, v_a_864_, v_a_865_, v_a_914_);
return v___x_926_;
}
else
{
size_t v___x_927_; size_t v___x_928_; uint8_t v___x_929_; 
v___x_927_ = lean_ptr_addr(v_body_903_);
v___x_928_ = lean_ptr_addr(v_fst_918_);
v___x_929_ = lean_usize_dec_eq(v___x_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; 
lean_inc(v_binderName_901_);
lean_del_object(v___x_921_);
lean_del_object(v___x_916_);
lean_dec_ref_known(v_e_861_, 3);
v___x_930_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_binderName_901_, v_binderInfo_904_, v_fst_908_, v_fst_918_, v_snd_919_, v_a_864_, v_a_865_, v_a_914_);
return v___x_930_;
}
else
{
lean_object* v___x_932_; 
lean_dec(v_fst_918_);
lean_dec(v_fst_908_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v_e_861_);
v___x_932_ = v___x_921_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_e_861_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_snd_919_);
v___x_932_ = v_reuseFailAlloc_936_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_934_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_932_);
v___x_934_ = v___x_916_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_a_914_);
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
lean_dec(v_fst_908_);
lean_dec_ref_known(v_e_861_, 3);
return v___x_912_;
}
}
else
{
lean_dec_ref_known(v_e_861_, 3);
lean_dec(v_offset_862_);
lean_dec_ref(v___x_856_);
return v___x_905_;
}
}
case 7:
{
lean_object* v_binderName_939_; lean_object* v_binderType_940_; lean_object* v_body_941_; uint8_t v_binderInfo_942_; lean_object* v___x_943_; 
v_binderName_939_ = lean_ctor_get(v_e_861_, 0);
v_binderType_940_ = lean_ctor_get(v_e_861_, 1);
v_body_941_ = lean_ctor_get(v_e_861_, 2);
v_binderInfo_942_ = lean_ctor_get_uint8(v_e_861_, sizeof(void*)*3 + 8);
lean_inc(v_offset_862_);
lean_inc_ref(v_binderType_940_);
lean_inc_ref(v___x_856_);
v___x_943_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_855_, v___x_856_, v___x_857_, v_start_858_, v_xs_859_, v___x_860_, v_binderType_940_, v_offset_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v_a_945_; lean_object* v_fst_946_; lean_object* v_snd_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_944_);
v_a_945_ = lean_ctor_get(v___x_943_, 1);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_943_, 2);
v_fst_946_ = lean_ctor_get(v_a_944_, 0);
lean_inc(v_fst_946_);
v_snd_947_ = lean_ctor_get(v_a_944_, 1);
lean_inc(v_snd_947_);
lean_dec(v_a_944_);
v___x_948_ = lean_unsigned_to_nat(1u);
v___x_949_ = lean_nat_add(v_offset_862_, v___x_948_);
lean_dec(v_offset_862_);
lean_inc_ref(v_body_941_);
v___x_950_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_855_, v___x_856_, v___x_857_, v_start_858_, v_xs_859_, v___x_860_, v_body_941_, v___x_949_, v_snd_947_, v_a_864_, v_a_865_, v_a_945_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_976_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
v_a_952_ = lean_ctor_get(v___x_950_, 1);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_976_ == 0)
{
v___x_954_ = v___x_950_;
v_isShared_955_ = v_isSharedCheck_976_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_inc(v_a_951_);
lean_dec(v___x_950_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_976_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v_fst_956_; lean_object* v_snd_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_975_; 
v_fst_956_ = lean_ctor_get(v_a_951_, 0);
v_snd_957_ = lean_ctor_get(v_a_951_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_a_951_);
if (v_isSharedCheck_975_ == 0)
{
v___x_959_ = v_a_951_;
v_isShared_960_ = v_isSharedCheck_975_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_snd_957_);
lean_inc(v_fst_956_);
lean_dec(v_a_951_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_975_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
size_t v___x_961_; size_t v___x_962_; uint8_t v___x_963_; 
v___x_961_ = lean_ptr_addr(v_binderType_940_);
v___x_962_ = lean_ptr_addr(v_fst_946_);
v___x_963_ = lean_usize_dec_eq(v___x_961_, v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; 
lean_inc(v_binderName_939_);
lean_del_object(v___x_959_);
lean_del_object(v___x_954_);
lean_dec_ref_known(v_e_861_, 3);
v___x_964_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_binderName_939_, v_binderInfo_942_, v_fst_946_, v_fst_956_, v_snd_957_, v_a_864_, v_a_865_, v_a_952_);
return v___x_964_;
}
else
{
size_t v___x_965_; size_t v___x_966_; uint8_t v___x_967_; 
v___x_965_ = lean_ptr_addr(v_body_941_);
v___x_966_ = lean_ptr_addr(v_fst_956_);
v___x_967_ = lean_usize_dec_eq(v___x_965_, v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; 
lean_inc(v_binderName_939_);
lean_del_object(v___x_959_);
lean_del_object(v___x_954_);
lean_dec_ref_known(v_e_861_, 3);
v___x_968_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_binderName_939_, v_binderInfo_942_, v_fst_946_, v_fst_956_, v_snd_957_, v_a_864_, v_a_865_, v_a_952_);
return v___x_968_;
}
else
{
lean_object* v___x_970_; 
lean_dec(v_fst_956_);
lean_dec(v_fst_946_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v_e_861_);
v___x_970_ = v___x_959_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_e_861_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_snd_957_);
v___x_970_ = v_reuseFailAlloc_974_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_972_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_970_);
v___x_972_ = v___x_954_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_a_952_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_946_);
lean_dec_ref_known(v_e_861_, 3);
return v___x_950_;
}
}
else
{
lean_dec_ref_known(v_e_861_, 3);
lean_dec(v_offset_862_);
lean_dec_ref(v___x_856_);
return v___x_943_;
}
}
case 8:
{
lean_object* v_declName_977_; lean_object* v_type_978_; lean_object* v_value_979_; lean_object* v_body_980_; uint8_t v_nondep_981_; lean_object* v___x_982_; 
v_declName_977_ = lean_ctor_get(v_e_861_, 0);
v_type_978_ = lean_ctor_get(v_e_861_, 1);
v_value_979_ = lean_ctor_get(v_e_861_, 2);
v_body_980_ = lean_ctor_get(v_e_861_, 3);
v_nondep_981_ = lean_ctor_get_uint8(v_e_861_, sizeof(void*)*4 + 8);
lean_inc(v_offset_862_);
lean_inc_ref(v_type_978_);
lean_inc_ref(v___x_856_);
v___x_982_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_855_, v___x_856_, v___x_857_, v_start_858_, v_xs_859_, v___x_860_, v_type_978_, v_offset_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v_a_984_; lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v___x_987_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
v_a_984_ = lean_ctor_get(v___x_982_, 1);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_982_, 2);
v_fst_985_ = lean_ctor_get(v_a_983_, 0);
lean_inc(v_fst_985_);
v_snd_986_ = lean_ctor_get(v_a_983_, 1);
lean_inc(v_snd_986_);
lean_dec(v_a_983_);
lean_inc(v_offset_862_);
lean_inc_ref(v_value_979_);
lean_inc_ref(v___x_856_);
v___x_987_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_855_, v___x_856_, v___x_857_, v_start_858_, v_xs_859_, v___x_860_, v_value_979_, v_offset_862_, v_snd_986_, v_a_864_, v_a_865_, v_a_984_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v_a_989_; lean_object* v_fst_990_; lean_object* v_snd_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
v_a_989_ = lean_ctor_get(v___x_987_, 1);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_987_, 2);
v_fst_990_ = lean_ctor_get(v_a_988_, 0);
lean_inc(v_fst_990_);
v_snd_991_ = lean_ctor_get(v_a_988_, 1);
lean_inc(v_snd_991_);
lean_dec(v_a_988_);
v___x_992_ = lean_unsigned_to_nat(1u);
v___x_993_ = lean_nat_add(v_offset_862_, v___x_992_);
lean_dec(v_offset_862_);
lean_inc_ref(v_body_980_);
v___x_994_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_855_, v___x_856_, v___x_857_, v_start_858_, v_xs_859_, v___x_860_, v_body_980_, v___x_993_, v_snd_991_, v_a_864_, v_a_865_, v_a_989_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1024_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_a_996_ = lean_ctor_get(v___x_994_, 1);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_998_ = v___x_994_;
v_isShared_999_ = v_isSharedCheck_1024_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1024_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v_fst_1000_; lean_object* v_snd_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1023_; 
v_fst_1000_ = lean_ctor_get(v_a_995_, 0);
v_snd_1001_ = lean_ctor_get(v_a_995_, 1);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_a_995_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1003_ = v_a_995_;
v_isShared_1004_ = v_isSharedCheck_1023_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_snd_1001_);
lean_inc(v_fst_1000_);
lean_dec(v_a_995_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1023_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
size_t v___x_1005_; size_t v___x_1006_; uint8_t v___x_1007_; 
v___x_1005_ = lean_ptr_addr(v_type_978_);
v___x_1006_ = lean_ptr_addr(v_fst_985_);
v___x_1007_ = lean_usize_dec_eq(v___x_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
lean_inc(v_declName_977_);
lean_del_object(v___x_1003_);
lean_del_object(v___x_998_);
lean_dec_ref_known(v_e_861_, 4);
v___x_1008_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_977_, v_fst_985_, v_fst_990_, v_fst_1000_, v_nondep_981_, v_snd_1001_, v_a_864_, v_a_865_, v_a_996_);
return v___x_1008_;
}
else
{
size_t v___x_1009_; size_t v___x_1010_; uint8_t v___x_1011_; 
v___x_1009_ = lean_ptr_addr(v_value_979_);
v___x_1010_ = lean_ptr_addr(v_fst_990_);
v___x_1011_ = lean_usize_dec_eq(v___x_1009_, v___x_1010_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; 
lean_inc(v_declName_977_);
lean_del_object(v___x_1003_);
lean_del_object(v___x_998_);
lean_dec_ref_known(v_e_861_, 4);
v___x_1012_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_977_, v_fst_985_, v_fst_990_, v_fst_1000_, v_nondep_981_, v_snd_1001_, v_a_864_, v_a_865_, v_a_996_);
return v___x_1012_;
}
else
{
size_t v___x_1013_; size_t v___x_1014_; uint8_t v___x_1015_; 
v___x_1013_ = lean_ptr_addr(v_body_980_);
v___x_1014_ = lean_ptr_addr(v_fst_1000_);
v___x_1015_ = lean_usize_dec_eq(v___x_1013_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; 
lean_inc(v_declName_977_);
lean_del_object(v___x_1003_);
lean_del_object(v___x_998_);
lean_dec_ref_known(v_e_861_, 4);
v___x_1016_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_977_, v_fst_985_, v_fst_990_, v_fst_1000_, v_nondep_981_, v_snd_1001_, v_a_864_, v_a_865_, v_a_996_);
return v___x_1016_;
}
else
{
lean_object* v___x_1018_; 
lean_dec(v_fst_1000_);
lean_dec(v_fst_990_);
lean_dec(v_fst_985_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v_e_861_);
v___x_1018_ = v___x_1003_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_e_861_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_snd_1001_);
v___x_1018_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1020_; 
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1018_);
v___x_1020_ = v___x_998_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_a_996_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
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
lean_dec(v_fst_990_);
lean_dec(v_fst_985_);
lean_dec_ref_known(v_e_861_, 4);
return v___x_994_;
}
}
else
{
lean_dec(v_fst_985_);
lean_dec_ref_known(v_e_861_, 4);
lean_dec(v_offset_862_);
lean_dec_ref(v___x_856_);
return v___x_987_;
}
}
else
{
lean_dec_ref_known(v_e_861_, 4);
lean_dec(v_offset_862_);
lean_dec_ref(v___x_856_);
return v___x_982_;
}
}
case 10:
{
lean_object* v_data_1025_; lean_object* v_expr_1026_; lean_object* v___x_1027_; 
v_data_1025_ = lean_ctor_get(v_e_861_, 0);
v_expr_1026_ = lean_ctor_get(v_e_861_, 1);
lean_inc_ref(v_expr_1026_);
v___x_1027_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_855_, v___x_856_, v___x_857_, v_start_858_, v_xs_859_, v___x_860_, v_expr_1026_, v_offset_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1049_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_a_1029_ = lean_ctor_get(v___x_1027_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1031_ = v___x_1027_;
v_isShared_1032_ = v_isSharedCheck_1049_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1049_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v_fst_1033_; lean_object* v_snd_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1048_; 
v_fst_1033_ = lean_ctor_get(v_a_1028_, 0);
v_snd_1034_ = lean_ctor_get(v_a_1028_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_a_1028_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1036_ = v_a_1028_;
v_isShared_1037_ = v_isSharedCheck_1048_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_snd_1034_);
lean_inc(v_fst_1033_);
lean_dec(v_a_1028_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1048_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
size_t v___x_1038_; size_t v___x_1039_; uint8_t v___x_1040_; 
v___x_1038_ = lean_ptr_addr(v_expr_1026_);
v___x_1039_ = lean_ptr_addr(v_fst_1033_);
v___x_1040_ = lean_usize_dec_eq(v___x_1038_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_inc(v_data_1025_);
lean_del_object(v___x_1036_);
lean_del_object(v___x_1031_);
lean_dec_ref_known(v_e_861_, 2);
v___x_1041_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(v_data_1025_, v_fst_1033_, v_snd_1034_, v_a_864_, v_a_865_, v_a_1029_);
return v___x_1041_;
}
else
{
lean_object* v___x_1043_; 
lean_dec(v_fst_1033_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v_e_861_);
v___x_1043_ = v___x_1036_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_e_861_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_snd_1034_);
v___x_1043_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1045_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v___x_1043_);
v___x_1045_ = v___x_1031_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_a_1029_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_861_, 2);
return v___x_1027_;
}
}
case 11:
{
lean_object* v_typeName_1050_; lean_object* v_idx_1051_; lean_object* v_struct_1052_; lean_object* v___x_1053_; 
v_typeName_1050_ = lean_ctor_get(v_e_861_, 0);
v_idx_1051_ = lean_ctor_get(v_e_861_, 1);
v_struct_1052_ = lean_ctor_get(v_e_861_, 2);
lean_inc_ref(v_struct_1052_);
v___x_1053_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_855_, v___x_856_, v___x_857_, v_start_858_, v_xs_859_, v___x_860_, v_struct_1052_, v_offset_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1075_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_a_1055_ = lean_ctor_get(v___x_1053_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1057_ = v___x_1053_;
v_isShared_1058_ = v_isSharedCheck_1075_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1075_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v_fst_1059_; lean_object* v_snd_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1074_; 
v_fst_1059_ = lean_ctor_get(v_a_1054_, 0);
v_snd_1060_ = lean_ctor_get(v_a_1054_, 1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_a_1054_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1062_ = v_a_1054_;
v_isShared_1063_ = v_isSharedCheck_1074_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_snd_1060_);
lean_inc(v_fst_1059_);
lean_dec(v_a_1054_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1074_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
size_t v___x_1064_; size_t v___x_1065_; uint8_t v___x_1066_; 
v___x_1064_ = lean_ptr_addr(v_struct_1052_);
v___x_1065_ = lean_ptr_addr(v_fst_1059_);
v___x_1066_ = lean_usize_dec_eq(v___x_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
lean_inc(v_idx_1051_);
lean_inc(v_typeName_1050_);
lean_del_object(v___x_1062_);
lean_del_object(v___x_1057_);
lean_dec_ref_known(v_e_861_, 3);
v___x_1067_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(v_typeName_1050_, v_idx_1051_, v_fst_1059_, v_snd_1060_, v_a_864_, v_a_865_, v_a_1055_);
return v___x_1067_;
}
else
{
lean_object* v___x_1069_; 
lean_dec(v_fst_1059_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v_e_861_);
v___x_1069_ = v___x_1062_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_e_861_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_snd_1060_);
v___x_1069_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1071_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1069_);
v___x_1071_ = v___x_1057_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_a_1055_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_861_, 3);
return v___x_1053_;
}
}
default: 
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec(v_offset_862_);
lean_dec_ref(v_e_861_);
lean_dec_ref(v___x_856_);
v___x_1076_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3);
v___x_1077_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(v___x_1076_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
return v___x_1077_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(lean_object* v_minIndex_1078_, lean_object* v___x_1079_, lean_object* v___x_1080_, lean_object* v_start_1081_, lean_object* v_xs_1082_, lean_object* v___x_1083_, lean_object* v_e_1084_, lean_object* v_offset_1085_, lean_object* v_a_1086_, uint8_t v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v_key_1090_; lean_object* v_a_1092_; lean_object* v___y_1106_; lean_object* v___y_1111_; lean_object* v___x_1116_; 
lean_inc(v_offset_1085_);
lean_inc_ref(v_e_1084_);
v_key_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1090_, 0, v_e_1084_);
lean_ctor_set(v_key_1090_, 1, v_offset_1085_);
v___x_1116_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_a_1086_, v_key_1090_);
if (lean_obj_tag(v___x_1116_) == 1)
{
lean_object* v_val_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec_ref_known(v_key_1090_, 2);
lean_dec(v_offset_1085_);
lean_dec_ref(v_e_1084_);
lean_dec_ref(v___x_1079_);
v_val_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_val_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v_val_1117_);
lean_ctor_set(v___x_1118_, 1, v_a_1086_);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set(v___x_1119_, 1, v_a_1089_);
return v___x_1119_;
}
else
{
lean_dec(v___x_1116_);
switch(lean_obj_tag(v_e_1084_))
{
case 1:
{
lean_object* v_fvarId_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_dec_ref(v___x_1079_);
v_fvarId_1120_ = lean_ctor_get(v_e_1084_, 0);
v___x_1121_ = lean_unsigned_to_nat(0u);
v___x_1122_ = lean_unsigned_to_nat(1u);
v___x_1123_ = lean_nat_sub(v___x_1080_, v___x_1122_);
v___x_1124_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_1081_, v_xs_1082_, v_fvarId_1120_, v___x_1121_, v___x_1123_);
if (lean_obj_tag(v___x_1124_) == 1)
{
lean_object* v_val_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec_ref_known(v_e_1084_, 1);
v_val_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_val_1125_);
lean_dec_ref_known(v___x_1124_, 1);
v___x_1126_ = lean_nat_add(v_offset_1085_, v_val_1125_);
lean_dec(v_val_1125_);
lean_dec(v_offset_1085_);
v___x_1127_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v___x_1126_, v_a_1089_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v_a_1129_; lean_object* v___x_1130_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
v_a_1129_ = lean_ctor_get(v___x_1127_, 1);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1127_, 2);
v___x_1130_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1090_, v_a_1128_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1129_);
return v___x_1130_;
}
else
{
lean_object* v_a_1131_; lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec_ref_known(v_key_1090_, 2);
lean_dec_ref(v_a_1086_);
v_a_1131_ = lean_ctor_get(v___x_1127_, 0);
v_a_1132_ = lean_ctor_get(v___x_1127_, 1);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1127_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_inc(v_a_1131_);
lean_dec(v___x_1127_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1131_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_a_1132_);
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
else
{
lean_object* v___x_1140_; 
lean_dec(v___x_1124_);
lean_dec(v_offset_1085_);
v___x_1140_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1090_, v_e_1084_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
return v___x_1140_;
}
}
case 9:
{
lean_object* v___x_1141_; 
lean_dec(v_offset_1085_);
lean_dec_ref(v___x_1079_);
v___x_1141_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1090_, v_e_1084_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
return v___x_1141_;
}
case 2:
{
lean_object* v___x_1142_; 
lean_dec(v_offset_1085_);
lean_dec_ref(v___x_1079_);
v___x_1142_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1090_, v_e_1084_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
return v___x_1142_;
}
case 0:
{
lean_object* v___x_1143_; 
lean_dec(v_offset_1085_);
lean_dec_ref(v___x_1079_);
v___x_1143_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1090_, v_e_1084_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
return v___x_1143_;
}
case 4:
{
lean_object* v___x_1144_; 
lean_dec(v_offset_1085_);
lean_dec_ref(v___x_1079_);
v___x_1144_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1090_, v_e_1084_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
return v___x_1144_;
}
case 3:
{
lean_object* v___x_1145_; 
lean_dec(v_offset_1085_);
lean_dec_ref(v___x_1079_);
v___x_1145_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1090_, v_e_1084_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
return v___x_1145_;
}
default: 
{
uint8_t v___x_1146_; 
v___x_1146_ = l_Lean_Expr_hasFVar(v_e_1084_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
lean_dec(v_offset_1085_);
lean_dec_ref(v___x_1079_);
v___x_1147_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1090_, v_e_1084_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v___x_1083_, v_e_1084_);
if (lean_obj_tag(v___x_1148_) == 1)
{
lean_object* v_val_1149_; 
v_val_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_val_1149_);
lean_dec_ref_known(v___x_1148_, 1);
if (lean_obj_tag(v_val_1149_) == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1151_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v___x_1150_);
v___y_1111_ = v___x_1151_;
goto v___jp_1110_;
}
else
{
lean_object* v_val_1152_; 
v_val_1152_ = lean_ctor_get(v_val_1149_, 0);
lean_inc(v_val_1152_);
lean_dec_ref_known(v_val_1149_, 1);
v___y_1111_ = v_val_1152_;
goto v___jp_1110_;
}
}
else
{
lean_dec(v___x_1148_);
v_a_1092_ = v_a_1089_;
goto v___jp_1091_;
}
}
}
}
}
v___jp_1091_:
{
switch(lean_obj_tag(v_e_1084_))
{
case 9:
{
lean_object* v___x_1093_; 
lean_dec(v_offset_1085_);
lean_dec_ref(v___x_1079_);
v___x_1093_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1090_, v_e_1084_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1092_);
return v___x_1093_;
}
case 2:
{
lean_object* v___x_1094_; 
lean_dec(v_offset_1085_);
lean_dec_ref(v___x_1079_);
v___x_1094_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1090_, v_e_1084_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1092_);
return v___x_1094_;
}
case 0:
{
lean_object* v___x_1095_; 
lean_dec(v_offset_1085_);
lean_dec_ref(v___x_1079_);
v___x_1095_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1090_, v_e_1084_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1092_);
return v___x_1095_;
}
case 1:
{
lean_object* v___x_1096_; 
lean_dec(v_offset_1085_);
lean_dec_ref(v___x_1079_);
v___x_1096_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1090_, v_e_1084_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1092_);
return v___x_1096_;
}
case 4:
{
lean_object* v___x_1097_; 
lean_dec(v_offset_1085_);
lean_dec_ref(v___x_1079_);
v___x_1097_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1090_, v_e_1084_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1092_);
return v___x_1097_;
}
case 3:
{
lean_object* v___x_1098_; 
lean_dec(v_offset_1085_);
lean_dec_ref(v___x_1079_);
v___x_1098_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1090_, v_e_1084_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1092_);
return v___x_1098_;
}
default: 
{
lean_object* v___x_1099_; 
v___x_1099_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v_minIndex_1078_, v___x_1079_, v___x_1080_, v_start_1081_, v_xs_1082_, v___x_1083_, v_e_1084_, v_offset_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1092_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v_a_1101_; lean_object* v_fst_1102_; lean_object* v_snd_1103_; lean_object* v___x_1104_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
v_a_1101_ = lean_ctor_get(v___x_1099_, 1);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1099_, 2);
v_fst_1102_ = lean_ctor_get(v_a_1100_, 0);
lean_inc(v_fst_1102_);
v_snd_1103_ = lean_ctor_get(v_a_1100_, 1);
lean_inc(v_snd_1103_);
lean_dec(v_a_1100_);
v___x_1104_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1090_, v_fst_1102_, v_snd_1103_, v_a_1087_, v_a_1088_, v_a_1101_);
return v___x_1104_;
}
else
{
lean_dec_ref_known(v_key_1090_, 2);
return v___x_1099_;
}
}
}
}
v___jp_1105_:
{
lean_object* v_maxIndex_1107_; uint8_t v___x_1108_; 
v_maxIndex_1107_ = l_Lean_LocalDecl_index(v___y_1106_);
lean_dec_ref(v___y_1106_);
v___x_1108_ = lean_nat_dec_lt(v_maxIndex_1107_, v_minIndex_1078_);
lean_dec(v_maxIndex_1107_);
if (v___x_1108_ == 0)
{
v_a_1092_ = v_a_1089_;
goto v___jp_1091_;
}
else
{
lean_object* v___x_1109_; 
lean_dec(v_offset_1085_);
lean_dec_ref(v___x_1079_);
v___x_1109_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1090_, v_e_1084_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
return v___x_1109_;
}
}
v___jp_1110_:
{
lean_object* v___x_1112_; 
lean_inc_ref(v___x_1079_);
v___x_1112_ = lean_local_ctx_find(v___x_1079_, v___y_1111_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1114_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1113_);
v___y_1106_ = v___x_1114_;
goto v___jp_1105_;
}
else
{
lean_object* v_val_1115_; 
v_val_1115_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_val_1115_);
lean_dec_ref_known(v___x_1112_, 1);
v___y_1106_ = v_val_1115_;
goto v___jp_1105_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5___boxed(lean_object* v_minIndex_1153_, lean_object* v___x_1154_, lean_object* v___x_1155_, lean_object* v_start_1156_, lean_object* v_xs_1157_, lean_object* v___x_1158_, lean_object* v_e_1159_, lean_object* v_offset_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
uint8_t v_a_boxed_1165_; lean_object* v_res_1166_; 
v_a_boxed_1165_ = lean_unbox(v_a_1162_);
v_res_1166_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_1153_, v___x_1154_, v___x_1155_, v_start_1156_, v_xs_1157_, v___x_1158_, v_e_1159_, v_offset_1160_, v_a_1161_, v_a_boxed_1165_, v_a_1163_, v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_xs_1157_);
lean_dec(v_start_1156_);
lean_dec(v___x_1155_);
lean_dec(v_minIndex_1153_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___boxed(lean_object* v_minIndex_1167_, lean_object* v___x_1168_, lean_object* v___x_1169_, lean_object* v_start_1170_, lean_object* v_xs_1171_, lean_object* v___x_1172_, lean_object* v_e_1173_, lean_object* v_offset_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
uint8_t v_a_boxed_1179_; lean_object* v_res_1180_; 
v_a_boxed_1179_ = lean_unbox(v_a_1176_);
v_res_1180_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v_minIndex_1167_, v___x_1168_, v___x_1169_, v_start_1170_, v_xs_1171_, v___x_1172_, v_e_1173_, v_offset_1174_, v_a_1175_, v_a_boxed_1179_, v_a_1177_, v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec_ref(v___x_1172_);
lean_dec_ref(v_xs_1171_);
lean_dec(v_start_1170_);
lean_dec(v___x_1169_);
lean_dec(v_minIndex_1167_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___lam__0(lean_object* v_e_1181_, lean_object* v_lctx_1182_, lean_object* v___x_1183_, lean_object* v_start_1184_, lean_object* v_xs_1185_, lean_object* v_maxFVar_1186_, uint8_t v_debug_1187_, lean_object* v___x_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1238_; lean_object* v___x_1258_; 
lean_inc_ref(v_lctx_1182_);
v___x_1258_ = lean_local_ctx_find(v_lctx_1182_, v___x_1188_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1260_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1259_);
v___y_1238_ = v___x_1260_;
goto v___jp_1237_;
}
else
{
lean_object* v_val_1261_; 
v_val_1261_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_val_1261_);
lean_dec_ref_known(v___x_1258_, 1);
v___y_1238_ = v_val_1261_;
goto v___jp_1237_;
}
v___jp_1191_:
{
switch(lean_obj_tag(v_e_1181_))
{
case 9:
{
lean_object* v___x_1194_; 
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v_lctx_1182_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v_e_1181_);
lean_ctor_set(v___x_1194_, 1, v___y_1190_);
return v___x_1194_;
}
case 2:
{
lean_object* v___x_1195_; 
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v_lctx_1182_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v_e_1181_);
lean_ctor_set(v___x_1195_, 1, v___y_1190_);
return v___x_1195_;
}
case 0:
{
lean_object* v___x_1196_; 
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v_lctx_1182_);
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v_e_1181_);
lean_ctor_set(v___x_1196_, 1, v___y_1190_);
return v___x_1196_;
}
case 1:
{
lean_object* v___x_1197_; 
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v_lctx_1182_);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v_e_1181_);
lean_ctor_set(v___x_1197_, 1, v___y_1190_);
return v___x_1197_;
}
case 4:
{
lean_object* v___x_1198_; 
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v_lctx_1182_);
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v_e_1181_);
lean_ctor_set(v___x_1198_, 1, v___y_1190_);
return v___x_1198_;
}
case 3:
{
lean_object* v___x_1199_; 
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v_lctx_1182_);
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v_e_1181_);
lean_ctor_set(v___x_1199_, 1, v___y_1190_);
return v___x_1199_;
}
default: 
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2);
lean_inc(v___y_1193_);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___y_1193_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v___y_1192_, v_lctx_1182_, v___x_1183_, v_start_1184_, v_xs_1185_, v_maxFVar_1186_, v_e_1181_, v___y_1193_, v___x_1201_, v_debug_1187_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1192_);
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
v___x_1227_ = lean_nat_dec_lt(v_maxIndex_1226_, v___y_1223_);
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
lean_dec_ref(v_lctx_1182_);
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_e_1181_);
lean_ctor_set(v___x_1228_, 1, v___y_1190_);
return v___x_1228_;
}
}
v___jp_1229_:
{
lean_object* v___x_1233_; 
lean_inc_ref(v_lctx_1182_);
v___x_1233_ = lean_local_ctx_find(v_lctx_1182_, v___y_1232_);
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
switch(lean_obj_tag(v_e_1181_))
{
case 1:
{
lean_object* v_fvarId_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec_ref(v___y_1238_);
lean_dec_ref(v_lctx_1182_);
v_fvarId_1240_ = lean_ctor_get(v_e_1181_, 0);
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = lean_nat_sub(v___x_1183_, v___x_1241_);
v___x_1243_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_1184_, v_xs_1185_, v_fvarId_1240_, v___x_1239_, v___x_1242_);
if (lean_obj_tag(v___x_1243_) == 1)
{
lean_object* v_val_1244_; lean_object* v___x_1245_; 
lean_dec_ref_known(v_e_1181_, 1);
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
lean_ctor_set(v___x_1246_, 0, v_e_1181_);
lean_ctor_set(v___x_1246_, 1, v___y_1190_);
return v___x_1246_;
}
}
case 9:
{
lean_object* v___x_1247_; 
lean_dec_ref(v___y_1238_);
lean_dec_ref(v_lctx_1182_);
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_e_1181_);
lean_ctor_set(v___x_1247_, 1, v___y_1190_);
return v___x_1247_;
}
case 2:
{
lean_object* v___x_1248_; 
lean_dec_ref(v___y_1238_);
lean_dec_ref(v_lctx_1182_);
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v_e_1181_);
lean_ctor_set(v___x_1248_, 1, v___y_1190_);
return v___x_1248_;
}
case 0:
{
lean_object* v___x_1249_; 
lean_dec_ref(v___y_1238_);
lean_dec_ref(v_lctx_1182_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v_e_1181_);
lean_ctor_set(v___x_1249_, 1, v___y_1190_);
return v___x_1249_;
}
case 4:
{
lean_object* v___x_1250_; 
lean_dec_ref(v___y_1238_);
lean_dec_ref(v_lctx_1182_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v_e_1181_);
lean_ctor_set(v___x_1250_, 1, v___y_1190_);
return v___x_1250_;
}
case 3:
{
lean_object* v___x_1251_; 
lean_dec_ref(v___y_1238_);
lean_dec_ref(v_lctx_1182_);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_e_1181_);
lean_ctor_set(v___x_1251_, 1, v___y_1190_);
return v___x_1251_;
}
default: 
{
lean_object* v_minIndex_1252_; lean_object* v___x_1253_; 
v_minIndex_1252_ = l_Lean_LocalDecl_index(v___y_1238_);
lean_dec_ref(v___y_1238_);
v___x_1253_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_maxFVar_1186_, v_e_1181_);
if (lean_obj_tag(v___x_1253_) == 1)
{
lean_object* v_val_1254_; 
v_val_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_val_1254_);
lean_dec_ref_known(v___x_1253_, 1);
if (lean_obj_tag(v_val_1254_) == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1256_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v___x_1255_);
v___y_1230_ = v_minIndex_1252_;
v___y_1231_ = v___x_1239_;
v___y_1232_ = v___x_1256_;
goto v___jp_1229_;
}
else
{
lean_object* v_val_1257_; 
v_val_1257_ = lean_ctor_get(v_val_1254_, 0);
lean_inc(v_val_1257_);
lean_dec_ref_known(v_val_1254_, 1);
v___y_1230_ = v_minIndex_1252_;
v___y_1231_ = v___x_1239_;
v___y_1232_ = v_val_1257_;
goto v___jp_1229_;
}
}
else
{
lean_dec(v___x_1253_);
v___y_1192_ = v_minIndex_1252_;
v___y_1193_ = v___x_1239_;
goto v___jp_1191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___lam__0___boxed(lean_object* v_e_1262_, lean_object* v_lctx_1263_, lean_object* v___x_1264_, lean_object* v_start_1265_, lean_object* v_xs_1266_, lean_object* v_maxFVar_1267_, lean_object* v_debug_1268_, lean_object* v___x_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
uint8_t v_debug_boxed_1272_; lean_object* v_res_1273_; 
v_debug_boxed_1272_ = lean_unbox(v_debug_1268_);
v_res_1273_ = l_Lean_Meta_Sym_abstractFVarsRange___lam__0(v_e_1262_, v_lctx_1263_, v___x_1264_, v_start_1265_, v_xs_1266_, v_maxFVar_1267_, v_debug_boxed_1272_, v___x_1269_, v___y_1270_, v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec_ref(v_maxFVar_1267_);
lean_dec_ref(v_xs_1266_);
lean_dec(v_start_1265_);
lean_dec(v___x_1264_);
return v_res_1273_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_abstractFVarsRange___closed__2(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1276_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__2));
v___x_1277_ = lean_unsigned_to_nat(16u);
v___x_1278_ = lean_unsigned_to_nat(62u);
v___x_1279_ = ((lean_object*)(l_Lean_Meta_Sym_abstractFVarsRange___closed__1));
v___x_1280_ = ((lean_object*)(l_Lean_Meta_Sym_abstractFVarsRange___closed__0));
v___x_1281_ = l_mkPanicMessageWithDecl(v___x_1280_, v___x_1279_, v___x_1278_, v___x_1277_, v___x_1276_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange(lean_object* v_e_1282_, lean_object* v_start_1283_, lean_object* v_xs_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
uint8_t v___x_1292_; 
v___x_1292_ = l_Lean_Expr_hasFVar(v_e_1282_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
lean_dec_ref(v_xs_1284_);
lean_dec(v_start_1283_);
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v_e_1282_);
return v___x_1293_;
}
else
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = lean_array_get_size(v_xs_1284_);
v___x_1295_ = lean_nat_dec_lt(v_start_1283_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; 
lean_dec_ref(v_xs_1284_);
lean_dec(v_start_1283_);
v___x_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1296_, 0, v_e_1282_);
return v___x_1296_;
}
else
{
lean_object* v_lctx_1297_; uint8_t v___x_1298_; lean_object* v___x_1299_; lean_object* v_maxFVar_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v_debug_1304_; lean_object* v___x_1305_; lean_object* v___f_1306_; lean_object* v___x_1307_; lean_object* v_env_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_lctx_1297_ = lean_ctor_get(v_a_1287_, 2);
v___x_1298_ = 0;
v___x_1299_ = lean_st_ref_get(v_a_1286_);
v_maxFVar_1300_ = lean_ctor_get(v___x_1299_, 1);
lean_inc_ref(v_maxFVar_1300_);
lean_dec(v___x_1299_);
v___x_1301_ = lean_array_fget_borrowed(v_xs_1284_, v_start_1283_);
v___x_1302_ = l_Lean_Expr_fvarId_x21(v___x_1301_);
v___x_1303_ = lean_st_ref_get(v_a_1286_);
v_debug_1304_ = lean_ctor_get_uint8(v___x_1303_, sizeof(void*)*12);
lean_dec(v___x_1303_);
v___x_1305_ = lean_box(v_debug_1304_);
lean_inc_ref(v_lctx_1297_);
v___f_1306_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_abstractFVarsRange___lam__0___boxed), 10, 8);
lean_closure_set(v___f_1306_, 0, v_e_1282_);
lean_closure_set(v___f_1306_, 1, v_lctx_1297_);
lean_closure_set(v___f_1306_, 2, v___x_1294_);
lean_closure_set(v___f_1306_, 3, v_start_1283_);
lean_closure_set(v___f_1306_, 4, v_xs_1284_);
lean_closure_set(v___f_1306_, 5, v_maxFVar_1300_);
lean_closure_set(v___f_1306_, 6, v___x_1305_);
lean_closure_set(v___f_1306_, 7, v___x_1302_);
v___x_1307_ = lean_st_ref_get(v_a_1290_);
v_env_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc_ref(v_env_1308_);
lean_dec(v___x_1307_);
v___x_1309_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1309_, 0, v_env_1308_);
lean_ctor_set_uint8(v___x_1309_, sizeof(void*)*1, v___x_1298_);
lean_ctor_set_uint8(v___x_1309_, sizeof(void*)*1 + 1, v___x_1298_);
v___x_1310_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1306_, v___x_1309_, v_a_1286_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1321_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1321_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1321_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
if (lean_obj_tag(v_a_1311_) == 0)
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec_ref_known(v_a_1311_, 1);
lean_del_object(v___x_1313_);
v___x_1315_ = lean_obj_once(&l_Lean_Meta_Sym_abstractFVarsRange___closed__2, &l_Lean_Meta_Sym_abstractFVarsRange___closed__2_once, _init_l_Lean_Meta_Sym_abstractFVarsRange___closed__2);
v___x_1316_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v___x_1315_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
return v___x_1316_;
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; 
v_a_1317_ = lean_ctor_get(v_a_1311_, 0);
lean_inc(v_a_1317_);
lean_dec_ref_known(v_a_1311_, 1);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v_a_1317_);
v___x_1319_ = v___x_1313_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
v_a_1322_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1310_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1310_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
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
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___boxed(lean_object* v_e_1330_, lean_object* v_start_1331_, lean_object* v_xs_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1330_, v_start_1331_, v_xs_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(lean_object* v_00_u03b2_1341_, lean_object* v_x_1342_, lean_object* v_x_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_x_1342_, v_x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___boxed(lean_object* v_00_u03b2_1345_, lean_object* v_x_1346_, lean_object* v_x_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(v_00_u03b2_1345_, v_x_1346_, v_x_1347_);
lean_dec_ref(v_x_1347_);
lean_dec_ref(v_x_1346_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2(lean_object* v_00_u03b2_1349_, lean_object* v_x_1350_, size_t v_x_1351_, lean_object* v_x_1352_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_1350_, v_x_1351_, v_x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1354_, lean_object* v_x_1355_, lean_object* v_x_1356_, lean_object* v_x_1357_){
_start:
{
size_t v_x_27503__boxed_1358_; lean_object* v_res_1359_; 
v_x_27503__boxed_1358_ = lean_unbox_usize(v_x_1356_);
lean_dec(v_x_1356_);
v_res_1359_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2(v_00_u03b2_1354_, v_x_1355_, v_x_27503__boxed_1358_, v_x_1357_);
lean_dec_ref(v_x_1357_);
lean_dec_ref(v_x_1355_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_1360_, lean_object* v_keys_1361_, lean_object* v_vals_1362_, lean_object* v_heq_1363_, lean_object* v_i_1364_, lean_object* v_k_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_keys_1361_, v_vals_1362_, v_i_1364_, v_k_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1367_, lean_object* v_keys_1368_, lean_object* v_vals_1369_, lean_object* v_heq_1370_, lean_object* v_i_1371_, lean_object* v_k_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5(v_00_u03b2_1367_, v_keys_1368_, v_vals_1369_, v_heq_1370_, v_i_1371_, v_k_1372_);
lean_dec_ref(v_k_1372_);
lean_dec_ref(v_vals_1369_);
lean_dec_ref(v_keys_1368_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_1374_, lean_object* v_m_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_m_1375_, v_a_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1378_, lean_object* v_m_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8(v_00_u03b2_1378_, v_m_1379_, v_a_1380_);
lean_dec_ref(v_a_1380_);
lean_dec_ref(v_m_1379_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16(lean_object* v_00_u03b2_1382_, lean_object* v_a_1383_, lean_object* v_x_1384_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_a_1383_, v_x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___boxed(lean_object* v_00_u03b2_1386_, lean_object* v_a_1387_, lean_object* v_x_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16(v_00_u03b2_1386_, v_a_1387_, v_x_1388_);
lean_dec(v_x_1388_);
lean_dec_ref(v_a_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___redArg(lean_object* v_xs_1390_, lean_object* v_fvarId_1391_, lean_object* v_bidx_1392_, lean_object* v_i_1393_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1394_ = lean_array_fget_borrowed(v_xs_1390_, v_i_1393_);
v___x_1395_ = l_Lean_Expr_fvarId_x21(v___x_1394_);
v___x_1396_ = l_Lean_instBEqFVarId_beq(v___x_1395_, v_fvarId_1391_);
lean_dec(v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = lean_nat_dec_lt(v___x_1397_, v_i_1393_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; 
lean_dec(v_i_1393_);
lean_dec(v_bidx_1392_);
v___x_1399_ = lean_box(0);
return v___x_1399_;
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = lean_unsigned_to_nat(1u);
v___x_1401_ = lean_nat_add(v_bidx_1392_, v___x_1400_);
lean_dec(v_bidx_1392_);
v___x_1402_ = lean_nat_sub(v_i_1393_, v___x_1400_);
lean_dec(v_i_1393_);
v_bidx_1392_ = v___x_1401_;
v_i_1393_ = v___x_1402_;
goto _start;
}
}
else
{
lean_object* v___x_1404_; 
lean_dec(v_i_1393_);
v___x_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1404_, 0, v_bidx_1392_);
return v___x_1404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___redArg___boxed(lean_object* v_xs_1405_, lean_object* v_fvarId_1406_, lean_object* v_bidx_1407_, lean_object* v_i_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___redArg(v_xs_1405_, v_fvarId_1406_, v_bidx_1407_, v_i_1408_);
lean_dec(v_fvarId_1406_);
lean_dec_ref(v_xs_1405_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go(lean_object* v_n_1410_, lean_object* v_xs_1411_, lean_object* v_this_1412_, lean_object* v_fvarId_1413_, lean_object* v_bidx_1414_, lean_object* v_i_1415_, lean_object* v_h_1416_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___redArg(v_xs_1411_, v_fvarId_1413_, v_bidx_1414_, v_i_1415_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___boxed(lean_object* v_n_1418_, lean_object* v_xs_1419_, lean_object* v_this_1420_, lean_object* v_fvarId_1421_, lean_object* v_bidx_1422_, lean_object* v_i_1423_, lean_object* v_h_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go(v_n_1418_, v_xs_1419_, v_this_1420_, v_fvarId_1421_, v_bidx_1422_, v_i_1423_, v_h_1424_);
lean_dec(v_fvarId_1421_);
lean_dec_ref(v_xs_1419_);
lean_dec(v_n_1418_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0(lean_object* v_minIndex_1426_, lean_object* v___x_1427_, lean_object* v___y_1428_, lean_object* v_n_1429_, lean_object* v_xs_1430_, lean_object* v___x_1431_, lean_object* v_e_1432_, lean_object* v_offset_1433_, lean_object* v_a_1434_, uint8_t v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
switch(lean_obj_tag(v_e_1432_))
{
case 5:
{
lean_object* v_fn_1438_; lean_object* v_arg_1439_; lean_object* v___x_1440_; 
v_fn_1438_ = lean_ctor_get(v_e_1432_, 0);
v_arg_1439_ = lean_ctor_get(v_e_1432_, 1);
lean_inc(v_offset_1433_);
lean_inc_ref(v_fn_1438_);
lean_inc_ref(v___x_1427_);
v___x_1440_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1426_, v___x_1427_, v___y_1428_, v_n_1429_, v_xs_1430_, v___x_1431_, v_fn_1438_, v_offset_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v_a_1442_; lean_object* v_fst_1443_; lean_object* v_snd_1444_; lean_object* v___x_1445_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
v_a_1442_ = lean_ctor_get(v___x_1440_, 1);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1440_, 2);
v_fst_1443_ = lean_ctor_get(v_a_1441_, 0);
lean_inc(v_fst_1443_);
v_snd_1444_ = lean_ctor_get(v_a_1441_, 1);
lean_inc(v_snd_1444_);
lean_dec(v_a_1441_);
lean_inc_ref(v_arg_1439_);
v___x_1445_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1426_, v___x_1427_, v___y_1428_, v_n_1429_, v_xs_1430_, v___x_1431_, v_arg_1439_, v_offset_1433_, v_snd_1444_, v_a_1435_, v_a_1436_, v_a_1442_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1471_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
v_a_1447_ = lean_ctor_get(v___x_1445_, 1);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1449_ = v___x_1445_;
v_isShared_1450_ = v_isSharedCheck_1471_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_inc(v_a_1446_);
lean_dec(v___x_1445_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1471_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v_fst_1451_; lean_object* v_snd_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1470_; 
v_fst_1451_ = lean_ctor_get(v_a_1446_, 0);
v_snd_1452_ = lean_ctor_get(v_a_1446_, 1);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_a_1446_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1454_ = v_a_1446_;
v_isShared_1455_ = v_isSharedCheck_1470_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_snd_1452_);
lean_inc(v_fst_1451_);
lean_dec(v_a_1446_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1470_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
size_t v___x_1456_; size_t v___x_1457_; uint8_t v___x_1458_; 
v___x_1456_ = lean_ptr_addr(v_fn_1438_);
v___x_1457_ = lean_ptr_addr(v_fst_1443_);
v___x_1458_ = lean_usize_dec_eq(v___x_1456_, v___x_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; 
lean_del_object(v___x_1454_);
lean_del_object(v___x_1449_);
lean_dec_ref_known(v_e_1432_, 2);
v___x_1459_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_fst_1443_, v_fst_1451_, v_snd_1452_, v_a_1435_, v_a_1436_, v_a_1447_);
return v___x_1459_;
}
else
{
size_t v___x_1460_; size_t v___x_1461_; uint8_t v___x_1462_; 
v___x_1460_ = lean_ptr_addr(v_arg_1439_);
v___x_1461_ = lean_ptr_addr(v_fst_1451_);
v___x_1462_ = lean_usize_dec_eq(v___x_1460_, v___x_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
lean_del_object(v___x_1454_);
lean_del_object(v___x_1449_);
lean_dec_ref_known(v_e_1432_, 2);
v___x_1463_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_fst_1443_, v_fst_1451_, v_snd_1452_, v_a_1435_, v_a_1436_, v_a_1447_);
return v___x_1463_;
}
else
{
lean_object* v___x_1465_; 
lean_dec(v_fst_1451_);
lean_dec(v_fst_1443_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v_e_1432_);
v___x_1465_ = v___x_1454_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_e_1432_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_snd_1452_);
v___x_1465_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1467_; 
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1465_);
v___x_1467_ = v___x_1449_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_a_1447_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1443_);
lean_dec_ref_known(v_e_1432_, 2);
return v___x_1445_;
}
}
else
{
lean_dec_ref_known(v_e_1432_, 2);
lean_dec(v_offset_1433_);
lean_dec_ref(v___x_1427_);
return v___x_1440_;
}
}
case 6:
{
lean_object* v_binderName_1472_; lean_object* v_binderType_1473_; lean_object* v_body_1474_; uint8_t v_binderInfo_1475_; lean_object* v___x_1476_; 
v_binderName_1472_ = lean_ctor_get(v_e_1432_, 0);
v_binderType_1473_ = lean_ctor_get(v_e_1432_, 1);
v_body_1474_ = lean_ctor_get(v_e_1432_, 2);
v_binderInfo_1475_ = lean_ctor_get_uint8(v_e_1432_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1433_);
lean_inc_ref(v_binderType_1473_);
lean_inc_ref(v___x_1427_);
v___x_1476_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1426_, v___x_1427_, v___y_1428_, v_n_1429_, v_xs_1430_, v___x_1431_, v_binderType_1473_, v_offset_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v_a_1478_; lean_object* v_fst_1479_; lean_object* v_snd_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
v_a_1478_ = lean_ctor_get(v___x_1476_, 1);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1476_, 2);
v_fst_1479_ = lean_ctor_get(v_a_1477_, 0);
lean_inc(v_fst_1479_);
v_snd_1480_ = lean_ctor_get(v_a_1477_, 1);
lean_inc(v_snd_1480_);
lean_dec(v_a_1477_);
v___x_1481_ = lean_unsigned_to_nat(1u);
v___x_1482_ = lean_nat_add(v_offset_1433_, v___x_1481_);
lean_dec(v_offset_1433_);
lean_inc_ref(v_body_1474_);
v___x_1483_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1426_, v___x_1427_, v___y_1428_, v_n_1429_, v_xs_1430_, v___x_1431_, v_body_1474_, v___x_1482_, v_snd_1480_, v_a_1435_, v_a_1436_, v_a_1478_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1509_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
v_a_1485_ = lean_ctor_get(v___x_1483_, 1);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1487_ = v___x_1483_;
v_isShared_1488_ = v_isSharedCheck_1509_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_inc(v_a_1484_);
lean_dec(v___x_1483_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1509_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v_fst_1489_; lean_object* v_snd_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1508_; 
v_fst_1489_ = lean_ctor_get(v_a_1484_, 0);
v_snd_1490_ = lean_ctor_get(v_a_1484_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_a_1484_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1492_ = v_a_1484_;
v_isShared_1493_ = v_isSharedCheck_1508_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_snd_1490_);
lean_inc(v_fst_1489_);
lean_dec(v_a_1484_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1508_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
size_t v___x_1494_; size_t v___x_1495_; uint8_t v___x_1496_; 
v___x_1494_ = lean_ptr_addr(v_binderType_1473_);
v___x_1495_ = lean_ptr_addr(v_fst_1479_);
v___x_1496_ = lean_usize_dec_eq(v___x_1494_, v___x_1495_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; 
lean_inc(v_binderName_1472_);
lean_del_object(v___x_1492_);
lean_del_object(v___x_1487_);
lean_dec_ref_known(v_e_1432_, 3);
v___x_1497_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_binderName_1472_, v_binderInfo_1475_, v_fst_1479_, v_fst_1489_, v_snd_1490_, v_a_1435_, v_a_1436_, v_a_1485_);
return v___x_1497_;
}
else
{
size_t v___x_1498_; size_t v___x_1499_; uint8_t v___x_1500_; 
v___x_1498_ = lean_ptr_addr(v_body_1474_);
v___x_1499_ = lean_ptr_addr(v_fst_1489_);
v___x_1500_ = lean_usize_dec_eq(v___x_1498_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; 
lean_inc(v_binderName_1472_);
lean_del_object(v___x_1492_);
lean_del_object(v___x_1487_);
lean_dec_ref_known(v_e_1432_, 3);
v___x_1501_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_binderName_1472_, v_binderInfo_1475_, v_fst_1479_, v_fst_1489_, v_snd_1490_, v_a_1435_, v_a_1436_, v_a_1485_);
return v___x_1501_;
}
else
{
lean_object* v___x_1503_; 
lean_dec(v_fst_1489_);
lean_dec(v_fst_1479_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v_e_1432_);
v___x_1503_ = v___x_1492_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_e_1432_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_snd_1490_);
v___x_1503_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1505_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1503_);
v___x_1505_ = v___x_1487_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_a_1485_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1479_);
lean_dec_ref_known(v_e_1432_, 3);
return v___x_1483_;
}
}
else
{
lean_dec_ref_known(v_e_1432_, 3);
lean_dec(v_offset_1433_);
lean_dec_ref(v___x_1427_);
return v___x_1476_;
}
}
case 7:
{
lean_object* v_binderName_1510_; lean_object* v_binderType_1511_; lean_object* v_body_1512_; uint8_t v_binderInfo_1513_; lean_object* v___x_1514_; 
v_binderName_1510_ = lean_ctor_get(v_e_1432_, 0);
v_binderType_1511_ = lean_ctor_get(v_e_1432_, 1);
v_body_1512_ = lean_ctor_get(v_e_1432_, 2);
v_binderInfo_1513_ = lean_ctor_get_uint8(v_e_1432_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1433_);
lean_inc_ref(v_binderType_1511_);
lean_inc_ref(v___x_1427_);
v___x_1514_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1426_, v___x_1427_, v___y_1428_, v_n_1429_, v_xs_1430_, v___x_1431_, v_binderType_1511_, v_offset_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v_a_1516_; lean_object* v_fst_1517_; lean_object* v_snd_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
v_a_1516_ = lean_ctor_get(v___x_1514_, 1);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1514_, 2);
v_fst_1517_ = lean_ctor_get(v_a_1515_, 0);
lean_inc(v_fst_1517_);
v_snd_1518_ = lean_ctor_get(v_a_1515_, 1);
lean_inc(v_snd_1518_);
lean_dec(v_a_1515_);
v___x_1519_ = lean_unsigned_to_nat(1u);
v___x_1520_ = lean_nat_add(v_offset_1433_, v___x_1519_);
lean_dec(v_offset_1433_);
lean_inc_ref(v_body_1512_);
v___x_1521_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1426_, v___x_1427_, v___y_1428_, v_n_1429_, v_xs_1430_, v___x_1431_, v_body_1512_, v___x_1520_, v_snd_1518_, v_a_1435_, v_a_1436_, v_a_1516_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1547_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_a_1523_ = lean_ctor_get(v___x_1521_, 1);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1525_ = v___x_1521_;
v_isShared_1526_ = v_isSharedCheck_1547_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1547_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v_fst_1527_; lean_object* v_snd_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1546_; 
v_fst_1527_ = lean_ctor_get(v_a_1522_, 0);
v_snd_1528_ = lean_ctor_get(v_a_1522_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_a_1522_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1530_ = v_a_1522_;
v_isShared_1531_ = v_isSharedCheck_1546_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_snd_1528_);
lean_inc(v_fst_1527_);
lean_dec(v_a_1522_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1546_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
size_t v___x_1532_; size_t v___x_1533_; uint8_t v___x_1534_; 
v___x_1532_ = lean_ptr_addr(v_binderType_1511_);
v___x_1533_ = lean_ptr_addr(v_fst_1517_);
v___x_1534_ = lean_usize_dec_eq(v___x_1532_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_inc(v_binderName_1510_);
lean_del_object(v___x_1530_);
lean_del_object(v___x_1525_);
lean_dec_ref_known(v_e_1432_, 3);
v___x_1535_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_binderName_1510_, v_binderInfo_1513_, v_fst_1517_, v_fst_1527_, v_snd_1528_, v_a_1435_, v_a_1436_, v_a_1523_);
return v___x_1535_;
}
else
{
size_t v___x_1536_; size_t v___x_1537_; uint8_t v___x_1538_; 
v___x_1536_ = lean_ptr_addr(v_body_1512_);
v___x_1537_ = lean_ptr_addr(v_fst_1527_);
v___x_1538_ = lean_usize_dec_eq(v___x_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; 
lean_inc(v_binderName_1510_);
lean_del_object(v___x_1530_);
lean_del_object(v___x_1525_);
lean_dec_ref_known(v_e_1432_, 3);
v___x_1539_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_binderName_1510_, v_binderInfo_1513_, v_fst_1517_, v_fst_1527_, v_snd_1528_, v_a_1435_, v_a_1436_, v_a_1523_);
return v___x_1539_;
}
else
{
lean_object* v___x_1541_; 
lean_dec(v_fst_1527_);
lean_dec(v_fst_1517_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v_e_1432_);
v___x_1541_ = v___x_1530_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_e_1432_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_snd_1528_);
v___x_1541_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1543_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1541_);
v___x_1543_ = v___x_1525_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_a_1523_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1517_);
lean_dec_ref_known(v_e_1432_, 3);
return v___x_1521_;
}
}
else
{
lean_dec_ref_known(v_e_1432_, 3);
lean_dec(v_offset_1433_);
lean_dec_ref(v___x_1427_);
return v___x_1514_;
}
}
case 8:
{
lean_object* v_declName_1548_; lean_object* v_type_1549_; lean_object* v_value_1550_; lean_object* v_body_1551_; uint8_t v_nondep_1552_; lean_object* v___x_1553_; 
v_declName_1548_ = lean_ctor_get(v_e_1432_, 0);
v_type_1549_ = lean_ctor_get(v_e_1432_, 1);
v_value_1550_ = lean_ctor_get(v_e_1432_, 2);
v_body_1551_ = lean_ctor_get(v_e_1432_, 3);
v_nondep_1552_ = lean_ctor_get_uint8(v_e_1432_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1433_);
lean_inc_ref(v_type_1549_);
lean_inc_ref(v___x_1427_);
v___x_1553_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1426_, v___x_1427_, v___y_1428_, v_n_1429_, v_xs_1430_, v___x_1431_, v_type_1549_, v_offset_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v_a_1555_; lean_object* v_fst_1556_; lean_object* v_snd_1557_; lean_object* v___x_1558_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
v_a_1555_ = lean_ctor_get(v___x_1553_, 1);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1553_, 2);
v_fst_1556_ = lean_ctor_get(v_a_1554_, 0);
lean_inc(v_fst_1556_);
v_snd_1557_ = lean_ctor_get(v_a_1554_, 1);
lean_inc(v_snd_1557_);
lean_dec(v_a_1554_);
lean_inc(v_offset_1433_);
lean_inc_ref(v_value_1550_);
lean_inc_ref(v___x_1427_);
v___x_1558_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1426_, v___x_1427_, v___y_1428_, v_n_1429_, v_xs_1430_, v___x_1431_, v_value_1550_, v_offset_1433_, v_snd_1557_, v_a_1435_, v_a_1436_, v_a_1555_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v_a_1560_; lean_object* v_fst_1561_; lean_object* v_snd_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
v_a_1560_ = lean_ctor_get(v___x_1558_, 1);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1558_, 2);
v_fst_1561_ = lean_ctor_get(v_a_1559_, 0);
lean_inc(v_fst_1561_);
v_snd_1562_ = lean_ctor_get(v_a_1559_, 1);
lean_inc(v_snd_1562_);
lean_dec(v_a_1559_);
v___x_1563_ = lean_unsigned_to_nat(1u);
v___x_1564_ = lean_nat_add(v_offset_1433_, v___x_1563_);
lean_dec(v_offset_1433_);
lean_inc_ref(v_body_1551_);
v___x_1565_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1426_, v___x_1427_, v___y_1428_, v_n_1429_, v_xs_1430_, v___x_1431_, v_body_1551_, v___x_1564_, v_snd_1562_, v_a_1435_, v_a_1436_, v_a_1560_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1595_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
v_a_1567_ = lean_ctor_get(v___x_1565_, 1);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1569_ = v___x_1565_;
v_isShared_1570_ = v_isSharedCheck_1595_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_inc(v_a_1566_);
lean_dec(v___x_1565_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1595_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v_fst_1571_; lean_object* v_snd_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1594_; 
v_fst_1571_ = lean_ctor_get(v_a_1566_, 0);
v_snd_1572_ = lean_ctor_get(v_a_1566_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_a_1566_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1574_ = v_a_1566_;
v_isShared_1575_ = v_isSharedCheck_1594_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_snd_1572_);
lean_inc(v_fst_1571_);
lean_dec(v_a_1566_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1594_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
size_t v___x_1576_; size_t v___x_1577_; uint8_t v___x_1578_; 
v___x_1576_ = lean_ptr_addr(v_type_1549_);
v___x_1577_ = lean_ptr_addr(v_fst_1556_);
v___x_1578_ = lean_usize_dec_eq(v___x_1576_, v___x_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; 
lean_inc(v_declName_1548_);
lean_del_object(v___x_1574_);
lean_del_object(v___x_1569_);
lean_dec_ref_known(v_e_1432_, 4);
v___x_1579_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_1548_, v_fst_1556_, v_fst_1561_, v_fst_1571_, v_nondep_1552_, v_snd_1572_, v_a_1435_, v_a_1436_, v_a_1567_);
return v___x_1579_;
}
else
{
size_t v___x_1580_; size_t v___x_1581_; uint8_t v___x_1582_; 
v___x_1580_ = lean_ptr_addr(v_value_1550_);
v___x_1581_ = lean_ptr_addr(v_fst_1561_);
v___x_1582_ = lean_usize_dec_eq(v___x_1580_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
lean_inc(v_declName_1548_);
lean_del_object(v___x_1574_);
lean_del_object(v___x_1569_);
lean_dec_ref_known(v_e_1432_, 4);
v___x_1583_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_1548_, v_fst_1556_, v_fst_1561_, v_fst_1571_, v_nondep_1552_, v_snd_1572_, v_a_1435_, v_a_1436_, v_a_1567_);
return v___x_1583_;
}
else
{
size_t v___x_1584_; size_t v___x_1585_; uint8_t v___x_1586_; 
v___x_1584_ = lean_ptr_addr(v_body_1551_);
v___x_1585_ = lean_ptr_addr(v_fst_1571_);
v___x_1586_ = lean_usize_dec_eq(v___x_1584_, v___x_1585_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; 
lean_inc(v_declName_1548_);
lean_del_object(v___x_1574_);
lean_del_object(v___x_1569_);
lean_dec_ref_known(v_e_1432_, 4);
v___x_1587_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_1548_, v_fst_1556_, v_fst_1561_, v_fst_1571_, v_nondep_1552_, v_snd_1572_, v_a_1435_, v_a_1436_, v_a_1567_);
return v___x_1587_;
}
else
{
lean_object* v___x_1589_; 
lean_dec(v_fst_1571_);
lean_dec(v_fst_1561_);
lean_dec(v_fst_1556_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v_e_1432_);
v___x_1589_ = v___x_1574_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_e_1432_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_snd_1572_);
v___x_1589_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1591_; 
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1589_);
v___x_1591_ = v___x_1569_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_a_1567_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
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
lean_dec(v_fst_1561_);
lean_dec(v_fst_1556_);
lean_dec_ref_known(v_e_1432_, 4);
return v___x_1565_;
}
}
else
{
lean_dec(v_fst_1556_);
lean_dec_ref_known(v_e_1432_, 4);
lean_dec(v_offset_1433_);
lean_dec_ref(v___x_1427_);
return v___x_1558_;
}
}
else
{
lean_dec_ref_known(v_e_1432_, 4);
lean_dec(v_offset_1433_);
lean_dec_ref(v___x_1427_);
return v___x_1553_;
}
}
case 10:
{
lean_object* v_data_1596_; lean_object* v_expr_1597_; lean_object* v___x_1598_; 
v_data_1596_ = lean_ctor_get(v_e_1432_, 0);
v_expr_1597_ = lean_ctor_get(v_e_1432_, 1);
lean_inc_ref(v_expr_1597_);
v___x_1598_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1426_, v___x_1427_, v___y_1428_, v_n_1429_, v_xs_1430_, v___x_1431_, v_expr_1597_, v_offset_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1620_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
v_a_1600_ = lean_ctor_get(v___x_1598_, 1);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1602_ = v___x_1598_;
v_isShared_1603_ = v_isSharedCheck_1620_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_inc(v_a_1599_);
lean_dec(v___x_1598_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1620_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v_fst_1604_; lean_object* v_snd_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1619_; 
v_fst_1604_ = lean_ctor_get(v_a_1599_, 0);
v_snd_1605_ = lean_ctor_get(v_a_1599_, 1);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_a_1599_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1607_ = v_a_1599_;
v_isShared_1608_ = v_isSharedCheck_1619_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_snd_1605_);
lean_inc(v_fst_1604_);
lean_dec(v_a_1599_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1619_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
size_t v___x_1609_; size_t v___x_1610_; uint8_t v___x_1611_; 
v___x_1609_ = lean_ptr_addr(v_expr_1597_);
v___x_1610_ = lean_ptr_addr(v_fst_1604_);
v___x_1611_ = lean_usize_dec_eq(v___x_1609_, v___x_1610_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; 
lean_inc(v_data_1596_);
lean_del_object(v___x_1607_);
lean_del_object(v___x_1602_);
lean_dec_ref_known(v_e_1432_, 2);
v___x_1612_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(v_data_1596_, v_fst_1604_, v_snd_1605_, v_a_1435_, v_a_1436_, v_a_1600_);
return v___x_1612_;
}
else
{
lean_object* v___x_1614_; 
lean_dec(v_fst_1604_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v_e_1432_);
v___x_1614_ = v___x_1607_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_e_1432_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_snd_1605_);
v___x_1614_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1616_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1614_);
v___x_1616_ = v___x_1602_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_a_1600_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1432_, 2);
return v___x_1598_;
}
}
case 11:
{
lean_object* v_typeName_1621_; lean_object* v_idx_1622_; lean_object* v_struct_1623_; lean_object* v___x_1624_; 
v_typeName_1621_ = lean_ctor_get(v_e_1432_, 0);
v_idx_1622_ = lean_ctor_get(v_e_1432_, 1);
v_struct_1623_ = lean_ctor_get(v_e_1432_, 2);
lean_inc_ref(v_struct_1623_);
v___x_1624_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1426_, v___x_1427_, v___y_1428_, v_n_1429_, v_xs_1430_, v___x_1431_, v_struct_1623_, v_offset_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1646_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_a_1626_ = lean_ctor_get(v___x_1624_, 1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1628_ = v___x_1624_;
v_isShared_1629_ = v_isSharedCheck_1646_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1646_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v_fst_1630_; lean_object* v_snd_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1645_; 
v_fst_1630_ = lean_ctor_get(v_a_1625_, 0);
v_snd_1631_ = lean_ctor_get(v_a_1625_, 1);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_a_1625_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1633_ = v_a_1625_;
v_isShared_1634_ = v_isSharedCheck_1645_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_snd_1631_);
lean_inc(v_fst_1630_);
lean_dec(v_a_1625_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1645_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
size_t v___x_1635_; size_t v___x_1636_; uint8_t v___x_1637_; 
v___x_1635_ = lean_ptr_addr(v_struct_1623_);
v___x_1636_ = lean_ptr_addr(v_fst_1630_);
v___x_1637_ = lean_usize_dec_eq(v___x_1635_, v___x_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; 
lean_inc(v_idx_1622_);
lean_inc(v_typeName_1621_);
lean_del_object(v___x_1633_);
lean_del_object(v___x_1628_);
lean_dec_ref_known(v_e_1432_, 3);
v___x_1638_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(v_typeName_1621_, v_idx_1622_, v_fst_1630_, v_snd_1631_, v_a_1435_, v_a_1436_, v_a_1626_);
return v___x_1638_;
}
else
{
lean_object* v___x_1640_; 
lean_dec(v_fst_1630_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v_e_1432_);
v___x_1640_ = v___x_1633_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_e_1432_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_snd_1631_);
v___x_1640_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
lean_object* v___x_1642_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1640_);
v___x_1642_ = v___x_1628_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_a_1626_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1432_, 3);
return v___x_1624_;
}
}
default: 
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec(v_offset_1433_);
lean_dec_ref(v_e_1432_);
lean_dec_ref(v___x_1427_);
v___x_1647_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3);
v___x_1648_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(v___x_1647_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
return v___x_1648_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(lean_object* v_minIndex_1649_, lean_object* v___x_1650_, lean_object* v___y_1651_, lean_object* v_n_1652_, lean_object* v_xs_1653_, lean_object* v___x_1654_, lean_object* v_e_1655_, lean_object* v_offset_1656_, lean_object* v_a_1657_, uint8_t v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v_key_1661_; lean_object* v_a_1663_; lean_object* v___y_1677_; lean_object* v___y_1682_; lean_object* v___x_1687_; 
lean_inc(v_offset_1656_);
lean_inc_ref(v_e_1655_);
v_key_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1661_, 0, v_e_1655_);
lean_ctor_set(v_key_1661_, 1, v_offset_1656_);
v___x_1687_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_a_1657_, v_key_1661_);
if (lean_obj_tag(v___x_1687_) == 1)
{
lean_object* v_val_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec_ref_known(v_key_1661_, 2);
lean_dec(v_offset_1656_);
lean_dec_ref(v_e_1655_);
lean_dec_ref(v___x_1650_);
v_val_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_val_1688_);
lean_dec_ref_known(v___x_1687_, 1);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v_val_1688_);
lean_ctor_set(v___x_1689_, 1, v_a_1657_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
lean_ctor_set(v___x_1690_, 1, v_a_1660_);
return v___x_1690_;
}
else
{
lean_dec(v___x_1687_);
switch(lean_obj_tag(v_e_1655_))
{
case 1:
{
lean_object* v_fvarId_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec_ref(v___x_1650_);
v_fvarId_1691_ = lean_ctor_get(v_e_1655_, 0);
v___x_1692_ = lean_unsigned_to_nat(0u);
v___x_1693_ = lean_unsigned_to_nat(1u);
v___x_1694_ = lean_nat_sub(v___y_1651_, v___x_1693_);
v___x_1695_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___redArg(v_xs_1653_, v_fvarId_1691_, v___x_1692_, v___x_1694_);
if (lean_obj_tag(v___x_1695_) == 1)
{
lean_object* v_val_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
lean_dec_ref_known(v_e_1655_, 1);
v_val_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_val_1696_);
lean_dec_ref_known(v___x_1695_, 1);
v___x_1697_ = lean_nat_add(v_offset_1656_, v_val_1696_);
lean_dec(v_val_1696_);
lean_dec(v_offset_1656_);
v___x_1698_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v___x_1697_, v_a_1660_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v_a_1700_; lean_object* v___x_1701_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
v_a_1700_ = lean_ctor_get(v___x_1698_, 1);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1698_, 2);
v___x_1701_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1661_, v_a_1699_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1700_);
return v___x_1701_;
}
else
{
lean_object* v_a_1702_; lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec_ref_known(v_key_1661_, 2);
lean_dec_ref(v_a_1657_);
v_a_1702_ = lean_ctor_get(v___x_1698_, 0);
v_a_1703_ = lean_ctor_get(v___x_1698_, 1);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1698_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_inc(v_a_1702_);
lean_dec(v___x_1698_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1702_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v___x_1711_; 
lean_dec(v___x_1695_);
lean_dec(v_offset_1656_);
v___x_1711_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1661_, v_e_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1711_;
}
}
case 9:
{
lean_object* v___x_1712_; 
lean_dec(v_offset_1656_);
lean_dec_ref(v___x_1650_);
v___x_1712_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1661_, v_e_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1712_;
}
case 2:
{
lean_object* v___x_1713_; 
lean_dec(v_offset_1656_);
lean_dec_ref(v___x_1650_);
v___x_1713_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1661_, v_e_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1713_;
}
case 0:
{
lean_object* v___x_1714_; 
lean_dec(v_offset_1656_);
lean_dec_ref(v___x_1650_);
v___x_1714_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1661_, v_e_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1714_;
}
case 4:
{
lean_object* v___x_1715_; 
lean_dec(v_offset_1656_);
lean_dec_ref(v___x_1650_);
v___x_1715_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1661_, v_e_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1715_;
}
case 3:
{
lean_object* v___x_1716_; 
lean_dec(v_offset_1656_);
lean_dec_ref(v___x_1650_);
v___x_1716_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1661_, v_e_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1716_;
}
default: 
{
uint8_t v___x_1717_; 
v___x_1717_ = l_Lean_Expr_hasFVar(v_e_1655_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; 
lean_dec(v_offset_1656_);
lean_dec_ref(v___x_1650_);
v___x_1718_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1661_, v_e_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1718_;
}
else
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v___x_1654_, v_e_1655_);
if (lean_obj_tag(v___x_1719_) == 1)
{
lean_object* v_val_1720_; 
v_val_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_val_1720_);
lean_dec_ref_known(v___x_1719_, 1);
if (lean_obj_tag(v_val_1720_) == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1722_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v___x_1721_);
v___y_1682_ = v___x_1722_;
goto v___jp_1681_;
}
else
{
lean_object* v_val_1723_; 
v_val_1723_ = lean_ctor_get(v_val_1720_, 0);
lean_inc(v_val_1723_);
lean_dec_ref_known(v_val_1720_, 1);
v___y_1682_ = v_val_1723_;
goto v___jp_1681_;
}
}
else
{
lean_dec(v___x_1719_);
v_a_1663_ = v_a_1660_;
goto v___jp_1662_;
}
}
}
}
}
v___jp_1662_:
{
switch(lean_obj_tag(v_e_1655_))
{
case 9:
{
lean_object* v___x_1664_; 
lean_dec(v_offset_1656_);
lean_dec_ref(v___x_1650_);
v___x_1664_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1661_, v_e_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1663_);
return v___x_1664_;
}
case 2:
{
lean_object* v___x_1665_; 
lean_dec(v_offset_1656_);
lean_dec_ref(v___x_1650_);
v___x_1665_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1661_, v_e_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1663_);
return v___x_1665_;
}
case 0:
{
lean_object* v___x_1666_; 
lean_dec(v_offset_1656_);
lean_dec_ref(v___x_1650_);
v___x_1666_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1661_, v_e_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1663_);
return v___x_1666_;
}
case 1:
{
lean_object* v___x_1667_; 
lean_dec(v_offset_1656_);
lean_dec_ref(v___x_1650_);
v___x_1667_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1661_, v_e_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1663_);
return v___x_1667_;
}
case 4:
{
lean_object* v___x_1668_; 
lean_dec(v_offset_1656_);
lean_dec_ref(v___x_1650_);
v___x_1668_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1661_, v_e_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1663_);
return v___x_1668_;
}
case 3:
{
lean_object* v___x_1669_; 
lean_dec(v_offset_1656_);
lean_dec_ref(v___x_1650_);
v___x_1669_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1661_, v_e_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1663_);
return v___x_1669_;
}
default: 
{
lean_object* v___x_1670_; 
v___x_1670_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0(v_minIndex_1649_, v___x_1650_, v___y_1651_, v_n_1652_, v_xs_1653_, v___x_1654_, v_e_1655_, v_offset_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1663_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v_a_1672_; lean_object* v_fst_1673_; lean_object* v_snd_1674_; lean_object* v___x_1675_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
v_a_1672_ = lean_ctor_get(v___x_1670_, 1);
lean_inc(v_a_1672_);
lean_dec_ref_known(v___x_1670_, 2);
v_fst_1673_ = lean_ctor_get(v_a_1671_, 0);
lean_inc(v_fst_1673_);
v_snd_1674_ = lean_ctor_get(v_a_1671_, 1);
lean_inc(v_snd_1674_);
lean_dec(v_a_1671_);
v___x_1675_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1661_, v_fst_1673_, v_snd_1674_, v_a_1658_, v_a_1659_, v_a_1672_);
return v___x_1675_;
}
else
{
lean_dec_ref_known(v_key_1661_, 2);
return v___x_1670_;
}
}
}
}
v___jp_1676_:
{
lean_object* v_maxIndex_1678_; uint8_t v___x_1679_; 
v_maxIndex_1678_ = l_Lean_LocalDecl_index(v___y_1677_);
lean_dec_ref(v___y_1677_);
v___x_1679_ = lean_nat_dec_lt(v_maxIndex_1678_, v_minIndex_1649_);
lean_dec(v_maxIndex_1678_);
if (v___x_1679_ == 0)
{
v_a_1663_ = v_a_1660_;
goto v___jp_1662_;
}
else
{
lean_object* v___x_1680_; 
lean_dec(v_offset_1656_);
lean_dec_ref(v___x_1650_);
v___x_1680_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1661_, v_e_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1680_;
}
}
v___jp_1681_:
{
lean_object* v___x_1683_; 
lean_inc_ref(v___x_1650_);
v___x_1683_ = lean_local_ctx_find(v___x_1650_, v___y_1682_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1685_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1684_);
v___y_1677_ = v___x_1685_;
goto v___jp_1676_;
}
else
{
lean_object* v_val_1686_; 
v_val_1686_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_val_1686_);
lean_dec_ref_known(v___x_1683_, 1);
v___y_1677_ = v_val_1686_;
goto v___jp_1676_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0___boxed(lean_object* v_minIndex_1724_, lean_object* v___x_1725_, lean_object* v___y_1726_, lean_object* v_n_1727_, lean_object* v_xs_1728_, lean_object* v___x_1729_, lean_object* v_e_1730_, lean_object* v_offset_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_){
_start:
{
uint8_t v_a_boxed_1736_; lean_object* v_res_1737_; 
v_a_boxed_1736_ = lean_unbox(v_a_1733_);
v_res_1737_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1724_, v___x_1725_, v___y_1726_, v_n_1727_, v_xs_1728_, v___x_1729_, v_e_1730_, v_offset_1731_, v_a_1732_, v_a_boxed_1736_, v_a_1734_, v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec_ref(v___x_1729_);
lean_dec_ref(v_xs_1728_);
lean_dec(v_n_1727_);
lean_dec(v___y_1726_);
lean_dec(v_minIndex_1724_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0___boxed(lean_object* v_minIndex_1738_, lean_object* v___x_1739_, lean_object* v___y_1740_, lean_object* v_n_1741_, lean_object* v_xs_1742_, lean_object* v___x_1743_, lean_object* v_e_1744_, lean_object* v_offset_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
uint8_t v_a_boxed_1750_; lean_object* v_res_1751_; 
v_a_boxed_1750_ = lean_unbox(v_a_1747_);
v_res_1751_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0(v_minIndex_1738_, v___x_1739_, v___y_1740_, v_n_1741_, v_xs_1742_, v___x_1743_, v_e_1744_, v_offset_1745_, v_a_1746_, v_a_boxed_1750_, v_a_1748_, v_a_1749_);
lean_dec_ref(v_a_1748_);
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_xs_1742_);
lean_dec(v_n_1741_);
lean_dec(v___y_1740_);
lean_dec(v_minIndex_1738_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsPrefix___lam__0(lean_object* v_e_1752_, lean_object* v___x_1753_, lean_object* v_lctx_1754_, lean_object* v___y_1755_, lean_object* v_n_1756_, lean_object* v_xs_1757_, lean_object* v_maxFVar_1758_, uint8_t v_debug_1759_, lean_object* v___x_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v___y_1764_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1807_; lean_object* v___x_1826_; 
lean_inc_ref(v_lctx_1754_);
v___x_1826_ = lean_local_ctx_find(v_lctx_1754_, v___x_1760_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1828_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1827_);
v___y_1807_ = v___x_1828_;
goto v___jp_1806_;
}
else
{
lean_object* v_val_1829_; 
v_val_1829_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_val_1829_);
lean_dec_ref_known(v___x_1826_, 1);
v___y_1807_ = v_val_1829_;
goto v___jp_1806_;
}
v___jp_1763_:
{
switch(lean_obj_tag(v_e_1752_))
{
case 9:
{
lean_object* v___x_1765_; 
lean_dec(v___y_1764_);
lean_dec_ref(v_lctx_1754_);
lean_dec(v___x_1753_);
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v_e_1752_);
lean_ctor_set(v___x_1765_, 1, v___y_1762_);
return v___x_1765_;
}
case 2:
{
lean_object* v___x_1766_; 
lean_dec(v___y_1764_);
lean_dec_ref(v_lctx_1754_);
lean_dec(v___x_1753_);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v_e_1752_);
lean_ctor_set(v___x_1766_, 1, v___y_1762_);
return v___x_1766_;
}
case 0:
{
lean_object* v___x_1767_; 
lean_dec(v___y_1764_);
lean_dec_ref(v_lctx_1754_);
lean_dec(v___x_1753_);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_e_1752_);
lean_ctor_set(v___x_1767_, 1, v___y_1762_);
return v___x_1767_;
}
case 1:
{
lean_object* v___x_1768_; 
lean_dec(v___y_1764_);
lean_dec_ref(v_lctx_1754_);
lean_dec(v___x_1753_);
v___x_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1768_, 0, v_e_1752_);
lean_ctor_set(v___x_1768_, 1, v___y_1762_);
return v___x_1768_;
}
case 4:
{
lean_object* v___x_1769_; 
lean_dec(v___y_1764_);
lean_dec_ref(v_lctx_1754_);
lean_dec(v___x_1753_);
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v_e_1752_);
lean_ctor_set(v___x_1769_, 1, v___y_1762_);
return v___x_1769_;
}
case 3:
{
lean_object* v___x_1770_; 
lean_dec(v___y_1764_);
lean_dec_ref(v_lctx_1754_);
lean_dec(v___x_1753_);
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v_e_1752_);
lean_ctor_set(v___x_1770_, 1, v___y_1762_);
return v___x_1770_;
}
default: 
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2);
lean_inc(v___x_1753_);
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1753_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0(v___y_1764_, v_lctx_1754_, v___y_1755_, v_n_1756_, v_xs_1757_, v_maxFVar_1758_, v_e_1752_, v___x_1753_, v___x_1772_, v_debug_1759_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1764_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1783_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_a_1775_ = lean_ctor_get(v___x_1773_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1777_ = v___x_1773_;
v_isShared_1778_ = v_isSharedCheck_1783_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1783_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v_fst_1779_; lean_object* v___x_1781_; 
v_fst_1779_ = lean_ctor_get(v_a_1774_, 0);
lean_inc(v_fst_1779_);
lean_dec(v_a_1774_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v_fst_1779_);
v___x_1781_ = v___x_1777_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_fst_1779_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_a_1775_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
v_a_1784_ = lean_ctor_get(v___x_1773_, 0);
v_a_1785_ = lean_ctor_get(v___x_1773_, 1);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1773_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_inc(v_a_1784_);
lean_dec(v___x_1773_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1784_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
}
}
v___jp_1793_:
{
lean_object* v_maxIndex_1796_; uint8_t v___x_1797_; 
v_maxIndex_1796_ = l_Lean_LocalDecl_index(v___y_1795_);
lean_dec_ref(v___y_1795_);
v___x_1797_ = lean_nat_dec_lt(v_maxIndex_1796_, v___y_1794_);
lean_dec(v_maxIndex_1796_);
if (v___x_1797_ == 0)
{
v___y_1764_ = v___y_1794_;
goto v___jp_1763_;
}
else
{
lean_object* v___x_1798_; 
lean_dec(v___y_1794_);
lean_dec_ref(v_lctx_1754_);
lean_dec(v___x_1753_);
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v_e_1752_);
lean_ctor_set(v___x_1798_, 1, v___y_1762_);
return v___x_1798_;
}
}
v___jp_1799_:
{
lean_object* v___x_1802_; 
lean_inc_ref(v_lctx_1754_);
v___x_1802_ = lean_local_ctx_find(v_lctx_1754_, v___y_1801_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1804_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1803_);
v___y_1794_ = v___y_1800_;
v___y_1795_ = v___x_1804_;
goto v___jp_1793_;
}
else
{
lean_object* v_val_1805_; 
v_val_1805_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_val_1805_);
lean_dec_ref_known(v___x_1802_, 1);
v___y_1794_ = v___y_1800_;
v___y_1795_ = v_val_1805_;
goto v___jp_1793_;
}
}
v___jp_1806_:
{
switch(lean_obj_tag(v_e_1752_))
{
case 1:
{
lean_object* v_fvarId_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec_ref(v___y_1807_);
lean_dec_ref(v_lctx_1754_);
v_fvarId_1808_ = lean_ctor_get(v_e_1752_, 0);
v___x_1809_ = lean_unsigned_to_nat(1u);
v___x_1810_ = lean_nat_sub(v___y_1755_, v___x_1809_);
v___x_1811_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___redArg(v_xs_1757_, v_fvarId_1808_, v___x_1753_, v___x_1810_);
if (lean_obj_tag(v___x_1811_) == 1)
{
lean_object* v_val_1812_; lean_object* v___x_1813_; 
lean_dec_ref_known(v_e_1752_, 1);
v_val_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_val_1812_);
lean_dec_ref_known(v___x_1811_, 1);
v___x_1813_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v_val_1812_, v___y_1762_);
return v___x_1813_;
}
else
{
lean_object* v___x_1814_; 
lean_dec(v___x_1811_);
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v_e_1752_);
lean_ctor_set(v___x_1814_, 1, v___y_1762_);
return v___x_1814_;
}
}
case 9:
{
lean_object* v___x_1815_; 
lean_dec_ref(v___y_1807_);
lean_dec_ref(v_lctx_1754_);
lean_dec(v___x_1753_);
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v_e_1752_);
lean_ctor_set(v___x_1815_, 1, v___y_1762_);
return v___x_1815_;
}
case 2:
{
lean_object* v___x_1816_; 
lean_dec_ref(v___y_1807_);
lean_dec_ref(v_lctx_1754_);
lean_dec(v___x_1753_);
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v_e_1752_);
lean_ctor_set(v___x_1816_, 1, v___y_1762_);
return v___x_1816_;
}
case 0:
{
lean_object* v___x_1817_; 
lean_dec_ref(v___y_1807_);
lean_dec_ref(v_lctx_1754_);
lean_dec(v___x_1753_);
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v_e_1752_);
lean_ctor_set(v___x_1817_, 1, v___y_1762_);
return v___x_1817_;
}
case 4:
{
lean_object* v___x_1818_; 
lean_dec_ref(v___y_1807_);
lean_dec_ref(v_lctx_1754_);
lean_dec(v___x_1753_);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v_e_1752_);
lean_ctor_set(v___x_1818_, 1, v___y_1762_);
return v___x_1818_;
}
case 3:
{
lean_object* v___x_1819_; 
lean_dec_ref(v___y_1807_);
lean_dec_ref(v_lctx_1754_);
lean_dec(v___x_1753_);
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v_e_1752_);
lean_ctor_set(v___x_1819_, 1, v___y_1762_);
return v___x_1819_;
}
default: 
{
lean_object* v_minIndex_1820_; lean_object* v___x_1821_; 
v_minIndex_1820_ = l_Lean_LocalDecl_index(v___y_1807_);
lean_dec_ref(v___y_1807_);
v___x_1821_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_maxFVar_1758_, v_e_1752_);
if (lean_obj_tag(v___x_1821_) == 1)
{
lean_object* v_val_1822_; 
v_val_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_val_1822_);
lean_dec_ref_known(v___x_1821_, 1);
if (lean_obj_tag(v_val_1822_) == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1824_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v___x_1823_);
v___y_1800_ = v_minIndex_1820_;
v___y_1801_ = v___x_1824_;
goto v___jp_1799_;
}
else
{
lean_object* v_val_1825_; 
v_val_1825_ = lean_ctor_get(v_val_1822_, 0);
lean_inc(v_val_1825_);
lean_dec_ref_known(v_val_1822_, 1);
v___y_1800_ = v_minIndex_1820_;
v___y_1801_ = v_val_1825_;
goto v___jp_1799_;
}
}
else
{
lean_dec(v___x_1821_);
v___y_1764_ = v_minIndex_1820_;
goto v___jp_1763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsPrefix___lam__0___boxed(lean_object* v_e_1830_, lean_object* v___x_1831_, lean_object* v_lctx_1832_, lean_object* v___y_1833_, lean_object* v_n_1834_, lean_object* v_xs_1835_, lean_object* v_maxFVar_1836_, lean_object* v_debug_1837_, lean_object* v___x_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
uint8_t v_debug_boxed_1841_; lean_object* v_res_1842_; 
v_debug_boxed_1841_ = lean_unbox(v_debug_1837_);
v_res_1842_ = l_Lean_Meta_Sym_abstractFVarsPrefix___lam__0(v_e_1830_, v___x_1831_, v_lctx_1832_, v___y_1833_, v_n_1834_, v_xs_1835_, v_maxFVar_1836_, v_debug_boxed_1841_, v___x_1838_, v___y_1839_, v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v_maxFVar_1836_);
lean_dec_ref(v_xs_1835_);
lean_dec(v_n_1834_);
lean_dec(v___y_1833_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsPrefix(lean_object* v_e_1843_, lean_object* v_n_1844_, lean_object* v_xs_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
uint8_t v___x_1853_; 
v___x_1853_ = l_Lean_Expr_hasFVar(v_e_1843_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; 
lean_dec_ref(v_xs_1845_);
lean_dec(v_n_1844_);
v___x_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1854_, 0, v_e_1843_);
return v___x_1854_;
}
else
{
uint8_t v___x_1855_; lean_object* v___y_1857_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1855_ = 0;
v___x_1893_ = lean_array_get_size(v_xs_1845_);
v___x_1894_ = lean_nat_dec_le(v_n_1844_, v___x_1893_);
if (v___x_1894_ == 0)
{
v___y_1857_ = v___x_1893_;
goto v___jp_1856_;
}
else
{
lean_inc(v_n_1844_);
v___y_1857_ = v_n_1844_;
goto v___jp_1856_;
}
v___jp_1856_:
{
lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1858_ = lean_unsigned_to_nat(0u);
v___x_1859_ = lean_nat_dec_lt(v___x_1858_, v___y_1857_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_dec(v___y_1857_);
lean_dec_ref(v_xs_1845_);
lean_dec(v_n_1844_);
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v_e_1843_);
return v___x_1860_;
}
else
{
lean_object* v_lctx_1861_; lean_object* v___x_1862_; lean_object* v_maxFVar_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v_debug_1867_; lean_object* v___x_1868_; lean_object* v___f_1869_; lean_object* v___x_1870_; lean_object* v_env_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_lctx_1861_ = lean_ctor_get(v_a_1848_, 2);
v___x_1862_ = lean_st_ref_get(v_a_1847_);
v_maxFVar_1863_ = lean_ctor_get(v___x_1862_, 1);
lean_inc_ref(v_maxFVar_1863_);
lean_dec(v___x_1862_);
v___x_1864_ = lean_array_fget_borrowed(v_xs_1845_, v___x_1858_);
v___x_1865_ = l_Lean_Expr_fvarId_x21(v___x_1864_);
v___x_1866_ = lean_st_ref_get(v_a_1847_);
v_debug_1867_ = lean_ctor_get_uint8(v___x_1866_, sizeof(void*)*12);
lean_dec(v___x_1866_);
v___x_1868_ = lean_box(v_debug_1867_);
lean_inc_ref(v_lctx_1861_);
v___f_1869_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_abstractFVarsPrefix___lam__0___boxed), 11, 9);
lean_closure_set(v___f_1869_, 0, v_e_1843_);
lean_closure_set(v___f_1869_, 1, v___x_1858_);
lean_closure_set(v___f_1869_, 2, v_lctx_1861_);
lean_closure_set(v___f_1869_, 3, v___y_1857_);
lean_closure_set(v___f_1869_, 4, v_n_1844_);
lean_closure_set(v___f_1869_, 5, v_xs_1845_);
lean_closure_set(v___f_1869_, 6, v_maxFVar_1863_);
lean_closure_set(v___f_1869_, 7, v___x_1868_);
lean_closure_set(v___f_1869_, 8, v___x_1865_);
v___x_1870_ = lean_st_ref_get(v_a_1851_);
v_env_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc_ref(v_env_1871_);
lean_dec(v___x_1870_);
v___x_1872_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1872_, 0, v_env_1871_);
lean_ctor_set_uint8(v___x_1872_, sizeof(void*)*1, v___x_1855_);
lean_ctor_set_uint8(v___x_1872_, sizeof(void*)*1 + 1, v___x_1855_);
v___x_1873_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1869_, v___x_1872_, v_a_1847_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1884_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1884_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1884_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
if (lean_obj_tag(v_a_1874_) == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
lean_dec_ref_known(v_a_1874_, 1);
lean_del_object(v___x_1876_);
v___x_1878_ = lean_obj_once(&l_Lean_Meta_Sym_abstractFVarsRange___closed__2, &l_Lean_Meta_Sym_abstractFVarsRange___closed__2_once, _init_l_Lean_Meta_Sym_abstractFVarsRange___closed__2);
v___x_1879_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v___x_1878_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
return v___x_1879_;
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; 
v_a_1880_ = lean_ctor_get(v_a_1874_, 0);
lean_inc(v_a_1880_);
lean_dec_ref_known(v_a_1874_, 1);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v_a_1880_);
v___x_1882_ = v___x_1876_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
v_a_1885_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1873_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1873_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsPrefix___boxed(lean_object* v_e_1895_, lean_object* v_n_1896_, lean_object* v_xs_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Meta_Sym_abstractFVarsPrefix(v_e_1895_, v_n_1896_, v_xs_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars(lean_object* v_e_1906_, lean_object* v_xs_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_unsigned_to_nat(0u);
v___x_1916_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1906_, v___x_1915_, v_xs_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___boxed(lean_object* v_e_1917_, lean_object* v_xs_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_Meta_Sym_abstractFVars(v_e_1917_, v_xs_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(lean_object* v_x_1927_, uint8_t v_bi_1928_, lean_object* v_t_1929_, lean_object* v_b_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v___y_1939_; lean_object* v___x_1942_; uint8_t v_debug_1943_; 
v___x_1942_ = lean_st_ref_get(v___y_1932_);
v_debug_1943_ = lean_ctor_get_uint8(v___x_1942_, sizeof(void*)*12);
lean_dec(v___x_1942_);
if (v_debug_1943_ == 0)
{
v___y_1939_ = v___y_1932_;
goto v___jp_1938_;
}
else
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1929_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v___x_1945_; 
lean_dec_ref_known(v___x_1944_, 1);
v___x_1945_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_dec_ref_known(v___x_1945_, 1);
v___y_1939_ = v___y_1932_;
goto v___jp_1938_;
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec_ref(v_b_1930_);
lean_dec_ref(v_t_1929_);
lean_dec(v_x_1927_);
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec_ref(v_b_1930_);
lean_dec_ref(v_t_1929_);
lean_dec(v_x_1927_);
v_a_1954_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1944_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1944_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
v___jp_1938_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = l_Lean_Expr_lam___override(v_x_1927_, v_t_1929_, v_b_1930_, v_bi_1928_);
v___x_1941_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1940_, v___y_1939_);
return v___x_1941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0___boxed(lean_object* v_x_1962_, lean_object* v_bi_1963_, lean_object* v_t_1964_, lean_object* v_b_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
uint8_t v_bi_boxed_1973_; lean_object* v_res_1974_; 
v_bi_boxed_1973_ = lean_unbox(v_bi_1963_);
v_res_1974_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v_x_1962_, v_bi_boxed_1973_, v_t_1964_, v_b_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(lean_object* v_xs_1975_, lean_object* v_i_1976_, lean_object* v_a_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_zero_1985_; uint8_t v_isZero_1986_; 
v_zero_1985_ = lean_unsigned_to_nat(0u);
v_isZero_1986_ = lean_nat_dec_eq(v_i_1976_, v_zero_1985_);
if (v_isZero_1986_ == 1)
{
lean_object* v___x_1987_; 
lean_dec(v_i_1976_);
lean_dec_ref(v_xs_1975_);
v___x_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1987_, 0, v_a_1977_);
return v___x_1987_;
}
else
{
lean_object* v_one_1988_; lean_object* v_n_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v_one_1988_ = lean_unsigned_to_nat(1u);
v_n_1989_ = lean_nat_sub(v_i_1976_, v_one_1988_);
lean_dec(v_i_1976_);
v___x_1990_ = lean_array_fget_borrowed(v_xs_1975_, v_n_1989_);
v___x_1991_ = l_Lean_Expr_fvarId_x21(v___x_1990_);
v___x_1992_ = l_Lean_FVarId_getDecl___redArg(v___x_1991_, v___y_1980_, v___y_1982_, v___y_1983_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1992_, 1);
v___x_1994_ = l_Lean_LocalDecl_type(v_a_1993_);
lean_inc_ref(v_xs_1975_);
lean_inc(v_n_1989_);
v___x_1995_ = l_Lean_Meta_Sym_abstractFVarsPrefix(v___x_1994_, v_n_1989_, v_xs_1975_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref_known(v___x_1995_, 1);
v___x_1997_ = l_Lean_LocalDecl_userName(v_a_1993_);
v___x_1998_ = l_Lean_LocalDecl_binderInfo(v_a_1993_);
lean_dec(v_a_1993_);
v___x_1999_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v___x_1997_, v___x_1998_, v_a_1996_, v_a_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v_i_1976_ = v_n_1989_;
v_a_1977_ = v_a_2000_;
goto _start;
}
else
{
lean_dec(v_n_1989_);
lean_dec_ref(v_xs_1975_);
return v___x_1999_;
}
}
else
{
lean_dec(v_a_1993_);
lean_dec(v_n_1989_);
lean_dec_ref(v_a_1977_);
lean_dec_ref(v_xs_1975_);
return v___x_1995_;
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_dec(v_n_1989_);
lean_dec_ref(v_a_1977_);
lean_dec_ref(v_xs_1975_);
v_a_2002_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1992_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1992_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg___boxed(lean_object* v_xs_2010_, lean_object* v_i_2011_, lean_object* v_a_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_2010_, v_i_2011_, v_a_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS(lean_object* v_xs_2021_, lean_object* v_e_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_xs_2021_);
v___x_2031_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_2022_, v___x_2030_, v_xs_2021_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2033_ = lean_array_get_size(v_xs_2021_);
v___x_2034_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_2021_, v___x_2033_, v_a_2032_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
return v___x_2034_;
}
else
{
lean_dec_ref(v_xs_2021_);
return v___x_2031_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS___boxed(lean_object* v_xs_2035_, lean_object* v_e_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_2035_, v_e_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2037_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(lean_object* v_xs_2045_, lean_object* v_n_2046_, lean_object* v_i_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_2045_, v_i_2047_, v_a_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___boxed(lean_object* v_xs_2058_, lean_object* v_n_2059_, lean_object* v_i_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(v_xs_2058_, v_n_2059_, v_i_2060_, v_a_2061_, v_a_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v_n_2059_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(lean_object* v_x_2071_, uint8_t v_bi_2072_, lean_object* v_t_2073_, lean_object* v_b_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v___y_2083_; lean_object* v___x_2086_; uint8_t v_debug_2087_; 
v___x_2086_ = lean_st_ref_get(v___y_2076_);
v_debug_2087_ = lean_ctor_get_uint8(v___x_2086_, sizeof(void*)*12);
lean_dec(v___x_2086_);
if (v_debug_2087_ == 0)
{
v___y_2083_ = v___y_2076_;
goto v___jp_2082_;
}
else
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2073_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v___x_2089_; 
lean_dec_ref_known(v___x_2088_, 1);
v___x_2089_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_dec_ref_known(v___x_2089_, 1);
v___y_2083_ = v___y_2076_;
goto v___jp_2082_;
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec_ref(v_b_2074_);
lean_dec_ref(v_t_2073_);
lean_dec(v_x_2071_);
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec_ref(v_b_2074_);
lean_dec_ref(v_t_2073_);
lean_dec(v_x_2071_);
v_a_2098_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2088_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2088_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
v___jp_2082_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = l_Lean_Expr_forallE___override(v_x_2071_, v_t_2073_, v_b_2074_, v_bi_2072_);
v___x_2085_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2084_, v___y_2083_);
return v___x_2085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0___boxed(lean_object* v_x_2106_, lean_object* v_bi_2107_, lean_object* v_t_2108_, lean_object* v_b_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
uint8_t v_bi_boxed_2117_; lean_object* v_res_2118_; 
v_bi_boxed_2117_ = lean_unbox(v_bi_2107_);
v_res_2118_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v_x_2106_, v_bi_boxed_2117_, v_t_2108_, v_b_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(lean_object* v_xs_2119_, lean_object* v_i_2120_, lean_object* v_a_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_zero_2129_; uint8_t v_isZero_2130_; 
v_zero_2129_ = lean_unsigned_to_nat(0u);
v_isZero_2130_ = lean_nat_dec_eq(v_i_2120_, v_zero_2129_);
if (v_isZero_2130_ == 1)
{
lean_object* v___x_2131_; 
lean_dec(v_i_2120_);
lean_dec_ref(v_xs_2119_);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v_a_2121_);
return v___x_2131_;
}
else
{
lean_object* v_one_2132_; lean_object* v_n_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v_one_2132_ = lean_unsigned_to_nat(1u);
v_n_2133_ = lean_nat_sub(v_i_2120_, v_one_2132_);
lean_dec(v_i_2120_);
v___x_2134_ = lean_array_fget_borrowed(v_xs_2119_, v_n_2133_);
v___x_2135_ = l_Lean_Expr_fvarId_x21(v___x_2134_);
v___x_2136_ = l_Lean_FVarId_getDecl___redArg(v___x_2135_, v___y_2124_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v___x_2138_ = l_Lean_LocalDecl_type(v_a_2137_);
lean_inc_ref(v_xs_2119_);
lean_inc(v_n_2133_);
v___x_2139_ = l_Lean_Meta_Sym_abstractFVarsPrefix(v___x_2138_, v_n_2133_, v_xs_2119_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; lean_object* v___x_2143_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = l_Lean_LocalDecl_userName(v_a_2137_);
v___x_2142_ = l_Lean_LocalDecl_binderInfo(v_a_2137_);
lean_dec(v_a_2137_);
v___x_2143_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v___x_2141_, v___x_2142_, v_a_2140_, v_a_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v_i_2120_ = v_n_2133_;
v_a_2121_ = v_a_2144_;
goto _start;
}
else
{
lean_dec(v_n_2133_);
lean_dec_ref(v_xs_2119_);
return v___x_2143_;
}
}
else
{
lean_dec(v_a_2137_);
lean_dec(v_n_2133_);
lean_dec_ref(v_a_2121_);
lean_dec_ref(v_xs_2119_);
return v___x_2139_;
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_n_2133_);
lean_dec_ref(v_a_2121_);
lean_dec_ref(v_xs_2119_);
v_a_2146_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2136_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2136_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg___boxed(lean_object* v_xs_2154_, lean_object* v_i_2155_, lean_object* v_a_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_2154_, v_i_2155_, v_a_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object* v_xs_2165_, lean_object* v_e_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_xs_2165_);
v___x_2175_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_2166_, v___x_2174_, v_xs_2165_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2177_ = lean_array_get_size(v_xs_2165_);
v___x_2178_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_2165_, v___x_2177_, v_a_2176_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
return v___x_2178_;
}
else
{
lean_dec_ref(v_xs_2165_);
return v___x_2175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS___boxed(lean_object* v_xs_2179_, lean_object* v_e_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_Meta_Sym_mkForallFVarsS(v_xs_2179_, v_e_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(lean_object* v_xs_2189_, lean_object* v_n_2190_, lean_object* v_i_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_2189_, v_i_2191_, v_a_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___boxed(lean_object* v_xs_2202_, lean_object* v_n_2203_, lean_object* v_i_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(v_xs_2202_, v_n_2203_, v_i_2204_, v_a_2205_, v_a_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v_n_2203_);
return v_res_2214_;
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
