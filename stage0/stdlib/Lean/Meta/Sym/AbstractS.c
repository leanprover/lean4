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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsPrefix___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsPrefix___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(lean_object* v_toDeBruijn_x3f_10_, lean_object* v___x_11_, lean_object* v___f_12_, lean_object* v___f_13_, lean_object* v_maxFVar_14_, lean_object* v_minIndex_15_, lean_object* v_lctx_16_, lean_object* v___x_17_, lean_object* v___x_18_, lean_object* v_e_19_, lean_object* v_offset_20_, uint8_t v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toDeBruijn_x3f_10_ = stack[0].m_obj;
lean_object* v___x_11_ = stack[1].m_obj;
lean_object* v___f_12_ = stack[2].m_obj;
lean_object* v___f_13_ = stack[3].m_obj;
lean_object* v_maxFVar_14_ = stack[4].m_obj;
lean_object* v_minIndex_15_ = stack[5].m_obj;
lean_object* v_lctx_16_ = stack[6].m_obj;
lean_object* v___x_17_ = stack[7].m_obj;
lean_object* v___x_18_ = stack[8].m_obj;
lean_object* v_e_19_ = stack[9].m_obj;
lean_object* v_offset_20_ = stack[10].m_obj;
uint8_t v___y_21_ = stack[11].m_num;
lean_object* v___y_22_ = stack[12].m_obj;
lean_object* v___y_23_ = stack[13].m_obj;
lean_object* v_res_92_;
v_res_92_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(v_toDeBruijn_x3f_10_, v___x_11_, v___f_12_, v___f_13_, v_maxFVar_14_, v_minIndex_15_, v_lctx_16_, v___x_17_, v___x_18_, v_e_19_, v_offset_20_, v___y_21_, v___y_22_, v___y_23_);
stack->m_obj
 = v_res_92_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed(lean_object* v_toDeBruijn_x3f_93_, lean_object* v___x_94_, lean_object* v___f_95_, lean_object* v___f_96_, lean_object* v_maxFVar_97_, lean_object* v_minIndex_98_, lean_object* v_lctx_99_, lean_object* v___x_100_, lean_object* v___x_101_, lean_object* v_e_102_, lean_object* v_offset_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
uint8_t v___y_2602__boxed_107_; lean_object* v_res_108_; 
v___y_2602__boxed_107_ = lean_unbox(v___y_104_);
v_res_108_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(v_toDeBruijn_x3f_93_, v___x_94_, v___f_95_, v___f_96_, v_maxFVar_97_, v_minIndex_98_, v_lctx_99_, v___x_100_, v___x_101_, v_e_102_, v_offset_103_, v___y_2602__boxed_107_, v___y_105_, v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v_offset_103_);
lean_dec(v___x_101_);
lean_dec_ref(v___x_100_);
lean_dec(v_minIndex_98_);
lean_dec_ref(v_maxFVar_97_);
return v_res_108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = lean_box(0);
v___x_112_ = lean_unsigned_to_nat(16u);
v___x_113_ = lean_mk_array(v___x_112_, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__3(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___x_114_);
return v___x_116_;
}
}
lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(lean_object* v_e_117_, lean_object* v_lctx_118_, lean_object* v_maxFVar_119_, lean_object* v_minFVarId_120_, lean_object* v_toDeBruijn_x3f_121_, uint8_t v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___f_128_; lean_object* v___f_129_; lean_object* v___y_131_; lean_object* v___x_232_; 
v___x_125_ = l_Lean_instInhabitedLocalDecl_default;
v___x_126_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
v___x_127_ = lean_box(0);
v___f_128_ = ((lean_object*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0));
v___f_129_ = ((lean_object*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1));
lean_inc_ref(v_lctx_118_);
v___x_232_ = lean_local_ctx_find(v_lctx_118_, v_minFVarId_120_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_234_ = l_panic___redArg(v___x_125_, v___x_233_);
v___y_131_ = v___x_234_;
goto v___jp_130_;
}
else
{
lean_object* v_val_235_; 
v_val_235_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_val_235_);
lean_dec_ref_known(v___x_232_, 1);
v___y_131_ = v_val_235_;
goto v___jp_130_;
}
v___jp_130_:
{
lean_object* v_minIndex_132_; lean_object* v___f_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_minIndex_132_ = l_Lean_LocalDecl_index(v___y_131_);
lean_dec_ref(v___y_131_);
lean_inc_ref(v_lctx_118_);
lean_inc(v_minIndex_132_);
lean_inc_ref(v_maxFVar_119_);
lean_inc_ref(v_toDeBruijn_x3f_121_);
v___f_133_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed), 14, 9);
lean_closure_set(v___f_133_, 0, v_toDeBruijn_x3f_121_);
lean_closure_set(v___f_133_, 1, v___x_126_);
lean_closure_set(v___f_133_, 2, v___f_128_);
lean_closure_set(v___f_133_, 3, v___f_129_);
lean_closure_set(v___f_133_, 4, v_maxFVar_119_);
lean_closure_set(v___f_133_, 5, v_minIndex_132_);
lean_closure_set(v___f_133_, 6, v_lctx_118_);
lean_closure_set(v___f_133_, 7, v___x_125_);
lean_closure_set(v___f_133_, 8, v___x_127_);
v___x_134_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_e_117_);
v___x_135_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(v_toDeBruijn_x3f_121_, v___x_126_, v___f_128_, v___f_129_, v_maxFVar_119_, v_minIndex_132_, v_lctx_118_, v___x_125_, v___x_127_, v_e_117_, v___x_134_, v_a_122_, v_a_123_, v_a_124_);
lean_dec(v_minIndex_132_);
lean_dec_ref(v_maxFVar_119_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
if (lean_obj_tag(v_a_136_) == 1)
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_145_; 
lean_inc_ref(v_a_136_);
lean_dec_ref(v___f_133_);
lean_dec_ref(v_e_117_);
v_a_137_ = lean_ctor_get(v___x_135_, 1);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v___x_135_, 0);
lean_dec(v_unused_146_);
v___x_139_ = v___x_135_;
v_isShared_140_ = v_isSharedCheck_145_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_135_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_145_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v_val_141_; lean_object* v___x_143_; 
v_val_141_ = lean_ctor_get(v_a_136_, 0);
lean_inc(v_val_141_);
lean_dec_ref_known(v_a_136_, 1);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v_val_141_);
v___x_143_ = v___x_139_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_val_141_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_a_137_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
else
{
switch(lean_obj_tag(v_e_117_))
{
case 9:
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec_ref(v___f_133_);
v_a_147_ = lean_ctor_get(v___x_135_, 1);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_154_ == 0)
{
lean_object* v_unused_155_; 
v_unused_155_ = lean_ctor_get(v___x_135_, 0);
lean_dec(v_unused_155_);
v___x_149_ = v___x_135_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_135_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v_e_117_);
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_e_117_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
case 2:
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_dec_ref(v___f_133_);
v_a_156_ = lean_ctor_get(v___x_135_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_163_ == 0)
{
lean_object* v_unused_164_; 
v_unused_164_ = lean_ctor_get(v___x_135_, 0);
lean_dec(v_unused_164_);
v___x_158_ = v___x_135_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_135_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v_e_117_);
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_e_117_);
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
case 0:
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_dec_ref(v___f_133_);
v_a_165_ = lean_ctor_get(v___x_135_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_172_ == 0)
{
lean_object* v_unused_173_; 
v_unused_173_ = lean_ctor_get(v___x_135_, 0);
lean_dec(v_unused_173_);
v___x_167_ = v___x_135_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_135_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v_e_117_);
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_e_117_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
case 1:
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_dec_ref(v___f_133_);
v_a_174_ = lean_ctor_get(v___x_135_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; 
v_unused_182_ = lean_ctor_get(v___x_135_, 0);
lean_dec(v_unused_182_);
v___x_176_ = v___x_135_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_135_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v_e_117_);
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_e_117_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
case 4:
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
lean_dec_ref(v___f_133_);
v_a_183_ = lean_ctor_get(v___x_135_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; 
v_unused_191_ = lean_ctor_get(v___x_135_, 0);
lean_dec(v_unused_191_);
v___x_185_ = v___x_135_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_135_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v_e_117_);
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_e_117_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
case 3:
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec_ref(v___f_133_);
v_a_192_ = lean_ctor_get(v___x_135_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_199_ == 0)
{
lean_object* v_unused_200_; 
v_unused_200_ = lean_ctor_get(v___x_135_, 0);
lean_dec(v_unused_200_);
v___x_194_ = v___x_135_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_135_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v_e_117_);
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_e_117_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
default: 
{
lean_object* v_a_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_a_201_ = lean_ctor_get(v___x_135_, 1);
lean_inc(v_a_201_);
lean_dec_ref_known(v___x_135_, 2);
v___x_202_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__3);
v___x_203_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_117_, v___x_134_, v___f_133_, v___x_202_, v_a_122_, v_a_123_, v_a_201_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_204_; lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_213_; 
v_a_204_ = lean_ctor_get(v___x_203_, 0);
v_a_205_ = lean_ctor_get(v___x_203_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_213_ == 0)
{
v___x_207_ = v___x_203_;
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_inc(v_a_204_);
lean_dec(v___x_203_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_fst_209_; lean_object* v___x_211_; 
v_fst_209_ = lean_ctor_get(v_a_204_, 0);
lean_inc(v_fst_209_);
lean_dec(v_a_204_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v_fst_209_);
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_fst_209_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_a_205_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
else
{
lean_object* v_a_214_; lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
v_a_214_ = lean_ctor_get(v___x_203_, 0);
v_a_215_ = lean_ctor_get(v___x_203_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_203_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_inc(v_a_214_);
lean_dec(v___x_203_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_214_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_223_; lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
lean_dec_ref(v___f_133_);
lean_dec_ref(v_e_117_);
v_a_223_ = lean_ctor_get(v___x_135_, 0);
v_a_224_ = lean_ctor_get(v___x_135_, 1);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_135_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_inc(v_a_223_);
lean_dec(v___x_135_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_223_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_117_ = stack[0].m_obj;
lean_object* v_lctx_118_ = stack[1].m_obj;
lean_object* v_maxFVar_119_ = stack[2].m_obj;
lean_object* v_minFVarId_120_ = stack[3].m_obj;
lean_object* v_toDeBruijn_x3f_121_ = stack[4].m_obj;
uint8_t v_a_122_ = stack[5].m_num;
lean_object* v_a_123_ = stack[6].m_obj;
lean_object* v_a_124_ = stack[7].m_obj;
lean_object* v_res_236_;
v_res_236_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(v_e_117_, v_lctx_118_, v_maxFVar_119_, v_minFVarId_120_, v_toDeBruijn_x3f_121_, v_a_122_, v_a_123_, v_a_124_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___boxed(lean_object* v_e_237_, lean_object* v_lctx_238_, lean_object* v_maxFVar_239_, lean_object* v_minFVarId_240_, lean_object* v_toDeBruijn_x3f_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
uint8_t v_a_boxed_245_; lean_object* v_res_246_; 
v_a_boxed_245_ = lean_unbox(v_a_242_);
v_res_246_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(v_e_237_, v_lctx_238_, v_maxFVar_239_, v_minFVarId_240_, v_toDeBruijn_x3f_241_, v_a_boxed_245_, v_a_243_, v_a_244_);
lean_dec_ref(v_a_243_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(lean_object* v_start_247_, lean_object* v_xs_248_, lean_object* v_fvarId_249_, lean_object* v_bidx_250_, lean_object* v_i_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_252_ = lean_array_fget_borrowed(v_xs_248_, v_i_251_);
v___x_253_ = l_Lean_Expr_fvarId_x21(v___x_252_);
v___x_254_ = l_Lean_instBEqFVarId_beq(v___x_253_, v_fvarId_249_);
lean_dec(v___x_253_);
if (v___x_254_ == 0)
{
uint8_t v___x_255_; 
v___x_255_ = lean_nat_dec_lt(v_start_247_, v_i_251_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_dec(v_i_251_);
lean_dec(v_bidx_250_);
v___x_256_ = lean_box(0);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_add(v_bidx_250_, v___x_257_);
lean_dec(v_bidx_250_);
v___x_259_ = lean_nat_sub(v_i_251_, v___x_257_);
lean_dec(v_i_251_);
v_bidx_250_ = v___x_258_;
v_i_251_ = v___x_259_;
goto _start;
}
}
else
{
lean_object* v___x_261_; 
lean_dec(v_i_251_);
v___x_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_261_, 0, v_bidx_250_);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg___boxed(lean_object* v_start_262_, lean_object* v_xs_263_, lean_object* v_fvarId_264_, lean_object* v_bidx_265_, lean_object* v_i_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_262_, v_xs_263_, v_fvarId_264_, v_bidx_265_, v_i_266_);
lean_dec(v_fvarId_264_);
lean_dec_ref(v_xs_263_);
lean_dec(v_start_262_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(lean_object* v_start_268_, lean_object* v_xs_269_, lean_object* v_fvarId_270_, lean_object* v_bidx_271_, lean_object* v_i_272_, lean_object* v_h_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_268_, v_xs_269_, v_fvarId_270_, v_bidx_271_, v_i_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___boxed(lean_object* v_start_275_, lean_object* v_xs_276_, lean_object* v_fvarId_277_, lean_object* v_bidx_278_, lean_object* v_i_279_, lean_object* v_h_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(v_start_275_, v_xs_276_, v_fvarId_277_, v_bidx_278_, v_i_279_, v_h_280_);
lean_dec(v_fvarId_277_);
lean_dec_ref(v_xs_276_);
lean_dec(v_start_275_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(lean_object* v_msg_282_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = l_Lean_instInhabitedLocalDecl_default;
v___x_284_ = lean_panic_fn_borrowed(v___x_283_, v_msg_282_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(lean_object* v_idx_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = l_Lean_Expr_bvar___override(v_idx_285_);
v___x_288_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_287_, v___y_286_);
return v___x_288_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(lean_object* v_idx_289_, uint8_t v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v_idx_289_, v___y_292_);
return v___x_293_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_idx_289_ = stack[0].m_obj;
uint8_t v___y_290_ = stack[1].m_num;
lean_object* v___y_291_ = stack[2].m_obj;
lean_object* v___y_292_ = stack[3].m_obj;
lean_object* v_res_294_;
v_res_294_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v_idx_289_, v___y_290_, v___y_291_, v___y_292_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___boxed(lean_object* v_idx_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
uint8_t v___y_25621__boxed_299_; lean_object* v_res_300_; 
v___y_25621__boxed_299_ = lean_unbox(v___y_296_);
v_res_300_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v_idx_295_, v___y_25621__boxed_299_, v___y_297_, v___y_298_);
lean_dec_ref(v___y_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(lean_object* v_msg_301_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_box(0);
v___x_303_ = lean_panic_fn_borrowed(v___x_302_, v_msg_301_);
return v___x_303_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0(void){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_304_;
}
}
lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(lean_object* v_msg_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_2413__overap_314_; lean_object* v___x_315_; 
v___x_313_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0, &l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0);
v___x_2413__overap_314_ = lean_panic_fn_borrowed(v___x_313_, v_msg_305_);
lean_inc(v___y_311_);
lean_inc_ref(v___y_310_);
lean_inc(v___y_309_);
lean_inc_ref(v___y_308_);
lean_inc(v___y_307_);
lean_inc_ref(v___y_306_);
v___x_315_ = lean_apply_7(v___x_2413__overap_314_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, lean_box(0));
return v___x_315_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_305_ = stack[0].m_obj;
lean_object* v___y_306_ = stack[1].m_obj;
lean_object* v___y_307_ = stack[2].m_obj;
lean_object* v___y_308_ = stack[3].m_obj;
lean_object* v___y_309_ = stack[4].m_obj;
lean_object* v___y_310_ = stack[5].m_obj;
lean_object* v___y_311_ = stack[6].m_obj;
lean_object* v_res_316_;
v_res_316_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v_msg_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
stack->m_obj
 = v_res_316_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___boxed(lean_object* v_msg_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v_msg_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
return v_res_325_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(lean_object* v_msg_333_, lean_object* v___y_334_, uint8_t v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___f_338_; lean_object* v___f_339_; lean_object* v___f_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___f_350_; lean_object* v___f_351_; lean_object* v___f_352_; lean_object* v___f_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_25037__overap_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___f_338_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__0));
v___f_339_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__1));
v___f_340_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__2));
v___x_341_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__3));
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___f_338_);
v___x_343_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__4));
v___x_344_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__5));
v___x_345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_345_, 0, v___x_342_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
lean_ctor_set(v___x_345_, 2, v___f_339_);
lean_ctor_set(v___x_345_, 3, v___f_340_);
lean_ctor_set(v___x_345_, 4, v___x_344_);
v___x_346_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__6));
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_345_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = l_ReaderT_instMonad___redArg(v___x_347_);
v___x_349_ = l_ReaderT_instMonad___redArg(v___x_348_);
lean_inc_ref_n(v___x_349_, 6);
v___f_350_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_350_, 0, v___x_349_);
v___f_351_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_351_, 0, v___x_349_);
v___f_352_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_352_, 0, v___x_349_);
v___f_353_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_353_, 0, v___x_349_);
v___x_354_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_354_, 0, lean_box(0));
lean_closure_set(v___x_354_, 1, lean_box(0));
lean_closure_set(v___x_354_, 2, v___x_349_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___f_350_);
v___x_356_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_356_, 0, lean_box(0));
lean_closure_set(v___x_356_, 1, lean_box(0));
lean_closure_set(v___x_356_, 2, v___x_349_);
v___x_357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_357_, 0, v___x_355_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
lean_ctor_set(v___x_357_, 2, v___f_351_);
lean_ctor_set(v___x_357_, 3, v___f_352_);
lean_ctor_set(v___x_357_, 4, v___f_353_);
v___x_358_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_358_, 0, lean_box(0));
lean_closure_set(v___x_358_, 1, lean_box(0));
lean_closure_set(v___x_358_, 2, v___x_349_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = l_Lean_instInhabitedExpr;
v___x_361_ = l_instInhabitedOfMonad___redArg(v___x_359_, v___x_360_);
v___x_25037__overap_362_ = lean_panic_fn_borrowed(v___x_361_, v_msg_333_);
lean_dec(v___x_361_);
v___x_363_ = lean_box(v___y_335_);
lean_inc_ref(v___y_336_);
v___x_364_ = lean_apply_4(v___x_25037__overap_362_, v___y_334_, v___x_363_, v___y_336_, v___y_337_);
return v___x_364_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_333_ = stack[0].m_obj;
lean_object* v___y_334_ = stack[1].m_obj;
uint8_t v___y_335_ = stack[2].m_num;
lean_object* v___y_336_ = stack[3].m_obj;
lean_object* v___y_337_ = stack[4].m_obj;
lean_object* v_res_365_;
v_res_365_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(v_msg_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
stack->m_obj
 = v_res_365_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___boxed(lean_object* v_msg_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
uint8_t v___y_25705__boxed_371_; lean_object* v_res_372_; 
v___y_25705__boxed_371_ = lean_unbox(v___y_368_);
v_res_372_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(v_msg_366_, v___y_367_, v___y_25705__boxed_371_, v___y_369_, v___y_370_);
lean_dec_ref(v___y_369_);
return v_res_372_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(lean_object* v_structName_373_, lean_object* v_idx_374_, lean_object* v_struct_375_, lean_object* v___y_376_, uint8_t v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___y_381_; lean_object* v___y_382_; 
if (v___y_377_ == 0)
{
v___y_381_ = v___y_376_;
v___y_382_ = v___y_379_;
goto v___jp_380_;
}
else
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_375_, v___y_377_, v___y_378_, v___y_379_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; 
v_a_405_ = lean_ctor_get(v___x_404_, 1);
lean_inc(v_a_405_);
lean_dec_ref_known(v___x_404_, 2);
v___y_381_ = v___y_376_;
v___y_382_ = v_a_405_;
goto v___jp_380_;
}
else
{
lean_object* v_a_406_; lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec_ref(v___y_376_);
lean_dec_ref(v_struct_375_);
lean_dec(v_idx_374_);
lean_dec(v_structName_373_);
v_a_406_ = lean_ctor_get(v___x_404_, 0);
v_a_407_ = lean_ctor_get(v___x_404_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_404_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_inc(v_a_406_);
lean_dec(v___x_404_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_406_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
v___jp_380_:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = l_Lean_Expr_proj___override(v_structName_373_, v_idx_374_, v_struct_375_);
v___x_384_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_383_, v___y_382_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_394_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_a_386_ = lean_ctor_get(v___x_384_, 1);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_394_ == 0)
{
v___x_388_ = v___x_384_;
v_isShared_389_ = v_isSharedCheck_394_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_394_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_a_385_);
lean_ctor_set(v___x_390_, 1, v___y_381_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_390_);
v___x_392_ = v___x_388_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_a_386_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
else
{
lean_object* v_a_395_; lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec_ref(v___y_381_);
v_a_395_ = lean_ctor_get(v___x_384_, 0);
v_a_396_ = lean_ctor_get(v___x_384_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_384_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_inc(v_a_395_);
lean_dec(v___x_384_);
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
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_structName_373_ = stack[0].m_obj;
lean_object* v_idx_374_ = stack[1].m_obj;
lean_object* v_struct_375_ = stack[2].m_obj;
lean_object* v___y_376_ = stack[3].m_obj;
uint8_t v___y_377_ = stack[4].m_num;
lean_object* v___y_378_ = stack[5].m_obj;
lean_object* v___y_379_ = stack[6].m_obj;
lean_object* v_res_415_;
v_res_415_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(v_structName_373_, v_idx_374_, v_struct_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11___boxed(lean_object* v_structName_416_, lean_object* v_idx_417_, lean_object* v_struct_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
uint8_t v___y_25817__boxed_423_; lean_object* v_res_424_; 
v___y_25817__boxed_423_ = lean_unbox(v___y_420_);
v_res_424_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(v_structName_416_, v_idx_417_, v_struct_418_, v___y_419_, v___y_25817__boxed_423_, v___y_421_, v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_424_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(lean_object* v_d_425_, lean_object* v_e_426_, lean_object* v___y_427_, uint8_t v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
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
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_425_ = stack[0].m_obj;
lean_object* v_e_426_ = stack[1].m_obj;
lean_object* v___y_427_ = stack[2].m_obj;
uint8_t v___y_428_ = stack[3].m_num;
lean_object* v___y_429_ = stack[4].m_obj;
lean_object* v___y_430_ = stack[5].m_obj;
lean_object* v_res_466_;
v_res_466_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(v_d_425_, v_e_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
stack->m_obj
 = v_res_466_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10___boxed(lean_object* v_d_467_, lean_object* v_e_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
uint8_t v___y_25943__boxed_473_; lean_object* v_res_474_; 
v___y_25943__boxed_473_ = lean_unbox(v___y_470_);
v_res_474_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(v_d_467_, v_e_468_, v___y_469_, v___y_25943__boxed_473_, v___y_471_, v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(lean_object* v_keys_475_, lean_object* v_vals_476_, lean_object* v_i_477_, lean_object* v_k_478_){
_start:
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_array_get_size(v_keys_475_);
v___x_480_ = lean_nat_dec_lt(v_i_477_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
lean_dec(v_i_477_);
v___x_481_ = lean_box(0);
return v___x_481_;
}
else
{
lean_object* v_k_x27_482_; size_t v___x_483_; size_t v___x_484_; uint8_t v___x_485_; 
v_k_x27_482_ = lean_array_fget_borrowed(v_keys_475_, v_i_477_);
v___x_483_ = lean_ptr_addr(v_k_478_);
v___x_484_ = lean_ptr_addr(v_k_x27_482_);
v___x_485_ = lean_usize_dec_eq(v___x_483_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_add(v_i_477_, v___x_486_);
lean_dec(v_i_477_);
v_i_477_ = v___x_487_;
goto _start;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_array_fget_borrowed(v_vals_476_, v_i_477_);
lean_dec(v_i_477_);
lean_inc(v___x_489_);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_keys_491_, lean_object* v_vals_492_, lean_object* v_i_493_, lean_object* v_k_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_keys_491_, v_vals_492_, v_i_493_, v_k_494_);
lean_dec_ref(v_k_494_);
lean_dec_ref(v_vals_492_);
lean_dec_ref(v_keys_491_);
return v_res_495_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(lean_object* v_x_496_, size_t v_x_497_, lean_object* v_x_498_){
_start:
{
if (lean_obj_tag(v_x_496_) == 0)
{
lean_object* v_es_499_; lean_object* v___x_500_; size_t v___x_501_; size_t v___x_502_; lean_object* v_j_503_; lean_object* v___x_504_; 
v_es_499_ = lean_ctor_get(v_x_496_, 0);
v___x_500_ = lean_box(2);
v___x_501_ = ((size_t)31ULL);
v___x_502_ = lean_usize_land(v_x_497_, v___x_501_);
v_j_503_ = lean_usize_to_nat(v___x_502_);
v___x_504_ = lean_array_get_borrowed(v___x_500_, v_es_499_, v_j_503_);
lean_dec(v_j_503_);
switch(lean_obj_tag(v___x_504_))
{
case 0:
{
lean_object* v_key_505_; lean_object* v_val_506_; size_t v___x_507_; size_t v___x_508_; uint8_t v___x_509_; 
v_key_505_ = lean_ctor_get(v___x_504_, 0);
v_val_506_ = lean_ctor_get(v___x_504_, 1);
v___x_507_ = lean_ptr_addr(v_x_498_);
v___x_508_ = lean_ptr_addr(v_key_505_);
v___x_509_ = lean_usize_dec_eq(v___x_507_, v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
v___x_510_ = lean_box(0);
return v___x_510_;
}
else
{
lean_object* v___x_511_; 
lean_inc(v_val_506_);
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v_val_506_);
return v___x_511_;
}
}
case 1:
{
lean_object* v_node_512_; size_t v___x_513_; size_t v___x_514_; 
v_node_512_ = lean_ctor_get(v___x_504_, 0);
v___x_513_ = ((size_t)5ULL);
v___x_514_ = lean_usize_shift_right(v_x_497_, v___x_513_);
v_x_496_ = v_node_512_;
v_x_497_ = v___x_514_;
goto _start;
}
default: 
{
lean_object* v___x_516_; 
v___x_516_ = lean_box(0);
return v___x_516_;
}
}
}
else
{
lean_object* v_ks_517_; lean_object* v_vs_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_ks_517_ = lean_ctor_get(v_x_496_, 0);
v_vs_518_ = lean_ctor_get(v_x_496_, 1);
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_ks_517_, v_vs_518_, v___x_519_, v_x_498_);
return v___x_520_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_496_ = stack[0].m_obj;
size_t v_x_497_ = stack[1].m_num;
lean_object* v_x_498_ = stack[2].m_obj;
lean_object* v_res_521_;
v_res_521_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_496_, v_x_497_, v_x_498_);
stack->m_obj
 = v_res_521_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg___boxed(lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
size_t v_x_26102__boxed_525_; lean_object* v_res_526_; 
v_x_26102__boxed_525_ = lean_unbox_usize(v_x_523_);
lean_dec(v_x_523_);
v_res_526_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_522_, v_x_26102__boxed_525_, v_x_524_);
lean_dec_ref(v_x_524_);
lean_dec_ref(v_x_522_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
size_t v___x_529_; size_t v___x_530_; size_t v___x_531_; uint64_t v___x_532_; size_t v___x_533_; lean_object* v___x_534_; 
v___x_529_ = lean_ptr_addr(v_x_528_);
v___x_530_ = ((size_t)3ULL);
v___x_531_ = lean_usize_shift_right(v___x_529_, v___x_530_);
v___x_532_ = lean_usize_to_uint64(v___x_531_);
v___x_533_ = lean_uint64_to_usize(v___x_532_);
v___x_534_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_527_, v___x_533_, v_x_528_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg___boxed(lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_x_535_, v_x_536_);
lean_dec_ref(v_x_536_);
lean_dec_ref(v_x_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(lean_object* v_a_538_, lean_object* v_x_539_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v___x_540_; 
v___x_540_ = lean_box(0);
return v___x_540_;
}
else
{
lean_object* v_key_541_; lean_object* v_value_542_; lean_object* v_tail_543_; lean_object* v_fst_544_; lean_object* v_snd_545_; lean_object* v_fst_546_; lean_object* v_snd_547_; size_t v___x_548_; size_t v___x_549_; uint8_t v___x_550_; 
v_key_541_ = lean_ctor_get(v_x_539_, 0);
v_value_542_ = lean_ctor_get(v_x_539_, 1);
v_tail_543_ = lean_ctor_get(v_x_539_, 2);
v_fst_544_ = lean_ctor_get(v_key_541_, 0);
v_snd_545_ = lean_ctor_get(v_key_541_, 1);
v_fst_546_ = lean_ctor_get(v_a_538_, 0);
v_snd_547_ = lean_ctor_get(v_a_538_, 1);
v___x_548_ = lean_ptr_addr(v_fst_544_);
v___x_549_ = lean_ptr_addr(v_fst_546_);
v___x_550_ = lean_usize_dec_eq(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
v_x_539_ = v_tail_543_;
goto _start;
}
else
{
uint8_t v___x_552_; 
v___x_552_ = lean_nat_dec_eq(v_snd_545_, v_snd_547_);
if (v___x_552_ == 0)
{
v_x_539_ = v_tail_543_;
goto _start;
}
else
{
lean_object* v___x_554_; 
lean_inc(v_value_542_);
v___x_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_554_, 0, v_value_542_);
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg___boxed(lean_object* v_a_555_, lean_object* v_x_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_a_555_, v_x_556_);
lean_dec(v_x_556_);
lean_dec_ref(v_a_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(lean_object* v_m_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_buckets_560_; lean_object* v_fst_561_; lean_object* v_snd_562_; lean_object* v___x_563_; size_t v___x_564_; size_t v___x_565_; size_t v___x_566_; uint64_t v___x_567_; uint64_t v___x_568_; uint64_t v___x_569_; uint64_t v___x_570_; uint64_t v___x_571_; uint64_t v_fold_572_; uint64_t v___x_573_; uint64_t v___x_574_; uint64_t v___x_575_; size_t v___x_576_; size_t v___x_577_; size_t v___x_578_; size_t v___x_579_; size_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_buckets_560_ = lean_ctor_get(v_m_558_, 1);
v_fst_561_ = lean_ctor_get(v_a_559_, 0);
v_snd_562_ = lean_ctor_get(v_a_559_, 1);
v___x_563_ = lean_array_get_size(v_buckets_560_);
v___x_564_ = lean_ptr_addr(v_fst_561_);
v___x_565_ = ((size_t)3ULL);
v___x_566_ = lean_usize_shift_right(v___x_564_, v___x_565_);
v___x_567_ = lean_usize_to_uint64(v___x_566_);
v___x_568_ = lean_uint64_of_nat(v_snd_562_);
v___x_569_ = lean_uint64_mix_hash(v___x_567_, v___x_568_);
v___x_570_ = 32ULL;
v___x_571_ = lean_uint64_shift_right(v___x_569_, v___x_570_);
v_fold_572_ = lean_uint64_xor(v___x_569_, v___x_571_);
v___x_573_ = 16ULL;
v___x_574_ = lean_uint64_shift_right(v_fold_572_, v___x_573_);
v___x_575_ = lean_uint64_xor(v_fold_572_, v___x_574_);
v___x_576_ = lean_uint64_to_usize(v___x_575_);
v___x_577_ = lean_usize_of_nat(v___x_563_);
v___x_578_ = ((size_t)1ULL);
v___x_579_ = lean_usize_sub(v___x_577_, v___x_578_);
v___x_580_ = lean_usize_land(v___x_576_, v___x_579_);
v___x_581_ = lean_array_uget_borrowed(v_buckets_560_, v___x_580_);
v___x_582_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_a_559_, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_m_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_m_583_, v_a_584_);
lean_dec_ref(v_a_584_);
lean_dec_ref(v_m_583_);
return v_res_585_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(lean_object* v_x_586_, uint8_t v_bi_587_, lean_object* v_t_588_, lean_object* v_b_589_, lean_object* v___y_590_, uint8_t v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___y_595_; lean_object* v___y_596_; 
if (v___y_591_ == 0)
{
v___y_595_ = v___y_590_;
v___y_596_ = v___y_593_;
goto v___jp_594_;
}
else
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_588_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_620_; 
v_a_619_ = lean_ctor_get(v___x_618_, 1);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_618_, 2);
v___x_620_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_589_, v___y_591_, v___y_592_, v_a_619_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; 
v_a_621_ = lean_ctor_get(v___x_620_, 1);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 2);
v___y_595_ = v___y_590_;
v___y_596_ = v_a_621_;
goto v___jp_594_;
}
else
{
lean_object* v_a_622_; lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v___y_590_);
lean_dec_ref(v_b_589_);
lean_dec_ref(v_t_588_);
lean_dec(v_x_586_);
v_a_622_ = lean_ctor_get(v___x_620_, 0);
v_a_623_ = lean_ctor_get(v___x_620_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_620_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_inc(v_a_622_);
lean_dec(v___x_620_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_622_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_a_623_);
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
else
{
lean_object* v_a_631_; lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec_ref(v___y_590_);
lean_dec_ref(v_b_589_);
lean_dec_ref(v_t_588_);
lean_dec(v_x_586_);
v_a_631_ = lean_ctor_get(v___x_618_, 0);
v_a_632_ = lean_ctor_get(v___x_618_, 1);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_618_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_inc(v_a_631_);
lean_dec(v___x_618_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_631_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
v___jp_594_:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = l_Lean_Expr_forallE___override(v_x_586_, v_t_588_, v_b_589_, v_bi_587_);
v___x_598_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_597_, v___y_596_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_608_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_a_600_ = lean_ctor_get(v___x_598_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_608_ == 0)
{
v___x_602_ = v___x_598_;
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v_a_599_);
lean_ctor_set(v___x_604_, 1, v___y_595_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_604_);
v___x_606_ = v___x_602_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_a_600_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
else
{
lean_object* v_a_609_; lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v___y_595_);
v_a_609_ = lean_ctor_get(v___x_598_, 0);
v_a_610_ = lean_ctor_get(v___x_598_, 1);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_598_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_inc(v_a_609_);
lean_dec(v___x_598_);
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
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_586_ = stack[0].m_obj;
uint8_t v_bi_587_ = stack[1].m_num;
lean_object* v_t_588_ = stack[2].m_obj;
lean_object* v_b_589_ = stack[3].m_obj;
lean_object* v___y_590_ = stack[4].m_obj;
uint8_t v___y_591_ = stack[5].m_num;
lean_object* v___y_592_ = stack[6].m_obj;
lean_object* v___y_593_ = stack[7].m_obj;
lean_object* v_res_640_;
v_res_640_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_x_586_, v_bi_587_, v_t_588_, v_b_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
stack->m_obj
 = v_res_640_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8___boxed(lean_object* v_x_641_, lean_object* v_bi_642_, lean_object* v_t_643_, lean_object* v_b_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
uint8_t v_bi_boxed_649_; uint8_t v___y_26324__boxed_650_; lean_object* v_res_651_; 
v_bi_boxed_649_ = lean_unbox(v_bi_642_);
v___y_26324__boxed_650_ = lean_unbox(v___y_646_);
v_res_651_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_x_641_, v_bi_boxed_649_, v_t_643_, v_b_644_, v___y_645_, v___y_26324__boxed_650_, v___y_647_, v___y_648_);
lean_dec_ref(v___y_647_);
return v_res_651_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(lean_object* v_x_652_, uint8_t v_bi_653_, lean_object* v_t_654_, lean_object* v_b_655_, lean_object* v___y_656_, uint8_t v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___y_661_; lean_object* v___y_662_; 
if (v___y_657_ == 0)
{
v___y_661_ = v___y_656_;
v___y_662_ = v___y_659_;
goto v___jp_660_;
}
else
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_654_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; 
v_a_685_ = lean_ctor_get(v___x_684_, 1);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 2);
v___x_686_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_655_, v___y_657_, v___y_658_, v_a_685_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; 
v_a_687_ = lean_ctor_get(v___x_686_, 1);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 2);
v___y_661_ = v___y_656_;
v___y_662_ = v_a_687_;
goto v___jp_660_;
}
else
{
lean_object* v_a_688_; lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec_ref(v___y_656_);
lean_dec_ref(v_b_655_);
lean_dec_ref(v_t_654_);
lean_dec(v_x_652_);
v_a_688_ = lean_ctor_get(v___x_686_, 0);
v_a_689_ = lean_ctor_get(v___x_686_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_686_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_inc(v_a_688_);
lean_dec(v___x_686_);
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
else
{
lean_object* v_a_697_; lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec_ref(v___y_656_);
lean_dec_ref(v_b_655_);
lean_dec_ref(v_t_654_);
lean_dec(v_x_652_);
v_a_697_ = lean_ctor_get(v___x_684_, 0);
v_a_698_ = lean_ctor_get(v___x_684_, 1);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_684_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_inc(v_a_697_);
lean_dec(v___x_684_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_697_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
v___jp_660_:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = l_Lean_Expr_lam___override(v_x_652_, v_t_654_, v_b_655_, v_bi_653_);
v___x_664_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_663_, v___y_662_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_674_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
v_a_666_ = lean_ctor_get(v___x_664_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_674_ == 0)
{
v___x_668_ = v___x_664_;
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_inc(v_a_665_);
lean_dec(v___x_664_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v_a_665_);
lean_ctor_set(v___x_670_, 1, v___y_661_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_670_);
v___x_672_ = v___x_668_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_a_666_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
else
{
lean_object* v_a_675_; lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v___y_661_);
v_a_675_ = lean_ctor_get(v___x_664_, 0);
v_a_676_ = lean_ctor_get(v___x_664_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_664_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_inc(v_a_675_);
lean_dec(v___x_664_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_675_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_a_676_);
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
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_652_ = stack[0].m_obj;
uint8_t v_bi_653_ = stack[1].m_num;
lean_object* v_t_654_ = stack[2].m_obj;
lean_object* v_b_655_ = stack[3].m_obj;
lean_object* v___y_656_ = stack[4].m_obj;
uint8_t v___y_657_ = stack[5].m_num;
lean_object* v___y_658_ = stack[6].m_obj;
lean_object* v___y_659_ = stack[7].m_obj;
lean_object* v_res_706_;
v_res_706_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_x_652_, v_bi_653_, v_t_654_, v_b_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
stack->m_obj
 = v_res_706_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7___boxed(lean_object* v_x_707_, lean_object* v_bi_708_, lean_object* v_t_709_, lean_object* v_b_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
uint8_t v_bi_boxed_715_; uint8_t v___y_26484__boxed_716_; lean_object* v_res_717_; 
v_bi_boxed_715_ = lean_unbox(v_bi_708_);
v___y_26484__boxed_716_ = lean_unbox(v___y_712_);
v_res_717_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_x_707_, v_bi_boxed_715_, v_t_709_, v_b_710_, v___y_711_, v___y_26484__boxed_716_, v___y_713_, v___y_714_);
lean_dec_ref(v___y_713_);
return v_res_717_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(lean_object* v_x_718_, lean_object* v_t_719_, lean_object* v_v_720_, lean_object* v_b_721_, uint8_t v_nondep_722_, lean_object* v___y_723_, uint8_t v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___y_728_; lean_object* v___y_729_; 
if (v___y_724_ == 0)
{
v___y_728_ = v___y_723_;
v___y_729_ = v___y_726_;
goto v___jp_727_;
}
else
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_719_, v___y_724_, v___y_725_, v___y_726_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; 
v_a_752_ = lean_ctor_get(v___x_751_, 1);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 2);
v___x_753_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_720_, v___y_724_, v___y_725_, v_a_752_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_755_; 
v_a_754_ = lean_ctor_get(v___x_753_, 1);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 2);
v___x_755_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_721_, v___y_724_, v___y_725_, v_a_754_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; 
v_a_756_ = lean_ctor_get(v___x_755_, 1);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 2);
v___y_728_ = v___y_723_;
v___y_729_ = v_a_756_;
goto v___jp_727_;
}
else
{
lean_object* v_a_757_; lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v___y_723_);
lean_dec_ref(v_b_721_);
lean_dec_ref(v_v_720_);
lean_dec_ref(v_t_719_);
lean_dec(v_x_718_);
v_a_757_ = lean_ctor_get(v___x_755_, 0);
v_a_758_ = lean_ctor_get(v___x_755_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_755_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_inc(v_a_757_);
lean_dec(v___x_755_);
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
else
{
lean_object* v_a_766_; lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec_ref(v___y_723_);
lean_dec_ref(v_b_721_);
lean_dec_ref(v_v_720_);
lean_dec_ref(v_t_719_);
lean_dec(v_x_718_);
v_a_766_ = lean_ctor_get(v___x_753_, 0);
v_a_767_ = lean_ctor_get(v___x_753_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_753_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_inc(v_a_766_);
lean_dec(v___x_753_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_766_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
else
{
lean_object* v_a_775_; lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v___y_723_);
lean_dec_ref(v_b_721_);
lean_dec_ref(v_v_720_);
lean_dec_ref(v_t_719_);
lean_dec(v_x_718_);
v_a_775_ = lean_ctor_get(v___x_751_, 0);
v_a_776_ = lean_ctor_get(v___x_751_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_751_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_inc(v_a_775_);
lean_dec(v___x_751_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_775_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
v___jp_727_:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = l_Lean_Expr_letE___override(v_x_718_, v_t_719_, v_v_720_, v_b_721_, v_nondep_722_);
v___x_731_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_730_, v___y_729_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_741_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_a_733_ = lean_ctor_get(v___x_731_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_741_ == 0)
{
v___x_735_ = v___x_731_;
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v_a_732_);
lean_ctor_set(v___x_737_, 1, v___y_728_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_737_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_a_733_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
else
{
lean_object* v_a_742_; lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec_ref(v___y_728_);
v_a_742_ = lean_ctor_get(v___x_731_, 0);
v_a_743_ = lean_ctor_get(v___x_731_, 1);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_731_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_inc(v_a_742_);
lean_dec(v___x_731_);
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
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_718_ = stack[0].m_obj;
lean_object* v_t_719_ = stack[1].m_obj;
lean_object* v_v_720_ = stack[2].m_obj;
lean_object* v_b_721_ = stack[3].m_obj;
uint8_t v_nondep_722_ = stack[4].m_num;
lean_object* v___y_723_ = stack[5].m_obj;
uint8_t v___y_724_ = stack[6].m_num;
lean_object* v___y_725_ = stack[7].m_obj;
lean_object* v___y_726_ = stack[8].m_obj;
lean_object* v_res_784_;
v_res_784_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_x_718_, v_t_719_, v_v_720_, v_b_721_, v_nondep_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
stack->m_obj
 = v_res_784_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9___boxed(lean_object* v_x_785_, lean_object* v_t_786_, lean_object* v_v_787_, lean_object* v_b_788_, lean_object* v_nondep_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
uint8_t v_nondep_boxed_794_; uint8_t v___y_26644__boxed_795_; lean_object* v_res_796_; 
v_nondep_boxed_794_ = lean_unbox(v_nondep_789_);
v___y_26644__boxed_795_ = lean_unbox(v___y_791_);
v_res_796_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_x_785_, v_t_786_, v_v_787_, v_b_788_, v_nondep_boxed_794_, v___y_790_, v___y_26644__boxed_795_, v___y_792_, v___y_793_);
lean_dec_ref(v___y_792_);
return v_res_796_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(lean_object* v_f_797_, lean_object* v_a_798_, lean_object* v___y_799_, uint8_t v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___y_804_; lean_object* v___y_805_; 
if (v___y_800_ == 0)
{
v___y_804_ = v___y_799_;
v___y_805_ = v___y_802_;
goto v___jp_803_;
}
else
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_797_, v___y_800_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_829_; 
v_a_828_ = lean_ctor_get(v___x_827_, 1);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 2);
v___x_829_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_798_, v___y_800_, v___y_801_, v_a_828_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; 
v_a_830_ = lean_ctor_get(v___x_829_, 1);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 2);
v___y_804_ = v___y_799_;
v___y_805_ = v_a_830_;
goto v___jp_803_;
}
else
{
lean_object* v_a_831_; lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec_ref(v___y_799_);
lean_dec_ref(v_a_798_);
lean_dec_ref(v_f_797_);
v_a_831_ = lean_ctor_get(v___x_829_, 0);
v_a_832_ = lean_ctor_get(v___x_829_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_829_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_inc(v_a_831_);
lean_dec(v___x_829_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_831_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec_ref(v___y_799_);
lean_dec_ref(v_a_798_);
lean_dec_ref(v_f_797_);
v_a_840_ = lean_ctor_get(v___x_827_, 0);
v_a_841_ = lean_ctor_get(v___x_827_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_827_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_inc(v_a_840_);
lean_dec(v___x_827_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_840_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
v___jp_803_:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = l_Lean_Expr_app___override(v_f_797_, v_a_798_);
v___x_807_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_806_, v___y_805_);
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
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v_a_808_);
lean_ctor_set(v___x_813_, 1, v___y_804_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_813_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
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
lean_dec_ref(v___y_804_);
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
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_797_ = stack[0].m_obj;
lean_object* v_a_798_ = stack[1].m_obj;
lean_object* v___y_799_ = stack[2].m_obj;
uint8_t v___y_800_ = stack[3].m_num;
lean_object* v___y_801_ = stack[4].m_obj;
lean_object* v___y_802_ = stack[5].m_obj;
lean_object* v_res_849_;
v_res_849_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_f_797_, v_a_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
stack->m_obj
 = v_res_849_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6___boxed(lean_object* v_f_850_, lean_object* v_a_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
uint8_t v___y_26838__boxed_856_; lean_object* v_res_857_; 
v___y_26838__boxed_856_ = lean_unbox(v___y_853_);
v_res_857_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_f_850_, v_a_851_, v___y_852_, v___y_26838__boxed_856_, v___y_854_, v___y_855_);
lean_dec_ref(v___y_854_);
return v_res_857_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_861_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__2));
v___x_862_ = lean_unsigned_to_nat(67u);
v___x_863_ = lean_unsigned_to_nat(35u);
v___x_864_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__1));
v___x_865_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__0));
v___x_866_ = l_mkPanicMessageWithDecl(v___x_865_, v___x_864_, v___x_863_, v___x_862_, v___x_861_);
return v___x_866_;
}
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(lean_object* v_minIndex_867_, lean_object* v___x_868_, lean_object* v___x_869_, lean_object* v_start_870_, lean_object* v_xs_871_, lean_object* v___x_872_, lean_object* v_e_873_, lean_object* v_offset_874_, lean_object* v_a_875_, uint8_t v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
switch(lean_obj_tag(v_e_873_))
{
case 5:
{
lean_object* v_fn_879_; lean_object* v_arg_880_; lean_object* v___x_881_; 
v_fn_879_ = lean_ctor_get(v_e_873_, 0);
v_arg_880_ = lean_ctor_get(v_e_873_, 1);
lean_inc(v_offset_874_);
lean_inc_ref(v_fn_879_);
lean_inc_ref(v___x_868_);
v___x_881_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_867_, v___x_868_, v___x_869_, v_start_870_, v_xs_871_, v___x_872_, v_fn_879_, v_offset_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v_a_883_; lean_object* v_fst_884_; lean_object* v_snd_885_; lean_object* v___x_886_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
v_a_883_ = lean_ctor_get(v___x_881_, 1);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_881_, 2);
v_fst_884_ = lean_ctor_get(v_a_882_, 0);
lean_inc(v_fst_884_);
v_snd_885_ = lean_ctor_get(v_a_882_, 1);
lean_inc(v_snd_885_);
lean_dec(v_a_882_);
lean_inc_ref(v_arg_880_);
v___x_886_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_867_, v___x_868_, v___x_869_, v_start_870_, v_xs_871_, v___x_872_, v_arg_880_, v_offset_874_, v_snd_885_, v_a_876_, v_a_877_, v_a_883_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_912_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
v_a_888_ = lean_ctor_get(v___x_886_, 1);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_912_ == 0)
{
v___x_890_ = v___x_886_;
v_isShared_891_ = v_isSharedCheck_912_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_inc(v_a_887_);
lean_dec(v___x_886_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_912_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_fst_892_; lean_object* v_snd_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_911_; 
v_fst_892_ = lean_ctor_get(v_a_887_, 0);
v_snd_893_ = lean_ctor_get(v_a_887_, 1);
v_isSharedCheck_911_ = !lean_is_exclusive(v_a_887_);
if (v_isSharedCheck_911_ == 0)
{
v___x_895_ = v_a_887_;
v_isShared_896_ = v_isSharedCheck_911_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_snd_893_);
lean_inc(v_fst_892_);
lean_dec(v_a_887_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_911_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
size_t v___x_897_; size_t v___x_898_; uint8_t v___x_899_; 
v___x_897_ = lean_ptr_addr(v_fn_879_);
v___x_898_ = lean_ptr_addr(v_fst_884_);
v___x_899_ = lean_usize_dec_eq(v___x_897_, v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; 
lean_del_object(v___x_895_);
lean_del_object(v___x_890_);
lean_dec_ref_known(v_e_873_, 2);
v___x_900_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_fst_884_, v_fst_892_, v_snd_893_, v_a_876_, v_a_877_, v_a_888_);
return v___x_900_;
}
else
{
size_t v___x_901_; size_t v___x_902_; uint8_t v___x_903_; 
v___x_901_ = lean_ptr_addr(v_arg_880_);
v___x_902_ = lean_ptr_addr(v_fst_892_);
v___x_903_ = lean_usize_dec_eq(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
lean_del_object(v___x_895_);
lean_del_object(v___x_890_);
lean_dec_ref_known(v_e_873_, 2);
v___x_904_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_fst_884_, v_fst_892_, v_snd_893_, v_a_876_, v_a_877_, v_a_888_);
return v___x_904_;
}
else
{
lean_object* v___x_906_; 
lean_dec(v_fst_892_);
lean_dec(v_fst_884_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v_e_873_);
v___x_906_ = v___x_895_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_e_873_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_snd_893_);
v___x_906_ = v_reuseFailAlloc_910_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_908_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_906_);
v___x_908_ = v___x_890_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_a_888_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_884_);
lean_dec_ref_known(v_e_873_, 2);
return v___x_886_;
}
}
else
{
lean_dec_ref_known(v_e_873_, 2);
lean_dec(v_offset_874_);
lean_dec_ref(v___x_868_);
return v___x_881_;
}
}
case 6:
{
lean_object* v_binderName_913_; lean_object* v_binderType_914_; lean_object* v_body_915_; uint8_t v_binderInfo_916_; lean_object* v___x_917_; 
v_binderName_913_ = lean_ctor_get(v_e_873_, 0);
v_binderType_914_ = lean_ctor_get(v_e_873_, 1);
v_body_915_ = lean_ctor_get(v_e_873_, 2);
v_binderInfo_916_ = lean_ctor_get_uint8(v_e_873_, sizeof(void*)*3 + 8);
lean_inc(v_offset_874_);
lean_inc_ref(v_binderType_914_);
lean_inc_ref(v___x_868_);
v___x_917_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_867_, v___x_868_, v___x_869_, v_start_870_, v_xs_871_, v___x_872_, v_binderType_914_, v_offset_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v_a_919_; lean_object* v_fst_920_; lean_object* v_snd_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
v_a_919_ = lean_ctor_get(v___x_917_, 1);
lean_inc(v_a_919_);
lean_dec_ref_known(v___x_917_, 2);
v_fst_920_ = lean_ctor_get(v_a_918_, 0);
lean_inc(v_fst_920_);
v_snd_921_ = lean_ctor_get(v_a_918_, 1);
lean_inc(v_snd_921_);
lean_dec(v_a_918_);
v___x_922_ = lean_unsigned_to_nat(1u);
v___x_923_ = lean_nat_add(v_offset_874_, v___x_922_);
lean_dec(v_offset_874_);
lean_inc_ref(v_body_915_);
v___x_924_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_867_, v___x_868_, v___x_869_, v_start_870_, v_xs_871_, v___x_872_, v_body_915_, v___x_923_, v_snd_921_, v_a_876_, v_a_877_, v_a_919_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_950_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_a_926_ = lean_ctor_get(v___x_924_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_950_ == 0)
{
v___x_928_ = v___x_924_;
v_isShared_929_ = v_isSharedCheck_950_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_950_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v_fst_930_; lean_object* v_snd_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_949_; 
v_fst_930_ = lean_ctor_get(v_a_925_, 0);
v_snd_931_ = lean_ctor_get(v_a_925_, 1);
v_isSharedCheck_949_ = !lean_is_exclusive(v_a_925_);
if (v_isSharedCheck_949_ == 0)
{
v___x_933_ = v_a_925_;
v_isShared_934_ = v_isSharedCheck_949_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_snd_931_);
lean_inc(v_fst_930_);
lean_dec(v_a_925_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_949_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
size_t v___x_935_; size_t v___x_936_; uint8_t v___x_937_; 
v___x_935_ = lean_ptr_addr(v_binderType_914_);
v___x_936_ = lean_ptr_addr(v_fst_920_);
v___x_937_ = lean_usize_dec_eq(v___x_935_, v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; 
lean_inc(v_binderName_913_);
lean_del_object(v___x_933_);
lean_del_object(v___x_928_);
lean_dec_ref_known(v_e_873_, 3);
v___x_938_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_binderName_913_, v_binderInfo_916_, v_fst_920_, v_fst_930_, v_snd_931_, v_a_876_, v_a_877_, v_a_926_);
return v___x_938_;
}
else
{
size_t v___x_939_; size_t v___x_940_; uint8_t v___x_941_; 
v___x_939_ = lean_ptr_addr(v_body_915_);
v___x_940_ = lean_ptr_addr(v_fst_930_);
v___x_941_ = lean_usize_dec_eq(v___x_939_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
lean_inc(v_binderName_913_);
lean_del_object(v___x_933_);
lean_del_object(v___x_928_);
lean_dec_ref_known(v_e_873_, 3);
v___x_942_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_binderName_913_, v_binderInfo_916_, v_fst_920_, v_fst_930_, v_snd_931_, v_a_876_, v_a_877_, v_a_926_);
return v___x_942_;
}
else
{
lean_object* v___x_944_; 
lean_dec(v_fst_930_);
lean_dec(v_fst_920_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v_e_873_);
v___x_944_ = v___x_933_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_e_873_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_snd_931_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_944_);
v___x_946_ = v___x_928_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_a_926_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_920_);
lean_dec_ref_known(v_e_873_, 3);
return v___x_924_;
}
}
else
{
lean_dec_ref_known(v_e_873_, 3);
lean_dec(v_offset_874_);
lean_dec_ref(v___x_868_);
return v___x_917_;
}
}
case 7:
{
lean_object* v_binderName_951_; lean_object* v_binderType_952_; lean_object* v_body_953_; uint8_t v_binderInfo_954_; lean_object* v___x_955_; 
v_binderName_951_ = lean_ctor_get(v_e_873_, 0);
v_binderType_952_ = lean_ctor_get(v_e_873_, 1);
v_body_953_ = lean_ctor_get(v_e_873_, 2);
v_binderInfo_954_ = lean_ctor_get_uint8(v_e_873_, sizeof(void*)*3 + 8);
lean_inc(v_offset_874_);
lean_inc_ref(v_binderType_952_);
lean_inc_ref(v___x_868_);
v___x_955_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_867_, v___x_868_, v___x_869_, v_start_870_, v_xs_871_, v___x_872_, v_binderType_952_, v_offset_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v_a_957_; lean_object* v_fst_958_; lean_object* v_snd_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
v_a_957_ = lean_ctor_get(v___x_955_, 1);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_955_, 2);
v_fst_958_ = lean_ctor_get(v_a_956_, 0);
lean_inc(v_fst_958_);
v_snd_959_ = lean_ctor_get(v_a_956_, 1);
lean_inc(v_snd_959_);
lean_dec(v_a_956_);
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = lean_nat_add(v_offset_874_, v___x_960_);
lean_dec(v_offset_874_);
lean_inc_ref(v_body_953_);
v___x_962_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_867_, v___x_868_, v___x_869_, v_start_870_, v_xs_871_, v___x_872_, v_body_953_, v___x_961_, v_snd_959_, v_a_876_, v_a_877_, v_a_957_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_988_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_a_964_ = lean_ctor_get(v___x_962_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_988_ == 0)
{
v___x_966_ = v___x_962_;
v_isShared_967_ = v_isSharedCheck_988_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_988_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v_fst_968_; lean_object* v_snd_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_987_; 
v_fst_968_ = lean_ctor_get(v_a_963_, 0);
v_snd_969_ = lean_ctor_get(v_a_963_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v_a_963_);
if (v_isSharedCheck_987_ == 0)
{
v___x_971_ = v_a_963_;
v_isShared_972_ = v_isSharedCheck_987_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_snd_969_);
lean_inc(v_fst_968_);
lean_dec(v_a_963_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_987_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
size_t v___x_973_; size_t v___x_974_; uint8_t v___x_975_; 
v___x_973_ = lean_ptr_addr(v_binderType_952_);
v___x_974_ = lean_ptr_addr(v_fst_958_);
v___x_975_ = lean_usize_dec_eq(v___x_973_, v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; 
lean_inc(v_binderName_951_);
lean_del_object(v___x_971_);
lean_del_object(v___x_966_);
lean_dec_ref_known(v_e_873_, 3);
v___x_976_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_binderName_951_, v_binderInfo_954_, v_fst_958_, v_fst_968_, v_snd_969_, v_a_876_, v_a_877_, v_a_964_);
return v___x_976_;
}
else
{
size_t v___x_977_; size_t v___x_978_; uint8_t v___x_979_; 
v___x_977_ = lean_ptr_addr(v_body_953_);
v___x_978_ = lean_ptr_addr(v_fst_968_);
v___x_979_ = lean_usize_dec_eq(v___x_977_, v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; 
lean_inc(v_binderName_951_);
lean_del_object(v___x_971_);
lean_del_object(v___x_966_);
lean_dec_ref_known(v_e_873_, 3);
v___x_980_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_binderName_951_, v_binderInfo_954_, v_fst_958_, v_fst_968_, v_snd_969_, v_a_876_, v_a_877_, v_a_964_);
return v___x_980_;
}
else
{
lean_object* v___x_982_; 
lean_dec(v_fst_968_);
lean_dec(v_fst_958_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v_e_873_);
v___x_982_ = v___x_971_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_e_873_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_snd_969_);
v___x_982_ = v_reuseFailAlloc_986_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_984_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_982_);
v___x_984_ = v___x_966_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_a_964_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_958_);
lean_dec_ref_known(v_e_873_, 3);
return v___x_962_;
}
}
else
{
lean_dec_ref_known(v_e_873_, 3);
lean_dec(v_offset_874_);
lean_dec_ref(v___x_868_);
return v___x_955_;
}
}
case 8:
{
lean_object* v_declName_989_; lean_object* v_type_990_; lean_object* v_value_991_; lean_object* v_body_992_; uint8_t v_nondep_993_; lean_object* v___x_994_; 
v_declName_989_ = lean_ctor_get(v_e_873_, 0);
v_type_990_ = lean_ctor_get(v_e_873_, 1);
v_value_991_ = lean_ctor_get(v_e_873_, 2);
v_body_992_ = lean_ctor_get(v_e_873_, 3);
v_nondep_993_ = lean_ctor_get_uint8(v_e_873_, sizeof(void*)*4 + 8);
lean_inc(v_offset_874_);
lean_inc_ref(v_type_990_);
lean_inc_ref(v___x_868_);
v___x_994_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_867_, v___x_868_, v___x_869_, v_start_870_, v_xs_871_, v___x_872_, v_type_990_, v_offset_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v_a_996_; lean_object* v_fst_997_; lean_object* v_snd_998_; lean_object* v___x_999_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
v_a_996_ = lean_ctor_get(v___x_994_, 1);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_994_, 2);
v_fst_997_ = lean_ctor_get(v_a_995_, 0);
lean_inc(v_fst_997_);
v_snd_998_ = lean_ctor_get(v_a_995_, 1);
lean_inc(v_snd_998_);
lean_dec(v_a_995_);
lean_inc(v_offset_874_);
lean_inc_ref(v_value_991_);
lean_inc_ref(v___x_868_);
v___x_999_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_867_, v___x_868_, v___x_869_, v_start_870_, v_xs_871_, v___x_872_, v_value_991_, v_offset_874_, v_snd_998_, v_a_876_, v_a_877_, v_a_996_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v_a_1001_; lean_object* v_fst_1002_; lean_object* v_snd_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
v_a_1001_ = lean_ctor_get(v___x_999_, 1);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_999_, 2);
v_fst_1002_ = lean_ctor_get(v_a_1000_, 0);
lean_inc(v_fst_1002_);
v_snd_1003_ = lean_ctor_get(v_a_1000_, 1);
lean_inc(v_snd_1003_);
lean_dec(v_a_1000_);
v___x_1004_ = lean_unsigned_to_nat(1u);
v___x_1005_ = lean_nat_add(v_offset_874_, v___x_1004_);
lean_dec(v_offset_874_);
lean_inc_ref(v_body_992_);
v___x_1006_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_867_, v___x_868_, v___x_869_, v_start_870_, v_xs_871_, v___x_872_, v_body_992_, v___x_1005_, v_snd_1003_, v_a_876_, v_a_877_, v_a_1001_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1036_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_a_1008_ = lean_ctor_get(v___x_1006_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1010_ = v___x_1006_;
v_isShared_1011_ = v_isSharedCheck_1036_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1036_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v_fst_1012_; lean_object* v_snd_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1035_; 
v_fst_1012_ = lean_ctor_get(v_a_1007_, 0);
v_snd_1013_ = lean_ctor_get(v_a_1007_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_a_1007_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1015_ = v_a_1007_;
v_isShared_1016_ = v_isSharedCheck_1035_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_snd_1013_);
lean_inc(v_fst_1012_);
lean_dec(v_a_1007_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1035_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
size_t v___x_1017_; size_t v___x_1018_; uint8_t v___x_1019_; 
v___x_1017_ = lean_ptr_addr(v_type_990_);
v___x_1018_ = lean_ptr_addr(v_fst_997_);
v___x_1019_ = lean_usize_dec_eq(v___x_1017_, v___x_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
lean_inc(v_declName_989_);
lean_del_object(v___x_1015_);
lean_del_object(v___x_1010_);
lean_dec_ref_known(v_e_873_, 4);
v___x_1020_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_989_, v_fst_997_, v_fst_1002_, v_fst_1012_, v_nondep_993_, v_snd_1013_, v_a_876_, v_a_877_, v_a_1008_);
return v___x_1020_;
}
else
{
size_t v___x_1021_; size_t v___x_1022_; uint8_t v___x_1023_; 
v___x_1021_ = lean_ptr_addr(v_value_991_);
v___x_1022_ = lean_ptr_addr(v_fst_1002_);
v___x_1023_ = lean_usize_dec_eq(v___x_1021_, v___x_1022_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; 
lean_inc(v_declName_989_);
lean_del_object(v___x_1015_);
lean_del_object(v___x_1010_);
lean_dec_ref_known(v_e_873_, 4);
v___x_1024_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_989_, v_fst_997_, v_fst_1002_, v_fst_1012_, v_nondep_993_, v_snd_1013_, v_a_876_, v_a_877_, v_a_1008_);
return v___x_1024_;
}
else
{
size_t v___x_1025_; size_t v___x_1026_; uint8_t v___x_1027_; 
v___x_1025_ = lean_ptr_addr(v_body_992_);
v___x_1026_ = lean_ptr_addr(v_fst_1012_);
v___x_1027_ = lean_usize_dec_eq(v___x_1025_, v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; 
lean_inc(v_declName_989_);
lean_del_object(v___x_1015_);
lean_del_object(v___x_1010_);
lean_dec_ref_known(v_e_873_, 4);
v___x_1028_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_989_, v_fst_997_, v_fst_1002_, v_fst_1012_, v_nondep_993_, v_snd_1013_, v_a_876_, v_a_877_, v_a_1008_);
return v___x_1028_;
}
else
{
lean_object* v___x_1030_; 
lean_dec(v_fst_1012_);
lean_dec(v_fst_1002_);
lean_dec(v_fst_997_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v_e_873_);
v___x_1030_ = v___x_1015_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_e_873_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_snd_1013_);
v___x_1030_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1030_);
v___x_1032_ = v___x_1010_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_a_1008_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
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
lean_dec(v_fst_1002_);
lean_dec(v_fst_997_);
lean_dec_ref_known(v_e_873_, 4);
return v___x_1006_;
}
}
else
{
lean_dec(v_fst_997_);
lean_dec_ref_known(v_e_873_, 4);
lean_dec(v_offset_874_);
lean_dec_ref(v___x_868_);
return v___x_999_;
}
}
else
{
lean_dec_ref_known(v_e_873_, 4);
lean_dec(v_offset_874_);
lean_dec_ref(v___x_868_);
return v___x_994_;
}
}
case 10:
{
lean_object* v_data_1037_; lean_object* v_expr_1038_; lean_object* v___x_1039_; 
v_data_1037_ = lean_ctor_get(v_e_873_, 0);
v_expr_1038_ = lean_ctor_get(v_e_873_, 1);
lean_inc_ref(v_expr_1038_);
v___x_1039_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_867_, v___x_868_, v___x_869_, v_start_870_, v_xs_871_, v___x_872_, v_expr_1038_, v_offset_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1061_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_a_1041_ = lean_ctor_get(v___x_1039_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1043_ = v___x_1039_;
v_isShared_1044_ = v_isSharedCheck_1061_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1061_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v_fst_1045_; lean_object* v_snd_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1060_; 
v_fst_1045_ = lean_ctor_get(v_a_1040_, 0);
v_snd_1046_ = lean_ctor_get(v_a_1040_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_a_1040_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1048_ = v_a_1040_;
v_isShared_1049_ = v_isSharedCheck_1060_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_snd_1046_);
lean_inc(v_fst_1045_);
lean_dec(v_a_1040_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1060_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
size_t v___x_1050_; size_t v___x_1051_; uint8_t v___x_1052_; 
v___x_1050_ = lean_ptr_addr(v_expr_1038_);
v___x_1051_ = lean_ptr_addr(v_fst_1045_);
v___x_1052_ = lean_usize_dec_eq(v___x_1050_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
lean_inc(v_data_1037_);
lean_del_object(v___x_1048_);
lean_del_object(v___x_1043_);
lean_dec_ref_known(v_e_873_, 2);
v___x_1053_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(v_data_1037_, v_fst_1045_, v_snd_1046_, v_a_876_, v_a_877_, v_a_1041_);
return v___x_1053_;
}
else
{
lean_object* v___x_1055_; 
lean_dec(v_fst_1045_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v_e_873_);
v___x_1055_ = v___x_1048_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_e_873_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_snd_1046_);
v___x_1055_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1057_; 
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1055_);
v___x_1057_ = v___x_1043_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_a_1041_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_873_, 2);
return v___x_1039_;
}
}
case 11:
{
lean_object* v_typeName_1062_; lean_object* v_idx_1063_; lean_object* v_struct_1064_; lean_object* v___x_1065_; 
v_typeName_1062_ = lean_ctor_get(v_e_873_, 0);
v_idx_1063_ = lean_ctor_get(v_e_873_, 1);
v_struct_1064_ = lean_ctor_get(v_e_873_, 2);
lean_inc_ref(v_struct_1064_);
v___x_1065_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_867_, v___x_868_, v___x_869_, v_start_870_, v_xs_871_, v___x_872_, v_struct_1064_, v_offset_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1087_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
v_a_1067_ = lean_ctor_get(v___x_1065_, 1);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1069_ = v___x_1065_;
v_isShared_1070_ = v_isSharedCheck_1087_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_inc(v_a_1066_);
lean_dec(v___x_1065_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1087_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v_fst_1071_; lean_object* v_snd_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1086_; 
v_fst_1071_ = lean_ctor_get(v_a_1066_, 0);
v_snd_1072_ = lean_ctor_get(v_a_1066_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_a_1066_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1074_ = v_a_1066_;
v_isShared_1075_ = v_isSharedCheck_1086_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_snd_1072_);
lean_inc(v_fst_1071_);
lean_dec(v_a_1066_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1086_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
size_t v___x_1076_; size_t v___x_1077_; uint8_t v___x_1078_; 
v___x_1076_ = lean_ptr_addr(v_struct_1064_);
v___x_1077_ = lean_ptr_addr(v_fst_1071_);
v___x_1078_ = lean_usize_dec_eq(v___x_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
lean_inc(v_idx_1063_);
lean_inc(v_typeName_1062_);
lean_del_object(v___x_1074_);
lean_del_object(v___x_1069_);
lean_dec_ref_known(v_e_873_, 3);
v___x_1079_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(v_typeName_1062_, v_idx_1063_, v_fst_1071_, v_snd_1072_, v_a_876_, v_a_877_, v_a_1067_);
return v___x_1079_;
}
else
{
lean_object* v___x_1081_; 
lean_dec(v_fst_1071_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v_e_873_);
v___x_1081_ = v___x_1074_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_e_873_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_snd_1072_);
v___x_1081_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1083_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1081_);
v___x_1083_ = v___x_1069_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_a_1067_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_873_, 3);
return v___x_1065_;
}
}
default: 
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec(v_offset_874_);
lean_dec_ref(v_e_873_);
lean_dec_ref(v___x_868_);
v___x_1088_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3);
v___x_1089_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(v___x_1088_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
return v___x_1089_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_minIndex_867_ = stack[0].m_obj;
lean_object* v___x_868_ = stack[1].m_obj;
lean_object* v___x_869_ = stack[2].m_obj;
lean_object* v_start_870_ = stack[3].m_obj;
lean_object* v_xs_871_ = stack[4].m_obj;
lean_object* v___x_872_ = stack[5].m_obj;
lean_object* v_e_873_ = stack[6].m_obj;
lean_object* v_offset_874_ = stack[7].m_obj;
lean_object* v_a_875_ = stack[8].m_obj;
uint8_t v_a_876_ = stack[9].m_num;
lean_object* v_a_877_ = stack[10].m_obj;
lean_object* v_a_878_ = stack[11].m_obj;
lean_object* v_res_1090_;
v_res_1090_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v_minIndex_867_, v___x_868_, v___x_869_, v_start_870_, v_xs_871_, v___x_872_, v_e_873_, v_offset_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
stack->m_obj
 = v_res_1090_;
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(lean_object* v_minIndex_1091_, lean_object* v___x_1092_, lean_object* v___x_1093_, lean_object* v_start_1094_, lean_object* v_xs_1095_, lean_object* v___x_1096_, lean_object* v_e_1097_, lean_object* v_offset_1098_, lean_object* v_a_1099_, uint8_t v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_key_1103_; lean_object* v_a_1105_; lean_object* v___y_1119_; lean_object* v___y_1124_; lean_object* v___x_1129_; 
lean_inc(v_offset_1098_);
lean_inc_ref(v_e_1097_);
v_key_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1103_, 0, v_e_1097_);
lean_ctor_set(v_key_1103_, 1, v_offset_1098_);
v___x_1129_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_a_1099_, v_key_1103_);
if (lean_obj_tag(v___x_1129_) == 1)
{
lean_object* v_val_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec_ref_known(v_key_1103_, 2);
lean_dec(v_offset_1098_);
lean_dec_ref(v_e_1097_);
lean_dec_ref(v___x_1092_);
v_val_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_val_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v_val_1130_);
lean_ctor_set(v___x_1131_, 1, v_a_1099_);
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v_a_1102_);
return v___x_1132_;
}
else
{
lean_dec(v___x_1129_);
switch(lean_obj_tag(v_e_1097_))
{
case 1:
{
lean_object* v_fvarId_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec_ref(v___x_1092_);
v_fvarId_1133_ = lean_ctor_get(v_e_1097_, 0);
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = lean_unsigned_to_nat(1u);
v___x_1136_ = lean_nat_sub(v___x_1093_, v___x_1135_);
v___x_1137_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_1094_, v_xs_1095_, v_fvarId_1133_, v___x_1134_, v___x_1136_);
if (lean_obj_tag(v___x_1137_) == 1)
{
lean_object* v_val_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec_ref_known(v_e_1097_, 1);
v_val_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_val_1138_);
lean_dec_ref_known(v___x_1137_, 1);
v___x_1139_ = lean_nat_add(v_offset_1098_, v_val_1138_);
lean_dec(v_val_1138_);
lean_dec(v_offset_1098_);
v___x_1140_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v___x_1139_, v_a_1102_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v_a_1142_; lean_object* v___x_1143_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
v_a_1142_ = lean_ctor_get(v___x_1140_, 1);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1140_, 2);
v___x_1143_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1103_, v_a_1141_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1142_);
return v___x_1143_;
}
else
{
lean_object* v_a_1144_; lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec_ref_known(v_key_1103_, 2);
lean_dec_ref(v_a_1099_);
v_a_1144_ = lean_ctor_get(v___x_1140_, 0);
v_a_1145_ = lean_ctor_get(v___x_1140_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1140_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_inc(v_a_1144_);
lean_dec(v___x_1140_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1144_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
else
{
lean_object* v___x_1153_; 
lean_dec(v___x_1137_);
lean_dec(v_offset_1098_);
v___x_1153_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1103_, v_e_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
return v___x_1153_;
}
}
case 9:
{
lean_object* v___x_1154_; 
lean_dec(v_offset_1098_);
lean_dec_ref(v___x_1092_);
v___x_1154_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1103_, v_e_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
return v___x_1154_;
}
case 2:
{
lean_object* v___x_1155_; 
lean_dec(v_offset_1098_);
lean_dec_ref(v___x_1092_);
v___x_1155_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1103_, v_e_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
return v___x_1155_;
}
case 0:
{
lean_object* v___x_1156_; 
lean_dec(v_offset_1098_);
lean_dec_ref(v___x_1092_);
v___x_1156_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1103_, v_e_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
return v___x_1156_;
}
case 4:
{
lean_object* v___x_1157_; 
lean_dec(v_offset_1098_);
lean_dec_ref(v___x_1092_);
v___x_1157_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1103_, v_e_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
return v___x_1157_;
}
case 3:
{
lean_object* v___x_1158_; 
lean_dec(v_offset_1098_);
lean_dec_ref(v___x_1092_);
v___x_1158_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1103_, v_e_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
return v___x_1158_;
}
default: 
{
uint8_t v___x_1159_; 
v___x_1159_ = l_Lean_Expr_hasFVar(v_e_1097_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
lean_dec(v_offset_1098_);
lean_dec_ref(v___x_1092_);
v___x_1160_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1103_, v_e_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v___x_1096_, v_e_1097_);
if (lean_obj_tag(v___x_1161_) == 1)
{
lean_object* v_val_1162_; 
v_val_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_val_1162_);
lean_dec_ref_known(v___x_1161_, 1);
if (lean_obj_tag(v_val_1162_) == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1164_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v___x_1163_);
v___y_1124_ = v___x_1164_;
goto v___jp_1123_;
}
else
{
lean_object* v_val_1165_; 
v_val_1165_ = lean_ctor_get(v_val_1162_, 0);
lean_inc(v_val_1165_);
lean_dec_ref_known(v_val_1162_, 1);
v___y_1124_ = v_val_1165_;
goto v___jp_1123_;
}
}
else
{
lean_dec(v___x_1161_);
v_a_1105_ = v_a_1102_;
goto v___jp_1104_;
}
}
}
}
}
v___jp_1104_:
{
switch(lean_obj_tag(v_e_1097_))
{
case 9:
{
lean_object* v___x_1106_; 
lean_dec(v_offset_1098_);
lean_dec_ref(v___x_1092_);
v___x_1106_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1103_, v_e_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1105_);
return v___x_1106_;
}
case 2:
{
lean_object* v___x_1107_; 
lean_dec(v_offset_1098_);
lean_dec_ref(v___x_1092_);
v___x_1107_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1103_, v_e_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1105_);
return v___x_1107_;
}
case 0:
{
lean_object* v___x_1108_; 
lean_dec(v_offset_1098_);
lean_dec_ref(v___x_1092_);
v___x_1108_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1103_, v_e_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1105_);
return v___x_1108_;
}
case 1:
{
lean_object* v___x_1109_; 
lean_dec(v_offset_1098_);
lean_dec_ref(v___x_1092_);
v___x_1109_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1103_, v_e_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1105_);
return v___x_1109_;
}
case 4:
{
lean_object* v___x_1110_; 
lean_dec(v_offset_1098_);
lean_dec_ref(v___x_1092_);
v___x_1110_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1103_, v_e_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1105_);
return v___x_1110_;
}
case 3:
{
lean_object* v___x_1111_; 
lean_dec(v_offset_1098_);
lean_dec_ref(v___x_1092_);
v___x_1111_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1103_, v_e_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1105_);
return v___x_1111_;
}
default: 
{
lean_object* v___x_1112_; 
v___x_1112_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v_minIndex_1091_, v___x_1092_, v___x_1093_, v_start_1094_, v_xs_1095_, v___x_1096_, v_e_1097_, v_offset_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1105_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v_a_1114_; lean_object* v_fst_1115_; lean_object* v_snd_1116_; lean_object* v___x_1117_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
v_a_1114_ = lean_ctor_get(v___x_1112_, 1);
lean_inc(v_a_1114_);
lean_dec_ref_known(v___x_1112_, 2);
v_fst_1115_ = lean_ctor_get(v_a_1113_, 0);
lean_inc(v_fst_1115_);
v_snd_1116_ = lean_ctor_get(v_a_1113_, 1);
lean_inc(v_snd_1116_);
lean_dec(v_a_1113_);
v___x_1117_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1103_, v_fst_1115_, v_snd_1116_, v_a_1100_, v_a_1101_, v_a_1114_);
return v___x_1117_;
}
else
{
lean_dec_ref_known(v_key_1103_, 2);
return v___x_1112_;
}
}
}
}
v___jp_1118_:
{
lean_object* v_maxIndex_1120_; uint8_t v___x_1121_; 
v_maxIndex_1120_ = l_Lean_LocalDecl_index(v___y_1119_);
lean_dec_ref(v___y_1119_);
v___x_1121_ = lean_nat_dec_lt(v_maxIndex_1120_, v_minIndex_1091_);
lean_dec(v_maxIndex_1120_);
if (v___x_1121_ == 0)
{
v_a_1105_ = v_a_1102_;
goto v___jp_1104_;
}
else
{
lean_object* v___x_1122_; 
lean_dec(v_offset_1098_);
lean_dec_ref(v___x_1092_);
v___x_1122_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1103_, v_e_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
return v___x_1122_;
}
}
v___jp_1123_:
{
lean_object* v___x_1125_; 
lean_inc_ref(v___x_1092_);
v___x_1125_ = lean_local_ctx_find(v___x_1092_, v___y_1124_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1127_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1126_);
v___y_1119_ = v___x_1127_;
goto v___jp_1118_;
}
else
{
lean_object* v_val_1128_; 
v_val_1128_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_val_1128_);
lean_dec_ref_known(v___x_1125_, 1);
v___y_1119_ = v_val_1128_;
goto v___jp_1118_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_minIndex_1091_ = stack[0].m_obj;
lean_object* v___x_1092_ = stack[1].m_obj;
lean_object* v___x_1093_ = stack[2].m_obj;
lean_object* v_start_1094_ = stack[3].m_obj;
lean_object* v_xs_1095_ = stack[4].m_obj;
lean_object* v___x_1096_ = stack[5].m_obj;
lean_object* v_e_1097_ = stack[6].m_obj;
lean_object* v_offset_1098_ = stack[7].m_obj;
lean_object* v_a_1099_ = stack[8].m_obj;
uint8_t v_a_1100_ = stack[9].m_num;
lean_object* v_a_1101_ = stack[10].m_obj;
lean_object* v_a_1102_ = stack[11].m_obj;
lean_object* v_res_1166_;
v_res_1166_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_1091_, v___x_1092_, v___x_1093_, v_start_1094_, v_xs_1095_, v___x_1096_, v_e_1097_, v_offset_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
stack->m_obj
 = v_res_1166_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5___boxed(lean_object* v_minIndex_1167_, lean_object* v___x_1168_, lean_object* v___x_1169_, lean_object* v_start_1170_, lean_object* v_xs_1171_, lean_object* v___x_1172_, lean_object* v_e_1173_, lean_object* v_offset_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
uint8_t v_a_boxed_1179_; lean_object* v_res_1180_; 
v_a_boxed_1179_ = lean_unbox(v_a_1176_);
v_res_1180_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_1167_, v___x_1168_, v___x_1169_, v_start_1170_, v_xs_1171_, v___x_1172_, v_e_1173_, v_offset_1174_, v_a_1175_, v_a_boxed_1179_, v_a_1177_, v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec_ref(v___x_1172_);
lean_dec_ref(v_xs_1171_);
lean_dec(v_start_1170_);
lean_dec(v___x_1169_);
lean_dec(v_minIndex_1167_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___boxed(lean_object* v_minIndex_1181_, lean_object* v___x_1182_, lean_object* v___x_1183_, lean_object* v_start_1184_, lean_object* v_xs_1185_, lean_object* v___x_1186_, lean_object* v_e_1187_, lean_object* v_offset_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
uint8_t v_a_boxed_1193_; lean_object* v_res_1194_; 
v_a_boxed_1193_ = lean_unbox(v_a_1190_);
v_res_1194_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v_minIndex_1181_, v___x_1182_, v___x_1183_, v_start_1184_, v_xs_1185_, v___x_1186_, v_e_1187_, v_offset_1188_, v_a_1189_, v_a_boxed_1193_, v_a_1191_, v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec_ref(v___x_1186_);
lean_dec_ref(v_xs_1185_);
lean_dec(v_start_1184_);
lean_dec(v___x_1183_);
lean_dec(v_minIndex_1181_);
return v_res_1194_;
}
}
lean_object* l_Lean_Meta_Sym_abstractFVarsRange___lam__0(lean_object* v_e_1195_, lean_object* v_lctx_1196_, lean_object* v___x_1197_, lean_object* v_start_1198_, lean_object* v_xs_1199_, lean_object* v_maxFVar_1200_, uint8_t v_debug_1201_, uint8_t v___x_1202_, lean_object* v___x_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1253_; lean_object* v___x_1274_; 
lean_inc_ref(v_lctx_1196_);
v___x_1274_ = lean_local_ctx_find(v_lctx_1196_, v___x_1203_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1276_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1275_);
v___y_1253_ = v___x_1276_;
goto v___jp_1252_;
}
else
{
lean_object* v_val_1277_; 
v_val_1277_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_val_1277_);
lean_dec_ref_known(v___x_1274_, 1);
v___y_1253_ = v_val_1277_;
goto v___jp_1252_;
}
v___jp_1206_:
{
switch(lean_obj_tag(v_e_1195_))
{
case 9:
{
lean_object* v___x_1209_; 
lean_dec(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v_lctx_1196_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v_e_1195_);
lean_ctor_set(v___x_1209_, 1, v___y_1205_);
return v___x_1209_;
}
case 2:
{
lean_object* v___x_1210_; 
lean_dec(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v_lctx_1196_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v_e_1195_);
lean_ctor_set(v___x_1210_, 1, v___y_1205_);
return v___x_1210_;
}
case 0:
{
lean_object* v___x_1211_; 
lean_dec(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v_lctx_1196_);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v_e_1195_);
lean_ctor_set(v___x_1211_, 1, v___y_1205_);
return v___x_1211_;
}
case 1:
{
lean_object* v___x_1212_; 
lean_dec(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v_lctx_1196_);
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v_e_1195_);
lean_ctor_set(v___x_1212_, 1, v___y_1205_);
return v___x_1212_;
}
case 4:
{
lean_object* v___x_1213_; 
lean_dec(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v_lctx_1196_);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v_e_1195_);
lean_ctor_set(v___x_1213_, 1, v___y_1205_);
return v___x_1213_;
}
case 3:
{
lean_object* v___x_1214_; 
lean_dec(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v_lctx_1196_);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v_e_1195_);
lean_ctor_set(v___x_1214_, 1, v___y_1205_);
return v___x_1214_;
}
default: 
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2);
lean_inc(v___y_1208_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___y_1208_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v___y_1207_, v_lctx_1196_, v___x_1197_, v_start_1198_, v_xs_1199_, v_maxFVar_1200_, v_e_1195_, v___y_1208_, v___x_1216_, v_debug_1201_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1207_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1227_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
v_a_1219_ = lean_ctor_get(v___x_1217_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1221_ = v___x_1217_;
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_inc(v_a_1218_);
lean_dec(v___x_1217_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_fst_1223_; lean_object* v___x_1225_; 
v_fst_1223_ = lean_ctor_get(v_a_1218_, 0);
lean_inc(v_fst_1223_);
lean_dec(v_a_1218_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v_fst_1223_);
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_fst_1223_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_a_1219_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
v_a_1228_ = lean_ctor_get(v___x_1217_, 0);
v_a_1229_ = lean_ctor_get(v___x_1217_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1217_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_inc(v_a_1228_);
lean_dec(v___x_1217_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1228_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
}
v___jp_1237_:
{
lean_object* v_maxIndex_1241_; uint8_t v___x_1242_; 
v_maxIndex_1241_ = l_Lean_LocalDecl_index(v___y_1240_);
lean_dec_ref(v___y_1240_);
v___x_1242_ = lean_nat_dec_lt(v_maxIndex_1241_, v___y_1238_);
lean_dec(v_maxIndex_1241_);
if (v___x_1242_ == 0)
{
v___y_1207_ = v___y_1238_;
v___y_1208_ = v___y_1239_;
goto v___jp_1206_;
}
else
{
lean_object* v___x_1243_; 
lean_dec(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v_lctx_1196_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_e_1195_);
lean_ctor_set(v___x_1243_, 1, v___y_1205_);
return v___x_1243_;
}
}
v___jp_1244_:
{
lean_object* v___x_1248_; 
lean_inc_ref(v_lctx_1196_);
v___x_1248_ = lean_local_ctx_find(v_lctx_1196_, v___y_1247_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1250_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1249_);
v___y_1238_ = v___y_1245_;
v___y_1239_ = v___y_1246_;
v___y_1240_ = v___x_1250_;
goto v___jp_1237_;
}
else
{
lean_object* v_val_1251_; 
v_val_1251_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_val_1251_);
lean_dec_ref_known(v___x_1248_, 1);
v___y_1238_ = v___y_1245_;
v___y_1239_ = v___y_1246_;
v___y_1240_ = v_val_1251_;
goto v___jp_1237_;
}
}
v___jp_1252_:
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1195_))
{
case 1:
{
lean_object* v_fvarId_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_dec_ref(v___y_1253_);
lean_dec_ref(v_lctx_1196_);
v_fvarId_1255_ = lean_ctor_get(v_e_1195_, 0);
v___x_1256_ = lean_unsigned_to_nat(1u);
v___x_1257_ = lean_nat_sub(v___x_1197_, v___x_1256_);
v___x_1258_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_1198_, v_xs_1199_, v_fvarId_1255_, v___x_1254_, v___x_1257_);
if (lean_obj_tag(v___x_1258_) == 1)
{
lean_object* v_val_1259_; lean_object* v___x_1260_; 
lean_dec_ref_known(v_e_1195_, 1);
v_val_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_val_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v___x_1260_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v_val_1259_, v___y_1205_);
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; 
lean_dec(v___x_1258_);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v_e_1195_);
lean_ctor_set(v___x_1261_, 1, v___y_1205_);
return v___x_1261_;
}
}
case 9:
{
lean_object* v___x_1262_; 
lean_dec_ref(v___y_1253_);
lean_dec_ref(v_lctx_1196_);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v_e_1195_);
lean_ctor_set(v___x_1262_, 1, v___y_1205_);
return v___x_1262_;
}
case 2:
{
lean_object* v___x_1263_; 
lean_dec_ref(v___y_1253_);
lean_dec_ref(v_lctx_1196_);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v_e_1195_);
lean_ctor_set(v___x_1263_, 1, v___y_1205_);
return v___x_1263_;
}
case 0:
{
lean_object* v___x_1264_; 
lean_dec_ref(v___y_1253_);
lean_dec_ref(v_lctx_1196_);
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v_e_1195_);
lean_ctor_set(v___x_1264_, 1, v___y_1205_);
return v___x_1264_;
}
case 4:
{
lean_object* v___x_1265_; 
lean_dec_ref(v___y_1253_);
lean_dec_ref(v_lctx_1196_);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v_e_1195_);
lean_ctor_set(v___x_1265_, 1, v___y_1205_);
return v___x_1265_;
}
case 3:
{
lean_object* v___x_1266_; 
lean_dec_ref(v___y_1253_);
lean_dec_ref(v_lctx_1196_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v_e_1195_);
lean_ctor_set(v___x_1266_, 1, v___y_1205_);
return v___x_1266_;
}
default: 
{
if (v___x_1202_ == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref(v___y_1253_);
lean_dec_ref(v_lctx_1196_);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v_e_1195_);
lean_ctor_set(v___x_1267_, 1, v___y_1205_);
return v___x_1267_;
}
else
{
lean_object* v_minIndex_1268_; lean_object* v___x_1269_; 
v_minIndex_1268_ = l_Lean_LocalDecl_index(v___y_1253_);
lean_dec_ref(v___y_1253_);
v___x_1269_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_maxFVar_1200_, v_e_1195_);
if (lean_obj_tag(v___x_1269_) == 1)
{
lean_object* v_val_1270_; 
v_val_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_val_1270_);
lean_dec_ref_known(v___x_1269_, 1);
if (lean_obj_tag(v_val_1270_) == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1272_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v___x_1271_);
v___y_1245_ = v_minIndex_1268_;
v___y_1246_ = v___x_1254_;
v___y_1247_ = v___x_1272_;
goto v___jp_1244_;
}
else
{
lean_object* v_val_1273_; 
v_val_1273_ = lean_ctor_get(v_val_1270_, 0);
lean_inc(v_val_1273_);
lean_dec_ref_known(v_val_1270_, 1);
v___y_1245_ = v_minIndex_1268_;
v___y_1246_ = v___x_1254_;
v___y_1247_ = v_val_1273_;
goto v___jp_1244_;
}
}
else
{
lean_dec(v___x_1269_);
v___y_1207_ = v_minIndex_1268_;
v___y_1208_ = v___x_1254_;
goto v___jp_1206_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_abstractFVarsRange___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1195_ = stack[0].m_obj;
lean_object* v_lctx_1196_ = stack[1].m_obj;
lean_object* v___x_1197_ = stack[2].m_obj;
lean_object* v_start_1198_ = stack[3].m_obj;
lean_object* v_xs_1199_ = stack[4].m_obj;
lean_object* v_maxFVar_1200_ = stack[5].m_obj;
uint8_t v_debug_1201_ = stack[6].m_num;
uint8_t v___x_1202_ = stack[7].m_num;
lean_object* v___x_1203_ = stack[8].m_obj;
lean_object* v___y_1204_ = stack[9].m_obj;
lean_object* v___y_1205_ = stack[10].m_obj;
lean_object* v_res_1278_;
v_res_1278_ = l_Lean_Meta_Sym_abstractFVarsRange___lam__0(v_e_1195_, v_lctx_1196_, v___x_1197_, v_start_1198_, v_xs_1199_, v_maxFVar_1200_, v_debug_1201_, v___x_1202_, v___x_1203_, v___y_1204_, v___y_1205_);
stack->m_obj
 = v_res_1278_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___lam__0___boxed(lean_object* v_e_1279_, lean_object* v_lctx_1280_, lean_object* v___x_1281_, lean_object* v_start_1282_, lean_object* v_xs_1283_, lean_object* v_maxFVar_1284_, lean_object* v_debug_1285_, lean_object* v___x_1286_, lean_object* v___x_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
uint8_t v_debug_boxed_1290_; uint8_t v___x_27995__boxed_1291_; lean_object* v_res_1292_; 
v_debug_boxed_1290_ = lean_unbox(v_debug_1285_);
v___x_27995__boxed_1291_ = lean_unbox(v___x_1286_);
v_res_1292_ = l_Lean_Meta_Sym_abstractFVarsRange___lam__0(v_e_1279_, v_lctx_1280_, v___x_1281_, v_start_1282_, v_xs_1283_, v_maxFVar_1284_, v_debug_boxed_1290_, v___x_27995__boxed_1291_, v___x_1287_, v___y_1288_, v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec_ref(v_maxFVar_1284_);
lean_dec_ref(v_xs_1283_);
lean_dec(v_start_1282_);
lean_dec(v___x_1281_);
return v_res_1292_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_abstractFVarsRange___closed__2(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1295_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__2));
v___x_1296_ = lean_unsigned_to_nat(16u);
v___x_1297_ = lean_unsigned_to_nat(62u);
v___x_1298_ = ((lean_object*)(l_Lean_Meta_Sym_abstractFVarsRange___closed__1));
v___x_1299_ = ((lean_object*)(l_Lean_Meta_Sym_abstractFVarsRange___closed__0));
v___x_1300_ = l_mkPanicMessageWithDecl(v___x_1299_, v___x_1298_, v___x_1297_, v___x_1296_, v___x_1295_);
return v___x_1300_;
}
}
lean_object* l_Lean_Meta_Sym_abstractFVarsRange(lean_object* v_e_1301_, lean_object* v_start_1302_, lean_object* v_xs_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
uint8_t v___x_1311_; 
v___x_1311_ = l_Lean_Expr_hasFVar(v_e_1301_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; 
lean_dec_ref(v_xs_1303_);
lean_dec(v_start_1302_);
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v_e_1301_);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = lean_array_get_size(v_xs_1303_);
v___x_1314_ = lean_nat_dec_lt(v_start_1302_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; 
lean_dec_ref(v_xs_1303_);
lean_dec(v_start_1302_);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v_e_1301_);
return v___x_1315_;
}
else
{
lean_object* v_lctx_1316_; uint8_t v___x_1317_; lean_object* v___x_1318_; lean_object* v_maxFVar_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v_debug_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___f_1326_; lean_object* v___x_1327_; lean_object* v_env_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v_lctx_1316_ = lean_ctor_get(v_a_1306_, 2);
v___x_1317_ = 0;
v___x_1318_ = lean_st_ref_get(v_a_1305_);
v_maxFVar_1319_ = lean_ctor_get(v___x_1318_, 1);
lean_inc_ref(v_maxFVar_1319_);
lean_dec(v___x_1318_);
v___x_1320_ = lean_array_fget_borrowed(v_xs_1303_, v_start_1302_);
v___x_1321_ = l_Lean_Expr_fvarId_x21(v___x_1320_);
v___x_1322_ = lean_st_ref_get(v_a_1305_);
v_debug_1323_ = lean_ctor_get_uint8(v___x_1322_, sizeof(void*)*12);
lean_dec(v___x_1322_);
v___x_1324_ = lean_box(v_debug_1323_);
v___x_1325_ = lean_box(v___x_1311_);
lean_inc_ref(v_lctx_1316_);
v___f_1326_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_abstractFVarsRange___lam__0___boxed), 11, 9);
lean_closure_set(v___f_1326_, 0, v_e_1301_);
lean_closure_set(v___f_1326_, 1, v_lctx_1316_);
lean_closure_set(v___f_1326_, 2, v___x_1313_);
lean_closure_set(v___f_1326_, 3, v_start_1302_);
lean_closure_set(v___f_1326_, 4, v_xs_1303_);
lean_closure_set(v___f_1326_, 5, v_maxFVar_1319_);
lean_closure_set(v___f_1326_, 6, v___x_1324_);
lean_closure_set(v___f_1326_, 7, v___x_1325_);
lean_closure_set(v___f_1326_, 8, v___x_1321_);
v___x_1327_ = lean_st_ref_get(v_a_1309_);
v_env_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc_ref(v_env_1328_);
lean_dec(v___x_1327_);
v___x_1329_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1329_, 0, v_env_1328_);
lean_ctor_set_uint8(v___x_1329_, sizeof(void*)*1, v___x_1317_);
lean_ctor_set_uint8(v___x_1329_, sizeof(void*)*1 + 1, v___x_1317_);
v___x_1330_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1326_, v___x_1329_, v_a_1305_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1341_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1341_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1341_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
if (lean_obj_tag(v_a_1331_) == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec_ref_known(v_a_1331_, 1);
lean_del_object(v___x_1333_);
v___x_1335_ = lean_obj_once(&l_Lean_Meta_Sym_abstractFVarsRange___closed__2, &l_Lean_Meta_Sym_abstractFVarsRange___closed__2_once, _init_l_Lean_Meta_Sym_abstractFVarsRange___closed__2);
v___x_1336_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v___x_1335_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
return v___x_1336_;
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; 
v_a_1337_ = lean_ctor_get(v_a_1331_, 0);
lean_inc(v_a_1337_);
lean_dec_ref_known(v_a_1331_, 1);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v_a_1337_);
v___x_1339_ = v___x_1333_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
v_a_1342_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1330_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1330_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_abstractFVarsRange_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1301_ = stack[0].m_obj;
lean_object* v_start_1302_ = stack[1].m_obj;
lean_object* v_xs_1303_ = stack[2].m_obj;
lean_object* v_a_1304_ = stack[3].m_obj;
lean_object* v_a_1305_ = stack[4].m_obj;
lean_object* v_a_1306_ = stack[5].m_obj;
lean_object* v_a_1307_ = stack[6].m_obj;
lean_object* v_a_1308_ = stack[7].m_obj;
lean_object* v_a_1309_ = stack[8].m_obj;
lean_object* v_res_1350_;
v_res_1350_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1301_, v_start_1302_, v_xs_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
stack->m_obj
 = v_res_1350_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___boxed(lean_object* v_e_1351_, lean_object* v_start_1352_, lean_object* v_xs_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1351_, v_start_1352_, v_xs_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(lean_object* v_00_u03b2_1362_, lean_object* v_x_1363_, lean_object* v_x_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_x_1363_, v_x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___boxed(lean_object* v_00_u03b2_1366_, lean_object* v_x_1367_, lean_object* v_x_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(v_00_u03b2_1366_, v_x_1367_, v_x_1368_);
lean_dec_ref(v_x_1368_);
lean_dec_ref(v_x_1367_);
return v_res_1369_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2(lean_object* v_00_u03b2_1370_, lean_object* v_x_1371_, size_t v_x_1372_, lean_object* v_x_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_1371_, v_x_1372_, v_x_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1371_ = stack[1].m_obj;
size_t v_x_1372_ = stack[2].m_num;
lean_object* v_x_1373_ = stack[3].m_obj;
lean_object* v_res_1375_;
v_res_1375_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2(lean_box(0), v_x_1371_, v_x_1372_, v_x_1373_);
stack->m_obj
 = v_res_1375_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1376_, lean_object* v_x_1377_, lean_object* v_x_1378_, lean_object* v_x_1379_){
_start:
{
size_t v_x_28414__boxed_1380_; lean_object* v_res_1381_; 
v_x_28414__boxed_1380_ = lean_unbox_usize(v_x_1378_);
lean_dec(v_x_1378_);
v_res_1381_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2(v_00_u03b2_1376_, v_x_1377_, v_x_28414__boxed_1380_, v_x_1379_);
lean_dec_ref(v_x_1379_);
lean_dec_ref(v_x_1377_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_1382_, lean_object* v_keys_1383_, lean_object* v_vals_1384_, lean_object* v_heq_1385_, lean_object* v_i_1386_, lean_object* v_k_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_keys_1383_, v_vals_1384_, v_i_1386_, v_k_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1389_, lean_object* v_keys_1390_, lean_object* v_vals_1391_, lean_object* v_heq_1392_, lean_object* v_i_1393_, lean_object* v_k_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5(v_00_u03b2_1389_, v_keys_1390_, v_vals_1391_, v_heq_1392_, v_i_1393_, v_k_1394_);
lean_dec_ref(v_k_1394_);
lean_dec_ref(v_vals_1391_);
lean_dec_ref(v_keys_1390_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_1396_, lean_object* v_m_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_m_1397_, v_a_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1400_, lean_object* v_m_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8(v_00_u03b2_1400_, v_m_1401_, v_a_1402_);
lean_dec_ref(v_a_1402_);
lean_dec_ref(v_m_1401_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16(lean_object* v_00_u03b2_1404_, lean_object* v_a_1405_, lean_object* v_x_1406_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_a_1405_, v_x_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___boxed(lean_object* v_00_u03b2_1408_, lean_object* v_a_1409_, lean_object* v_x_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16(v_00_u03b2_1408_, v_a_1409_, v_x_1410_);
lean_dec(v_x_1410_);
lean_dec_ref(v_a_1409_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___redArg(lean_object* v_xs_1412_, lean_object* v_fvarId_1413_, lean_object* v_bidx_1414_, lean_object* v_i_1415_){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1416_ = lean_array_fget_borrowed(v_xs_1412_, v_i_1415_);
v___x_1417_ = l_Lean_Expr_fvarId_x21(v___x_1416_);
v___x_1418_ = l_Lean_instBEqFVarId_beq(v___x_1417_, v_fvarId_1413_);
lean_dec(v___x_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1419_ = lean_unsigned_to_nat(0u);
v___x_1420_ = lean_nat_dec_lt(v___x_1419_, v_i_1415_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; 
lean_dec(v_i_1415_);
lean_dec(v_bidx_1414_);
v___x_1421_ = lean_box(0);
return v___x_1421_;
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = lean_unsigned_to_nat(1u);
v___x_1423_ = lean_nat_add(v_bidx_1414_, v___x_1422_);
lean_dec(v_bidx_1414_);
v___x_1424_ = lean_nat_sub(v_i_1415_, v___x_1422_);
lean_dec(v_i_1415_);
v_bidx_1414_ = v___x_1423_;
v_i_1415_ = v___x_1424_;
goto _start;
}
}
else
{
lean_object* v___x_1426_; 
lean_dec(v_i_1415_);
v___x_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1426_, 0, v_bidx_1414_);
return v___x_1426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___redArg___boxed(lean_object* v_xs_1427_, lean_object* v_fvarId_1428_, lean_object* v_bidx_1429_, lean_object* v_i_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___redArg(v_xs_1427_, v_fvarId_1428_, v_bidx_1429_, v_i_1430_);
lean_dec(v_fvarId_1428_);
lean_dec_ref(v_xs_1427_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go(lean_object* v_n_1432_, lean_object* v_xs_1433_, lean_object* v_this_1434_, lean_object* v_fvarId_1435_, lean_object* v_bidx_1436_, lean_object* v_i_1437_, lean_object* v_h_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___redArg(v_xs_1433_, v_fvarId_1435_, v_bidx_1436_, v_i_1437_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___boxed(lean_object* v_n_1440_, lean_object* v_xs_1441_, lean_object* v_this_1442_, lean_object* v_fvarId_1443_, lean_object* v_bidx_1444_, lean_object* v_i_1445_, lean_object* v_h_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go(v_n_1440_, v_xs_1441_, v_this_1442_, v_fvarId_1443_, v_bidx_1444_, v_i_1445_, v_h_1446_);
lean_dec(v_fvarId_1443_);
lean_dec_ref(v_xs_1441_);
lean_dec(v_n_1440_);
return v_res_1447_;
}
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0(lean_object* v_minIndex_1448_, lean_object* v___x_1449_, lean_object* v___y_1450_, lean_object* v_n_1451_, lean_object* v_xs_1452_, lean_object* v___x_1453_, lean_object* v_e_1454_, lean_object* v_offset_1455_, lean_object* v_a_1456_, uint8_t v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
switch(lean_obj_tag(v_e_1454_))
{
case 5:
{
lean_object* v_fn_1460_; lean_object* v_arg_1461_; lean_object* v___x_1462_; 
v_fn_1460_ = lean_ctor_get(v_e_1454_, 0);
v_arg_1461_ = lean_ctor_get(v_e_1454_, 1);
lean_inc(v_offset_1455_);
lean_inc_ref(v_fn_1460_);
lean_inc_ref(v___x_1449_);
v___x_1462_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1448_, v___x_1449_, v___y_1450_, v_n_1451_, v_xs_1452_, v___x_1453_, v_fn_1460_, v_offset_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v_a_1464_; lean_object* v_fst_1465_; lean_object* v_snd_1466_; lean_object* v___x_1467_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
v_a_1464_ = lean_ctor_get(v___x_1462_, 1);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1462_, 2);
v_fst_1465_ = lean_ctor_get(v_a_1463_, 0);
lean_inc(v_fst_1465_);
v_snd_1466_ = lean_ctor_get(v_a_1463_, 1);
lean_inc(v_snd_1466_);
lean_dec(v_a_1463_);
lean_inc_ref(v_arg_1461_);
v___x_1467_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1448_, v___x_1449_, v___y_1450_, v_n_1451_, v_xs_1452_, v___x_1453_, v_arg_1461_, v_offset_1455_, v_snd_1466_, v_a_1457_, v_a_1458_, v_a_1464_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1493_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
v_a_1469_ = lean_ctor_get(v___x_1467_, 1);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1471_ = v___x_1467_;
v_isShared_1472_ = v_isSharedCheck_1493_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_inc(v_a_1468_);
lean_dec(v___x_1467_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1493_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v_fst_1473_; lean_object* v_snd_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1492_; 
v_fst_1473_ = lean_ctor_get(v_a_1468_, 0);
v_snd_1474_ = lean_ctor_get(v_a_1468_, 1);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_a_1468_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1476_ = v_a_1468_;
v_isShared_1477_ = v_isSharedCheck_1492_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_snd_1474_);
lean_inc(v_fst_1473_);
lean_dec(v_a_1468_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1492_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
size_t v___x_1478_; size_t v___x_1479_; uint8_t v___x_1480_; 
v___x_1478_ = lean_ptr_addr(v_fn_1460_);
v___x_1479_ = lean_ptr_addr(v_fst_1465_);
v___x_1480_ = lean_usize_dec_eq(v___x_1478_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; 
lean_del_object(v___x_1476_);
lean_del_object(v___x_1471_);
lean_dec_ref_known(v_e_1454_, 2);
v___x_1481_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_fst_1465_, v_fst_1473_, v_snd_1474_, v_a_1457_, v_a_1458_, v_a_1469_);
return v___x_1481_;
}
else
{
size_t v___x_1482_; size_t v___x_1483_; uint8_t v___x_1484_; 
v___x_1482_ = lean_ptr_addr(v_arg_1461_);
v___x_1483_ = lean_ptr_addr(v_fst_1473_);
v___x_1484_ = lean_usize_dec_eq(v___x_1482_, v___x_1483_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; 
lean_del_object(v___x_1476_);
lean_del_object(v___x_1471_);
lean_dec_ref_known(v_e_1454_, 2);
v___x_1485_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_fst_1465_, v_fst_1473_, v_snd_1474_, v_a_1457_, v_a_1458_, v_a_1469_);
return v___x_1485_;
}
else
{
lean_object* v___x_1487_; 
lean_dec(v_fst_1473_);
lean_dec(v_fst_1465_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v_e_1454_);
v___x_1487_ = v___x_1476_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_e_1454_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_snd_1474_);
v___x_1487_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1487_);
v___x_1489_ = v___x_1471_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_a_1469_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1465_);
lean_dec_ref_known(v_e_1454_, 2);
return v___x_1467_;
}
}
else
{
lean_dec_ref_known(v_e_1454_, 2);
lean_dec(v_offset_1455_);
lean_dec_ref(v___x_1449_);
return v___x_1462_;
}
}
case 6:
{
lean_object* v_binderName_1494_; lean_object* v_binderType_1495_; lean_object* v_body_1496_; uint8_t v_binderInfo_1497_; lean_object* v___x_1498_; 
v_binderName_1494_ = lean_ctor_get(v_e_1454_, 0);
v_binderType_1495_ = lean_ctor_get(v_e_1454_, 1);
v_body_1496_ = lean_ctor_get(v_e_1454_, 2);
v_binderInfo_1497_ = lean_ctor_get_uint8(v_e_1454_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1455_);
lean_inc_ref(v_binderType_1495_);
lean_inc_ref(v___x_1449_);
v___x_1498_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1448_, v___x_1449_, v___y_1450_, v_n_1451_, v_xs_1452_, v___x_1453_, v_binderType_1495_, v_offset_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v_a_1500_; lean_object* v_fst_1501_; lean_object* v_snd_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
v_a_1500_ = lean_ctor_get(v___x_1498_, 1);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1498_, 2);
v_fst_1501_ = lean_ctor_get(v_a_1499_, 0);
lean_inc(v_fst_1501_);
v_snd_1502_ = lean_ctor_get(v_a_1499_, 1);
lean_inc(v_snd_1502_);
lean_dec(v_a_1499_);
v___x_1503_ = lean_unsigned_to_nat(1u);
v___x_1504_ = lean_nat_add(v_offset_1455_, v___x_1503_);
lean_dec(v_offset_1455_);
lean_inc_ref(v_body_1496_);
v___x_1505_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1448_, v___x_1449_, v___y_1450_, v_n_1451_, v_xs_1452_, v___x_1453_, v_body_1496_, v___x_1504_, v_snd_1502_, v_a_1457_, v_a_1458_, v_a_1500_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1531_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_a_1507_ = lean_ctor_get(v___x_1505_, 1);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1509_ = v___x_1505_;
v_isShared_1510_ = v_isSharedCheck_1531_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1531_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v_fst_1511_; lean_object* v_snd_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1530_; 
v_fst_1511_ = lean_ctor_get(v_a_1506_, 0);
v_snd_1512_ = lean_ctor_get(v_a_1506_, 1);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_a_1506_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1514_ = v_a_1506_;
v_isShared_1515_ = v_isSharedCheck_1530_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_snd_1512_);
lean_inc(v_fst_1511_);
lean_dec(v_a_1506_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1530_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
size_t v___x_1516_; size_t v___x_1517_; uint8_t v___x_1518_; 
v___x_1516_ = lean_ptr_addr(v_binderType_1495_);
v___x_1517_ = lean_ptr_addr(v_fst_1501_);
v___x_1518_ = lean_usize_dec_eq(v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; 
lean_inc(v_binderName_1494_);
lean_del_object(v___x_1514_);
lean_del_object(v___x_1509_);
lean_dec_ref_known(v_e_1454_, 3);
v___x_1519_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_binderName_1494_, v_binderInfo_1497_, v_fst_1501_, v_fst_1511_, v_snd_1512_, v_a_1457_, v_a_1458_, v_a_1507_);
return v___x_1519_;
}
else
{
size_t v___x_1520_; size_t v___x_1521_; uint8_t v___x_1522_; 
v___x_1520_ = lean_ptr_addr(v_body_1496_);
v___x_1521_ = lean_ptr_addr(v_fst_1511_);
v___x_1522_ = lean_usize_dec_eq(v___x_1520_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; 
lean_inc(v_binderName_1494_);
lean_del_object(v___x_1514_);
lean_del_object(v___x_1509_);
lean_dec_ref_known(v_e_1454_, 3);
v___x_1523_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_binderName_1494_, v_binderInfo_1497_, v_fst_1501_, v_fst_1511_, v_snd_1512_, v_a_1457_, v_a_1458_, v_a_1507_);
return v___x_1523_;
}
else
{
lean_object* v___x_1525_; 
lean_dec(v_fst_1511_);
lean_dec(v_fst_1501_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v_e_1454_);
v___x_1525_ = v___x_1514_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_e_1454_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_snd_1512_);
v___x_1525_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1527_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1525_);
v___x_1527_ = v___x_1509_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_a_1507_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1501_);
lean_dec_ref_known(v_e_1454_, 3);
return v___x_1505_;
}
}
else
{
lean_dec_ref_known(v_e_1454_, 3);
lean_dec(v_offset_1455_);
lean_dec_ref(v___x_1449_);
return v___x_1498_;
}
}
case 7:
{
lean_object* v_binderName_1532_; lean_object* v_binderType_1533_; lean_object* v_body_1534_; uint8_t v_binderInfo_1535_; lean_object* v___x_1536_; 
v_binderName_1532_ = lean_ctor_get(v_e_1454_, 0);
v_binderType_1533_ = lean_ctor_get(v_e_1454_, 1);
v_body_1534_ = lean_ctor_get(v_e_1454_, 2);
v_binderInfo_1535_ = lean_ctor_get_uint8(v_e_1454_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1455_);
lean_inc_ref(v_binderType_1533_);
lean_inc_ref(v___x_1449_);
v___x_1536_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1448_, v___x_1449_, v___y_1450_, v_n_1451_, v_xs_1452_, v___x_1453_, v_binderType_1533_, v_offset_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v_a_1538_; lean_object* v_fst_1539_; lean_object* v_snd_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
v_a_1538_ = lean_ctor_get(v___x_1536_, 1);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1536_, 2);
v_fst_1539_ = lean_ctor_get(v_a_1537_, 0);
lean_inc(v_fst_1539_);
v_snd_1540_ = lean_ctor_get(v_a_1537_, 1);
lean_inc(v_snd_1540_);
lean_dec(v_a_1537_);
v___x_1541_ = lean_unsigned_to_nat(1u);
v___x_1542_ = lean_nat_add(v_offset_1455_, v___x_1541_);
lean_dec(v_offset_1455_);
lean_inc_ref(v_body_1534_);
v___x_1543_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1448_, v___x_1449_, v___y_1450_, v_n_1451_, v_xs_1452_, v___x_1453_, v_body_1534_, v___x_1542_, v_snd_1540_, v_a_1457_, v_a_1458_, v_a_1538_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1569_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_a_1545_ = lean_ctor_get(v___x_1543_, 1);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1547_ = v___x_1543_;
v_isShared_1548_ = v_isSharedCheck_1569_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1569_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v_fst_1549_; lean_object* v_snd_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1568_; 
v_fst_1549_ = lean_ctor_get(v_a_1544_, 0);
v_snd_1550_ = lean_ctor_get(v_a_1544_, 1);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_a_1544_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1552_ = v_a_1544_;
v_isShared_1553_ = v_isSharedCheck_1568_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_snd_1550_);
lean_inc(v_fst_1549_);
lean_dec(v_a_1544_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1568_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
size_t v___x_1554_; size_t v___x_1555_; uint8_t v___x_1556_; 
v___x_1554_ = lean_ptr_addr(v_binderType_1533_);
v___x_1555_ = lean_ptr_addr(v_fst_1539_);
v___x_1556_ = lean_usize_dec_eq(v___x_1554_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; 
lean_inc(v_binderName_1532_);
lean_del_object(v___x_1552_);
lean_del_object(v___x_1547_);
lean_dec_ref_known(v_e_1454_, 3);
v___x_1557_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_binderName_1532_, v_binderInfo_1535_, v_fst_1539_, v_fst_1549_, v_snd_1550_, v_a_1457_, v_a_1458_, v_a_1545_);
return v___x_1557_;
}
else
{
size_t v___x_1558_; size_t v___x_1559_; uint8_t v___x_1560_; 
v___x_1558_ = lean_ptr_addr(v_body_1534_);
v___x_1559_ = lean_ptr_addr(v_fst_1549_);
v___x_1560_ = lean_usize_dec_eq(v___x_1558_, v___x_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; 
lean_inc(v_binderName_1532_);
lean_del_object(v___x_1552_);
lean_del_object(v___x_1547_);
lean_dec_ref_known(v_e_1454_, 3);
v___x_1561_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_binderName_1532_, v_binderInfo_1535_, v_fst_1539_, v_fst_1549_, v_snd_1550_, v_a_1457_, v_a_1458_, v_a_1545_);
return v___x_1561_;
}
else
{
lean_object* v___x_1563_; 
lean_dec(v_fst_1549_);
lean_dec(v_fst_1539_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v_e_1454_);
v___x_1563_ = v___x_1552_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_e_1454_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_snd_1550_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1565_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1563_);
v___x_1565_ = v___x_1547_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_a_1545_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1539_);
lean_dec_ref_known(v_e_1454_, 3);
return v___x_1543_;
}
}
else
{
lean_dec_ref_known(v_e_1454_, 3);
lean_dec(v_offset_1455_);
lean_dec_ref(v___x_1449_);
return v___x_1536_;
}
}
case 8:
{
lean_object* v_declName_1570_; lean_object* v_type_1571_; lean_object* v_value_1572_; lean_object* v_body_1573_; uint8_t v_nondep_1574_; lean_object* v___x_1575_; 
v_declName_1570_ = lean_ctor_get(v_e_1454_, 0);
v_type_1571_ = lean_ctor_get(v_e_1454_, 1);
v_value_1572_ = lean_ctor_get(v_e_1454_, 2);
v_body_1573_ = lean_ctor_get(v_e_1454_, 3);
v_nondep_1574_ = lean_ctor_get_uint8(v_e_1454_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1455_);
lean_inc_ref(v_type_1571_);
lean_inc_ref(v___x_1449_);
v___x_1575_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1448_, v___x_1449_, v___y_1450_, v_n_1451_, v_xs_1452_, v___x_1453_, v_type_1571_, v_offset_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v_a_1577_; lean_object* v_fst_1578_; lean_object* v_snd_1579_; lean_object* v___x_1580_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
v_a_1577_ = lean_ctor_get(v___x_1575_, 1);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1575_, 2);
v_fst_1578_ = lean_ctor_get(v_a_1576_, 0);
lean_inc(v_fst_1578_);
v_snd_1579_ = lean_ctor_get(v_a_1576_, 1);
lean_inc(v_snd_1579_);
lean_dec(v_a_1576_);
lean_inc(v_offset_1455_);
lean_inc_ref(v_value_1572_);
lean_inc_ref(v___x_1449_);
v___x_1580_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1448_, v___x_1449_, v___y_1450_, v_n_1451_, v_xs_1452_, v___x_1453_, v_value_1572_, v_offset_1455_, v_snd_1579_, v_a_1457_, v_a_1458_, v_a_1577_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v_a_1582_; lean_object* v_fst_1583_; lean_object* v_snd_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
v_a_1582_ = lean_ctor_get(v___x_1580_, 1);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1580_, 2);
v_fst_1583_ = lean_ctor_get(v_a_1581_, 0);
lean_inc(v_fst_1583_);
v_snd_1584_ = lean_ctor_get(v_a_1581_, 1);
lean_inc(v_snd_1584_);
lean_dec(v_a_1581_);
v___x_1585_ = lean_unsigned_to_nat(1u);
v___x_1586_ = lean_nat_add(v_offset_1455_, v___x_1585_);
lean_dec(v_offset_1455_);
lean_inc_ref(v_body_1573_);
v___x_1587_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1448_, v___x_1449_, v___y_1450_, v_n_1451_, v_xs_1452_, v___x_1453_, v_body_1573_, v___x_1586_, v_snd_1584_, v_a_1457_, v_a_1458_, v_a_1582_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1617_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_a_1589_ = lean_ctor_get(v___x_1587_, 1);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1591_ = v___x_1587_;
v_isShared_1592_ = v_isSharedCheck_1617_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1617_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v_fst_1593_; lean_object* v_snd_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1616_; 
v_fst_1593_ = lean_ctor_get(v_a_1588_, 0);
v_snd_1594_ = lean_ctor_get(v_a_1588_, 1);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_a_1588_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1596_ = v_a_1588_;
v_isShared_1597_ = v_isSharedCheck_1616_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_snd_1594_);
lean_inc(v_fst_1593_);
lean_dec(v_a_1588_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1616_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
size_t v___x_1598_; size_t v___x_1599_; uint8_t v___x_1600_; 
v___x_1598_ = lean_ptr_addr(v_type_1571_);
v___x_1599_ = lean_ptr_addr(v_fst_1578_);
v___x_1600_ = lean_usize_dec_eq(v___x_1598_, v___x_1599_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; 
lean_inc(v_declName_1570_);
lean_del_object(v___x_1596_);
lean_del_object(v___x_1591_);
lean_dec_ref_known(v_e_1454_, 4);
v___x_1601_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_1570_, v_fst_1578_, v_fst_1583_, v_fst_1593_, v_nondep_1574_, v_snd_1594_, v_a_1457_, v_a_1458_, v_a_1589_);
return v___x_1601_;
}
else
{
size_t v___x_1602_; size_t v___x_1603_; uint8_t v___x_1604_; 
v___x_1602_ = lean_ptr_addr(v_value_1572_);
v___x_1603_ = lean_ptr_addr(v_fst_1583_);
v___x_1604_ = lean_usize_dec_eq(v___x_1602_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; 
lean_inc(v_declName_1570_);
lean_del_object(v___x_1596_);
lean_del_object(v___x_1591_);
lean_dec_ref_known(v_e_1454_, 4);
v___x_1605_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_1570_, v_fst_1578_, v_fst_1583_, v_fst_1593_, v_nondep_1574_, v_snd_1594_, v_a_1457_, v_a_1458_, v_a_1589_);
return v___x_1605_;
}
else
{
size_t v___x_1606_; size_t v___x_1607_; uint8_t v___x_1608_; 
v___x_1606_ = lean_ptr_addr(v_body_1573_);
v___x_1607_ = lean_ptr_addr(v_fst_1593_);
v___x_1608_ = lean_usize_dec_eq(v___x_1606_, v___x_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; 
lean_inc(v_declName_1570_);
lean_del_object(v___x_1596_);
lean_del_object(v___x_1591_);
lean_dec_ref_known(v_e_1454_, 4);
v___x_1609_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_1570_, v_fst_1578_, v_fst_1583_, v_fst_1593_, v_nondep_1574_, v_snd_1594_, v_a_1457_, v_a_1458_, v_a_1589_);
return v___x_1609_;
}
else
{
lean_object* v___x_1611_; 
lean_dec(v_fst_1593_);
lean_dec(v_fst_1583_);
lean_dec(v_fst_1578_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_e_1454_);
v___x_1611_ = v___x_1596_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_e_1454_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_snd_1594_);
v___x_1611_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1613_; 
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1611_);
v___x_1613_ = v___x_1591_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_a_1589_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
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
lean_dec(v_fst_1583_);
lean_dec(v_fst_1578_);
lean_dec_ref_known(v_e_1454_, 4);
return v___x_1587_;
}
}
else
{
lean_dec(v_fst_1578_);
lean_dec_ref_known(v_e_1454_, 4);
lean_dec(v_offset_1455_);
lean_dec_ref(v___x_1449_);
return v___x_1580_;
}
}
else
{
lean_dec_ref_known(v_e_1454_, 4);
lean_dec(v_offset_1455_);
lean_dec_ref(v___x_1449_);
return v___x_1575_;
}
}
case 10:
{
lean_object* v_data_1618_; lean_object* v_expr_1619_; lean_object* v___x_1620_; 
v_data_1618_ = lean_ctor_get(v_e_1454_, 0);
v_expr_1619_ = lean_ctor_get(v_e_1454_, 1);
lean_inc_ref(v_expr_1619_);
v___x_1620_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1448_, v___x_1449_, v___y_1450_, v_n_1451_, v_xs_1452_, v___x_1453_, v_expr_1619_, v_offset_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1642_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_a_1622_ = lean_ctor_get(v___x_1620_, 1);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1624_ = v___x_1620_;
v_isShared_1625_ = v_isSharedCheck_1642_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1642_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v_fst_1626_; lean_object* v_snd_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1641_; 
v_fst_1626_ = lean_ctor_get(v_a_1621_, 0);
v_snd_1627_ = lean_ctor_get(v_a_1621_, 1);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_a_1621_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1629_ = v_a_1621_;
v_isShared_1630_ = v_isSharedCheck_1641_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_snd_1627_);
lean_inc(v_fst_1626_);
lean_dec(v_a_1621_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1641_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
size_t v___x_1631_; size_t v___x_1632_; uint8_t v___x_1633_; 
v___x_1631_ = lean_ptr_addr(v_expr_1619_);
v___x_1632_ = lean_ptr_addr(v_fst_1626_);
v___x_1633_ = lean_usize_dec_eq(v___x_1631_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; 
lean_inc(v_data_1618_);
lean_del_object(v___x_1629_);
lean_del_object(v___x_1624_);
lean_dec_ref_known(v_e_1454_, 2);
v___x_1634_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(v_data_1618_, v_fst_1626_, v_snd_1627_, v_a_1457_, v_a_1458_, v_a_1622_);
return v___x_1634_;
}
else
{
lean_object* v___x_1636_; 
lean_dec(v_fst_1626_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v_e_1454_);
v___x_1636_ = v___x_1629_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_e_1454_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_snd_1627_);
v___x_1636_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1638_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v___x_1636_);
v___x_1638_ = v___x_1624_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1636_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_a_1622_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1454_, 2);
return v___x_1620_;
}
}
case 11:
{
lean_object* v_typeName_1643_; lean_object* v_idx_1644_; lean_object* v_struct_1645_; lean_object* v___x_1646_; 
v_typeName_1643_ = lean_ctor_get(v_e_1454_, 0);
v_idx_1644_ = lean_ctor_get(v_e_1454_, 1);
v_struct_1645_ = lean_ctor_get(v_e_1454_, 2);
lean_inc_ref(v_struct_1645_);
v___x_1646_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1448_, v___x_1449_, v___y_1450_, v_n_1451_, v_xs_1452_, v___x_1453_, v_struct_1645_, v_offset_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1668_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_a_1648_ = lean_ctor_get(v___x_1646_, 1);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1650_ = v___x_1646_;
v_isShared_1651_ = v_isSharedCheck_1668_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1668_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v_fst_1652_; lean_object* v_snd_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1667_; 
v_fst_1652_ = lean_ctor_get(v_a_1647_, 0);
v_snd_1653_ = lean_ctor_get(v_a_1647_, 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_a_1647_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1655_ = v_a_1647_;
v_isShared_1656_ = v_isSharedCheck_1667_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_snd_1653_);
lean_inc(v_fst_1652_);
lean_dec(v_a_1647_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1667_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
size_t v___x_1657_; size_t v___x_1658_; uint8_t v___x_1659_; 
v___x_1657_ = lean_ptr_addr(v_struct_1645_);
v___x_1658_ = lean_ptr_addr(v_fst_1652_);
v___x_1659_ = lean_usize_dec_eq(v___x_1657_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
lean_inc(v_idx_1644_);
lean_inc(v_typeName_1643_);
lean_del_object(v___x_1655_);
lean_del_object(v___x_1650_);
lean_dec_ref_known(v_e_1454_, 3);
v___x_1660_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(v_typeName_1643_, v_idx_1644_, v_fst_1652_, v_snd_1653_, v_a_1457_, v_a_1458_, v_a_1648_);
return v___x_1660_;
}
else
{
lean_object* v___x_1662_; 
lean_dec(v_fst_1652_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v_e_1454_);
v___x_1662_ = v___x_1655_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_e_1454_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_snd_1653_);
v___x_1662_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1664_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1662_);
v___x_1664_ = v___x_1650_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_a_1648_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1454_, 3);
return v___x_1646_;
}
}
default: 
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec(v_offset_1455_);
lean_dec_ref(v_e_1454_);
lean_dec_ref(v___x_1449_);
v___x_1669_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3);
v___x_1670_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(v___x_1669_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
return v___x_1670_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_minIndex_1448_ = stack[0].m_obj;
lean_object* v___x_1449_ = stack[1].m_obj;
lean_object* v___y_1450_ = stack[2].m_obj;
lean_object* v_n_1451_ = stack[3].m_obj;
lean_object* v_xs_1452_ = stack[4].m_obj;
lean_object* v___x_1453_ = stack[5].m_obj;
lean_object* v_e_1454_ = stack[6].m_obj;
lean_object* v_offset_1455_ = stack[7].m_obj;
lean_object* v_a_1456_ = stack[8].m_obj;
uint8_t v_a_1457_ = stack[9].m_num;
lean_object* v_a_1458_ = stack[10].m_obj;
lean_object* v_a_1459_ = stack[11].m_obj;
lean_object* v_res_1671_;
v_res_1671_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0(v_minIndex_1448_, v___x_1449_, v___y_1450_, v_n_1451_, v_xs_1452_, v___x_1453_, v_e_1454_, v_offset_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
stack->m_obj
 = v_res_1671_;
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(lean_object* v_minIndex_1672_, lean_object* v___x_1673_, lean_object* v___y_1674_, lean_object* v_n_1675_, lean_object* v_xs_1676_, lean_object* v___x_1677_, lean_object* v_e_1678_, lean_object* v_offset_1679_, lean_object* v_a_1680_, uint8_t v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v_key_1684_; lean_object* v_a_1686_; lean_object* v___y_1700_; lean_object* v___y_1705_; lean_object* v___x_1710_; 
lean_inc(v_offset_1679_);
lean_inc_ref(v_e_1678_);
v_key_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1684_, 0, v_e_1678_);
lean_ctor_set(v_key_1684_, 1, v_offset_1679_);
v___x_1710_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_a_1680_, v_key_1684_);
if (lean_obj_tag(v___x_1710_) == 1)
{
lean_object* v_val_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_dec_ref_known(v_key_1684_, 2);
lean_dec(v_offset_1679_);
lean_dec_ref(v_e_1678_);
lean_dec_ref(v___x_1673_);
v_val_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_val_1711_);
lean_dec_ref_known(v___x_1710_, 1);
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v_val_1711_);
lean_ctor_set(v___x_1712_, 1, v_a_1680_);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
lean_ctor_set(v___x_1713_, 1, v_a_1683_);
return v___x_1713_;
}
else
{
lean_dec(v___x_1710_);
switch(lean_obj_tag(v_e_1678_))
{
case 1:
{
lean_object* v_fvarId_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_dec_ref(v___x_1673_);
v_fvarId_1714_ = lean_ctor_get(v_e_1678_, 0);
v___x_1715_ = lean_unsigned_to_nat(0u);
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = lean_nat_sub(v___y_1674_, v___x_1716_);
v___x_1718_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___redArg(v_xs_1676_, v_fvarId_1714_, v___x_1715_, v___x_1717_);
if (lean_obj_tag(v___x_1718_) == 1)
{
lean_object* v_val_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_dec_ref_known(v_e_1678_, 1);
v_val_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_val_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1720_ = lean_nat_add(v_offset_1679_, v_val_1719_);
lean_dec(v_val_1719_);
lean_dec(v_offset_1679_);
v___x_1721_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v___x_1720_, v_a_1683_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v_a_1723_; lean_object* v___x_1724_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
v_a_1723_ = lean_ctor_get(v___x_1721_, 1);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1721_, 2);
v___x_1724_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1684_, v_a_1722_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1723_);
return v___x_1724_;
}
else
{
lean_object* v_a_1725_; lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec_ref_known(v_key_1684_, 2);
lean_dec_ref(v_a_1680_);
v_a_1725_ = lean_ctor_get(v___x_1721_, 0);
v_a_1726_ = lean_ctor_get(v___x_1721_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1721_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_inc(v_a_1725_);
lean_dec(v___x_1721_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1725_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
else
{
lean_object* v___x_1734_; 
lean_dec(v___x_1718_);
lean_dec(v_offset_1679_);
v___x_1734_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1684_, v_e_1678_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
return v___x_1734_;
}
}
case 9:
{
lean_object* v___x_1735_; 
lean_dec(v_offset_1679_);
lean_dec_ref(v___x_1673_);
v___x_1735_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1684_, v_e_1678_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
return v___x_1735_;
}
case 2:
{
lean_object* v___x_1736_; 
lean_dec(v_offset_1679_);
lean_dec_ref(v___x_1673_);
v___x_1736_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1684_, v_e_1678_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
return v___x_1736_;
}
case 0:
{
lean_object* v___x_1737_; 
lean_dec(v_offset_1679_);
lean_dec_ref(v___x_1673_);
v___x_1737_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1684_, v_e_1678_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
return v___x_1737_;
}
case 4:
{
lean_object* v___x_1738_; 
lean_dec(v_offset_1679_);
lean_dec_ref(v___x_1673_);
v___x_1738_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1684_, v_e_1678_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
return v___x_1738_;
}
case 3:
{
lean_object* v___x_1739_; 
lean_dec(v_offset_1679_);
lean_dec_ref(v___x_1673_);
v___x_1739_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1684_, v_e_1678_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
return v___x_1739_;
}
default: 
{
uint8_t v___x_1740_; 
v___x_1740_ = l_Lean_Expr_hasFVar(v_e_1678_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; 
lean_dec(v_offset_1679_);
lean_dec_ref(v___x_1673_);
v___x_1741_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1684_, v_e_1678_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
return v___x_1741_;
}
else
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v___x_1677_, v_e_1678_);
if (lean_obj_tag(v___x_1742_) == 1)
{
lean_object* v_val_1743_; 
v_val_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_val_1743_);
lean_dec_ref_known(v___x_1742_, 1);
if (lean_obj_tag(v_val_1743_) == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1745_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v___x_1744_);
v___y_1705_ = v___x_1745_;
goto v___jp_1704_;
}
else
{
lean_object* v_val_1746_; 
v_val_1746_ = lean_ctor_get(v_val_1743_, 0);
lean_inc(v_val_1746_);
lean_dec_ref_known(v_val_1743_, 1);
v___y_1705_ = v_val_1746_;
goto v___jp_1704_;
}
}
else
{
lean_dec(v___x_1742_);
v_a_1686_ = v_a_1683_;
goto v___jp_1685_;
}
}
}
}
}
v___jp_1685_:
{
switch(lean_obj_tag(v_e_1678_))
{
case 9:
{
lean_object* v___x_1687_; 
lean_dec(v_offset_1679_);
lean_dec_ref(v___x_1673_);
v___x_1687_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1684_, v_e_1678_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1686_);
return v___x_1687_;
}
case 2:
{
lean_object* v___x_1688_; 
lean_dec(v_offset_1679_);
lean_dec_ref(v___x_1673_);
v___x_1688_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1684_, v_e_1678_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1686_);
return v___x_1688_;
}
case 0:
{
lean_object* v___x_1689_; 
lean_dec(v_offset_1679_);
lean_dec_ref(v___x_1673_);
v___x_1689_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1684_, v_e_1678_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1686_);
return v___x_1689_;
}
case 1:
{
lean_object* v___x_1690_; 
lean_dec(v_offset_1679_);
lean_dec_ref(v___x_1673_);
v___x_1690_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1684_, v_e_1678_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1686_);
return v___x_1690_;
}
case 4:
{
lean_object* v___x_1691_; 
lean_dec(v_offset_1679_);
lean_dec_ref(v___x_1673_);
v___x_1691_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1684_, v_e_1678_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1686_);
return v___x_1691_;
}
case 3:
{
lean_object* v___x_1692_; 
lean_dec(v_offset_1679_);
lean_dec_ref(v___x_1673_);
v___x_1692_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1684_, v_e_1678_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1686_);
return v___x_1692_;
}
default: 
{
lean_object* v___x_1693_; 
v___x_1693_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0(v_minIndex_1672_, v___x_1673_, v___y_1674_, v_n_1675_, v_xs_1676_, v___x_1677_, v_e_1678_, v_offset_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1686_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v_a_1695_; lean_object* v_fst_1696_; lean_object* v_snd_1697_; lean_object* v___x_1698_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
v_a_1695_ = lean_ctor_get(v___x_1693_, 1);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1693_, 2);
v_fst_1696_ = lean_ctor_get(v_a_1694_, 0);
lean_inc(v_fst_1696_);
v_snd_1697_ = lean_ctor_get(v_a_1694_, 1);
lean_inc(v_snd_1697_);
lean_dec(v_a_1694_);
v___x_1698_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1684_, v_fst_1696_, v_snd_1697_, v_a_1681_, v_a_1682_, v_a_1695_);
return v___x_1698_;
}
else
{
lean_dec_ref_known(v_key_1684_, 2);
return v___x_1693_;
}
}
}
}
v___jp_1699_:
{
lean_object* v_maxIndex_1701_; uint8_t v___x_1702_; 
v_maxIndex_1701_ = l_Lean_LocalDecl_index(v___y_1700_);
lean_dec_ref(v___y_1700_);
v___x_1702_ = lean_nat_dec_lt(v_maxIndex_1701_, v_minIndex_1672_);
lean_dec(v_maxIndex_1701_);
if (v___x_1702_ == 0)
{
v_a_1686_ = v_a_1683_;
goto v___jp_1685_;
}
else
{
lean_object* v___x_1703_; 
lean_dec(v_offset_1679_);
lean_dec_ref(v___x_1673_);
v___x_1703_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1684_, v_e_1678_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
return v___x_1703_;
}
}
v___jp_1704_:
{
lean_object* v___x_1706_; 
lean_inc_ref(v___x_1673_);
v___x_1706_ = lean_local_ctx_find(v___x_1673_, v___y_1705_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1708_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1707_);
v___y_1700_ = v___x_1708_;
goto v___jp_1699_;
}
else
{
lean_object* v_val_1709_; 
v_val_1709_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_val_1709_);
lean_dec_ref_known(v___x_1706_, 1);
v___y_1700_ = v_val_1709_;
goto v___jp_1699_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_minIndex_1672_ = stack[0].m_obj;
lean_object* v___x_1673_ = stack[1].m_obj;
lean_object* v___y_1674_ = stack[2].m_obj;
lean_object* v_n_1675_ = stack[3].m_obj;
lean_object* v_xs_1676_ = stack[4].m_obj;
lean_object* v___x_1677_ = stack[5].m_obj;
lean_object* v_e_1678_ = stack[6].m_obj;
lean_object* v_offset_1679_ = stack[7].m_obj;
lean_object* v_a_1680_ = stack[8].m_obj;
uint8_t v_a_1681_ = stack[9].m_num;
lean_object* v_a_1682_ = stack[10].m_obj;
lean_object* v_a_1683_ = stack[11].m_obj;
lean_object* v_res_1747_;
v_res_1747_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1672_, v___x_1673_, v___y_1674_, v_n_1675_, v_xs_1676_, v___x_1677_, v_e_1678_, v_offset_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
stack->m_obj
 = v_res_1747_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0___boxed(lean_object* v_minIndex_1748_, lean_object* v___x_1749_, lean_object* v___y_1750_, lean_object* v_n_1751_, lean_object* v_xs_1752_, lean_object* v___x_1753_, lean_object* v_e_1754_, lean_object* v_offset_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
uint8_t v_a_boxed_1760_; lean_object* v_res_1761_; 
v_a_boxed_1760_ = lean_unbox(v_a_1757_);
v_res_1761_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0_spec__0(v_minIndex_1748_, v___x_1749_, v___y_1750_, v_n_1751_, v_xs_1752_, v___x_1753_, v_e_1754_, v_offset_1755_, v_a_1756_, v_a_boxed_1760_, v_a_1758_, v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec_ref(v___x_1753_);
lean_dec_ref(v_xs_1752_);
lean_dec(v_n_1751_);
lean_dec(v___y_1750_);
lean_dec(v_minIndex_1748_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0___boxed(lean_object* v_minIndex_1762_, lean_object* v___x_1763_, lean_object* v___y_1764_, lean_object* v_n_1765_, lean_object* v_xs_1766_, lean_object* v___x_1767_, lean_object* v_e_1768_, lean_object* v_offset_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
uint8_t v_a_boxed_1774_; lean_object* v_res_1775_; 
v_a_boxed_1774_ = lean_unbox(v_a_1771_);
v_res_1775_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0(v_minIndex_1762_, v___x_1763_, v___y_1764_, v_n_1765_, v_xs_1766_, v___x_1767_, v_e_1768_, v_offset_1769_, v_a_1770_, v_a_boxed_1774_, v_a_1772_, v_a_1773_);
lean_dec_ref(v_a_1772_);
lean_dec_ref(v___x_1767_);
lean_dec_ref(v_xs_1766_);
lean_dec(v_n_1765_);
lean_dec(v___y_1764_);
lean_dec(v_minIndex_1762_);
return v_res_1775_;
}
}
lean_object* l_Lean_Meta_Sym_abstractFVarsPrefix___lam__0(lean_object* v_e_1776_, lean_object* v___x_1777_, lean_object* v_lctx_1778_, lean_object* v___y_1779_, lean_object* v_n_1780_, lean_object* v_xs_1781_, lean_object* v_maxFVar_1782_, uint8_t v_debug_1783_, uint8_t v___x_1784_, lean_object* v___x_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v___y_1789_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1832_; lean_object* v___x_1852_; 
lean_inc_ref(v_lctx_1778_);
v___x_1852_ = lean_local_ctx_find(v_lctx_1778_, v___x_1785_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1854_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1853_);
v___y_1832_ = v___x_1854_;
goto v___jp_1831_;
}
else
{
lean_object* v_val_1855_; 
v_val_1855_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_val_1855_);
lean_dec_ref_known(v___x_1852_, 1);
v___y_1832_ = v_val_1855_;
goto v___jp_1831_;
}
v___jp_1788_:
{
switch(lean_obj_tag(v_e_1776_))
{
case 9:
{
lean_object* v___x_1790_; 
lean_dec(v___y_1789_);
lean_dec_ref(v_lctx_1778_);
lean_dec(v___x_1777_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v_e_1776_);
lean_ctor_set(v___x_1790_, 1, v___y_1787_);
return v___x_1790_;
}
case 2:
{
lean_object* v___x_1791_; 
lean_dec(v___y_1789_);
lean_dec_ref(v_lctx_1778_);
lean_dec(v___x_1777_);
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v_e_1776_);
lean_ctor_set(v___x_1791_, 1, v___y_1787_);
return v___x_1791_;
}
case 0:
{
lean_object* v___x_1792_; 
lean_dec(v___y_1789_);
lean_dec_ref(v_lctx_1778_);
lean_dec(v___x_1777_);
v___x_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1792_, 0, v_e_1776_);
lean_ctor_set(v___x_1792_, 1, v___y_1787_);
return v___x_1792_;
}
case 1:
{
lean_object* v___x_1793_; 
lean_dec(v___y_1789_);
lean_dec_ref(v_lctx_1778_);
lean_dec(v___x_1777_);
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v_e_1776_);
lean_ctor_set(v___x_1793_, 1, v___y_1787_);
return v___x_1793_;
}
case 4:
{
lean_object* v___x_1794_; 
lean_dec(v___y_1789_);
lean_dec_ref(v_lctx_1778_);
lean_dec(v___x_1777_);
v___x_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1794_, 0, v_e_1776_);
lean_ctor_set(v___x_1794_, 1, v___y_1787_);
return v___x_1794_;
}
case 3:
{
lean_object* v___x_1795_; 
lean_dec(v___y_1789_);
lean_dec_ref(v_lctx_1778_);
lean_dec(v___x_1777_);
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_e_1776_);
lean_ctor_set(v___x_1795_, 1, v___y_1787_);
return v___x_1795_;
}
default: 
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1796_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__2);
lean_inc(v___x_1777_);
v___x_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1777_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsPrefix_spec__0(v___y_1789_, v_lctx_1778_, v___y_1779_, v_n_1780_, v_xs_1781_, v_maxFVar_1782_, v_e_1776_, v___x_1777_, v___x_1797_, v_debug_1783_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1789_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1808_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_a_1800_ = lean_ctor_get(v___x_1798_, 1);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1802_ = v___x_1798_;
v_isShared_1803_ = v_isSharedCheck_1808_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1808_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v_fst_1804_; lean_object* v___x_1806_; 
v_fst_1804_ = lean_ctor_get(v_a_1799_, 0);
lean_inc(v_fst_1804_);
lean_dec(v_a_1799_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v_fst_1804_);
v___x_1806_ = v___x_1802_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_fst_1804_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_a_1800_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
v_a_1809_ = lean_ctor_get(v___x_1798_, 0);
v_a_1810_ = lean_ctor_get(v___x_1798_, 1);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1798_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_inc(v_a_1809_);
lean_dec(v___x_1798_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1809_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
}
v___jp_1818_:
{
lean_object* v_maxIndex_1821_; uint8_t v___x_1822_; 
v_maxIndex_1821_ = l_Lean_LocalDecl_index(v___y_1820_);
lean_dec_ref(v___y_1820_);
v___x_1822_ = lean_nat_dec_lt(v_maxIndex_1821_, v___y_1819_);
lean_dec(v_maxIndex_1821_);
if (v___x_1822_ == 0)
{
v___y_1789_ = v___y_1819_;
goto v___jp_1788_;
}
else
{
lean_object* v___x_1823_; 
lean_dec(v___y_1819_);
lean_dec_ref(v_lctx_1778_);
lean_dec(v___x_1777_);
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v_e_1776_);
lean_ctor_set(v___x_1823_, 1, v___y_1787_);
return v___x_1823_;
}
}
v___jp_1824_:
{
lean_object* v___x_1827_; 
lean_inc_ref(v_lctx_1778_);
v___x_1827_ = lean_local_ctx_find(v_lctx_1778_, v___y_1826_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1829_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1828_);
v___y_1819_ = v___y_1825_;
v___y_1820_ = v___x_1829_;
goto v___jp_1818_;
}
else
{
lean_object* v_val_1830_; 
v_val_1830_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_val_1830_);
lean_dec_ref_known(v___x_1827_, 1);
v___y_1819_ = v___y_1825_;
v___y_1820_ = v_val_1830_;
goto v___jp_1818_;
}
}
v___jp_1831_:
{
switch(lean_obj_tag(v_e_1776_))
{
case 1:
{
lean_object* v_fvarId_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec_ref(v___y_1832_);
lean_dec_ref(v_lctx_1778_);
v_fvarId_1833_ = lean_ctor_get(v_e_1776_, 0);
v___x_1834_ = lean_unsigned_to_nat(1u);
v___x_1835_ = lean_nat_sub(v___y_1779_, v___x_1834_);
v___x_1836_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsPrefix_go___redArg(v_xs_1781_, v_fvarId_1833_, v___x_1777_, v___x_1835_);
if (lean_obj_tag(v___x_1836_) == 1)
{
lean_object* v_val_1837_; lean_object* v___x_1838_; 
lean_dec_ref_known(v_e_1776_, 1);
v_val_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_val_1837_);
lean_dec_ref_known(v___x_1836_, 1);
v___x_1838_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v_val_1837_, v___y_1787_);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; 
lean_dec(v___x_1836_);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v_e_1776_);
lean_ctor_set(v___x_1839_, 1, v___y_1787_);
return v___x_1839_;
}
}
case 9:
{
lean_object* v___x_1840_; 
lean_dec_ref(v___y_1832_);
lean_dec_ref(v_lctx_1778_);
lean_dec(v___x_1777_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_e_1776_);
lean_ctor_set(v___x_1840_, 1, v___y_1787_);
return v___x_1840_;
}
case 2:
{
lean_object* v___x_1841_; 
lean_dec_ref(v___y_1832_);
lean_dec_ref(v_lctx_1778_);
lean_dec(v___x_1777_);
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v_e_1776_);
lean_ctor_set(v___x_1841_, 1, v___y_1787_);
return v___x_1841_;
}
case 0:
{
lean_object* v___x_1842_; 
lean_dec_ref(v___y_1832_);
lean_dec_ref(v_lctx_1778_);
lean_dec(v___x_1777_);
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v_e_1776_);
lean_ctor_set(v___x_1842_, 1, v___y_1787_);
return v___x_1842_;
}
case 4:
{
lean_object* v___x_1843_; 
lean_dec_ref(v___y_1832_);
lean_dec_ref(v_lctx_1778_);
lean_dec(v___x_1777_);
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v_e_1776_);
lean_ctor_set(v___x_1843_, 1, v___y_1787_);
return v___x_1843_;
}
case 3:
{
lean_object* v___x_1844_; 
lean_dec_ref(v___y_1832_);
lean_dec_ref(v_lctx_1778_);
lean_dec(v___x_1777_);
v___x_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1844_, 0, v_e_1776_);
lean_ctor_set(v___x_1844_, 1, v___y_1787_);
return v___x_1844_;
}
default: 
{
if (v___x_1784_ == 0)
{
lean_object* v___x_1845_; 
lean_dec_ref(v___y_1832_);
lean_dec_ref(v_lctx_1778_);
lean_dec(v___x_1777_);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_e_1776_);
lean_ctor_set(v___x_1845_, 1, v___y_1787_);
return v___x_1845_;
}
else
{
lean_object* v_minIndex_1846_; lean_object* v___x_1847_; 
v_minIndex_1846_ = l_Lean_LocalDecl_index(v___y_1832_);
lean_dec_ref(v___y_1832_);
v___x_1847_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_maxFVar_1782_, v_e_1776_);
if (lean_obj_tag(v___x_1847_) == 1)
{
lean_object* v_val_1848_; 
v_val_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_val_1848_);
lean_dec_ref_known(v___x_1847_, 1);
if (lean_obj_tag(v_val_1848_) == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1850_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v___x_1849_);
v___y_1825_ = v_minIndex_1846_;
v___y_1826_ = v___x_1850_;
goto v___jp_1824_;
}
else
{
lean_object* v_val_1851_; 
v_val_1851_ = lean_ctor_get(v_val_1848_, 0);
lean_inc(v_val_1851_);
lean_dec_ref_known(v_val_1848_, 1);
v___y_1825_ = v_minIndex_1846_;
v___y_1826_ = v_val_1851_;
goto v___jp_1824_;
}
}
else
{
lean_dec(v___x_1847_);
v___y_1789_ = v_minIndex_1846_;
goto v___jp_1788_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_abstractFVarsPrefix___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1776_ = stack[0].m_obj;
lean_object* v___x_1777_ = stack[1].m_obj;
lean_object* v_lctx_1778_ = stack[2].m_obj;
lean_object* v___y_1779_ = stack[3].m_obj;
lean_object* v_n_1780_ = stack[4].m_obj;
lean_object* v_xs_1781_ = stack[5].m_obj;
lean_object* v_maxFVar_1782_ = stack[6].m_obj;
uint8_t v_debug_1783_ = stack[7].m_num;
uint8_t v___x_1784_ = stack[8].m_num;
lean_object* v___x_1785_ = stack[9].m_obj;
lean_object* v___y_1786_ = stack[10].m_obj;
lean_object* v___y_1787_ = stack[11].m_obj;
lean_object* v_res_1856_;
v_res_1856_ = l_Lean_Meta_Sym_abstractFVarsPrefix___lam__0(v_e_1776_, v___x_1777_, v_lctx_1778_, v___y_1779_, v_n_1780_, v_xs_1781_, v_maxFVar_1782_, v_debug_1783_, v___x_1784_, v___x_1785_, v___y_1786_, v___y_1787_);
stack->m_obj
 = v_res_1856_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsPrefix___lam__0___boxed(lean_object* v_e_1857_, lean_object* v___x_1858_, lean_object* v_lctx_1859_, lean_object* v___y_1860_, lean_object* v_n_1861_, lean_object* v_xs_1862_, lean_object* v_maxFVar_1863_, lean_object* v_debug_1864_, lean_object* v___x_1865_, lean_object* v___x_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
uint8_t v_debug_boxed_1869_; uint8_t v___x_3965__boxed_1870_; lean_object* v_res_1871_; 
v_debug_boxed_1869_ = lean_unbox(v_debug_1864_);
v___x_3965__boxed_1870_ = lean_unbox(v___x_1865_);
v_res_1871_ = l_Lean_Meta_Sym_abstractFVarsPrefix___lam__0(v_e_1857_, v___x_1858_, v_lctx_1859_, v___y_1860_, v_n_1861_, v_xs_1862_, v_maxFVar_1863_, v_debug_boxed_1869_, v___x_3965__boxed_1870_, v___x_1866_, v___y_1867_, v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec_ref(v_maxFVar_1863_);
lean_dec_ref(v_xs_1862_);
lean_dec(v_n_1861_);
lean_dec(v___y_1860_);
return v_res_1871_;
}
}
lean_object* l_Lean_Meta_Sym_abstractFVarsPrefix(lean_object* v_e_1872_, lean_object* v_n_1873_, lean_object* v_xs_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
uint8_t v___x_1882_; 
v___x_1882_ = l_Lean_Expr_hasFVar(v_e_1872_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1883_; 
lean_dec_ref(v_xs_1874_);
lean_dec(v_n_1873_);
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v_e_1872_);
return v___x_1883_;
}
else
{
uint8_t v___x_1884_; lean_object* v___y_1886_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1884_ = 0;
v___x_1923_ = lean_array_get_size(v_xs_1874_);
v___x_1924_ = lean_nat_dec_le(v_n_1873_, v___x_1923_);
if (v___x_1924_ == 0)
{
v___y_1886_ = v___x_1923_;
goto v___jp_1885_;
}
else
{
lean_inc(v_n_1873_);
v___y_1886_ = v_n_1873_;
goto v___jp_1885_;
}
v___jp_1885_:
{
lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1887_ = lean_unsigned_to_nat(0u);
v___x_1888_ = lean_nat_dec_lt(v___x_1887_, v___y_1886_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; 
lean_dec(v___y_1886_);
lean_dec_ref(v_xs_1874_);
lean_dec(v_n_1873_);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v_e_1872_);
return v___x_1889_;
}
else
{
lean_object* v_lctx_1890_; lean_object* v___x_1891_; lean_object* v_maxFVar_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v_debug_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___f_1899_; lean_object* v___x_1900_; lean_object* v_env_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v_lctx_1890_ = lean_ctor_get(v_a_1877_, 2);
v___x_1891_ = lean_st_ref_get(v_a_1876_);
v_maxFVar_1892_ = lean_ctor_get(v___x_1891_, 1);
lean_inc_ref(v_maxFVar_1892_);
lean_dec(v___x_1891_);
v___x_1893_ = lean_array_fget_borrowed(v_xs_1874_, v___x_1887_);
v___x_1894_ = l_Lean_Expr_fvarId_x21(v___x_1893_);
v___x_1895_ = lean_st_ref_get(v_a_1876_);
v_debug_1896_ = lean_ctor_get_uint8(v___x_1895_, sizeof(void*)*12);
lean_dec(v___x_1895_);
v___x_1897_ = lean_box(v_debug_1896_);
v___x_1898_ = lean_box(v___x_1882_);
lean_inc_ref(v_lctx_1890_);
v___f_1899_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_abstractFVarsPrefix___lam__0___boxed), 12, 10);
lean_closure_set(v___f_1899_, 0, v_e_1872_);
lean_closure_set(v___f_1899_, 1, v___x_1887_);
lean_closure_set(v___f_1899_, 2, v_lctx_1890_);
lean_closure_set(v___f_1899_, 3, v___y_1886_);
lean_closure_set(v___f_1899_, 4, v_n_1873_);
lean_closure_set(v___f_1899_, 5, v_xs_1874_);
lean_closure_set(v___f_1899_, 6, v_maxFVar_1892_);
lean_closure_set(v___f_1899_, 7, v___x_1897_);
lean_closure_set(v___f_1899_, 8, v___x_1898_);
lean_closure_set(v___f_1899_, 9, v___x_1894_);
v___x_1900_ = lean_st_ref_get(v_a_1880_);
v_env_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc_ref(v_env_1901_);
lean_dec(v___x_1900_);
v___x_1902_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1902_, 0, v_env_1901_);
lean_ctor_set_uint8(v___x_1902_, sizeof(void*)*1, v___x_1884_);
lean_ctor_set_uint8(v___x_1902_, sizeof(void*)*1 + 1, v___x_1884_);
v___x_1903_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1899_, v___x_1902_, v_a_1876_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1914_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1906_ = v___x_1903_;
v_isShared_1907_ = v_isSharedCheck_1914_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1903_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1914_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
if (lean_obj_tag(v_a_1904_) == 0)
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
lean_dec_ref_known(v_a_1904_, 1);
lean_del_object(v___x_1906_);
v___x_1908_ = lean_obj_once(&l_Lean_Meta_Sym_abstractFVarsRange___closed__2, &l_Lean_Meta_Sym_abstractFVarsRange___closed__2_once, _init_l_Lean_Meta_Sym_abstractFVarsRange___closed__2);
v___x_1909_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v___x_1908_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
return v___x_1909_;
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; 
v_a_1910_ = lean_ctor_get(v_a_1904_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v_a_1904_, 1);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v_a_1910_);
v___x_1912_ = v___x_1906_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
v_a_1915_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1903_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1903_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_abstractFVarsPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1872_ = stack[0].m_obj;
lean_object* v_n_1873_ = stack[1].m_obj;
lean_object* v_xs_1874_ = stack[2].m_obj;
lean_object* v_a_1875_ = stack[3].m_obj;
lean_object* v_a_1876_ = stack[4].m_obj;
lean_object* v_a_1877_ = stack[5].m_obj;
lean_object* v_a_1878_ = stack[6].m_obj;
lean_object* v_a_1879_ = stack[7].m_obj;
lean_object* v_a_1880_ = stack[8].m_obj;
lean_object* v_res_1925_;
v_res_1925_ = l_Lean_Meta_Sym_abstractFVarsPrefix(v_e_1872_, v_n_1873_, v_xs_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
stack->m_obj
 = v_res_1925_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsPrefix___boxed(lean_object* v_e_1926_, lean_object* v_n_1927_, lean_object* v_xs_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_Meta_Sym_abstractFVarsPrefix(v_e_1926_, v_n_1927_, v_xs_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
return v_res_1936_;
}
}
lean_object* l_Lean_Meta_Sym_abstractFVars(lean_object* v_e_1937_, lean_object* v_xs_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = lean_unsigned_to_nat(0u);
v___x_1947_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1937_, v___x_1946_, v_xs_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
return v___x_1947_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_abstractFVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1937_ = stack[0].m_obj;
lean_object* v_xs_1938_ = stack[1].m_obj;
lean_object* v_a_1939_ = stack[2].m_obj;
lean_object* v_a_1940_ = stack[3].m_obj;
lean_object* v_a_1941_ = stack[4].m_obj;
lean_object* v_a_1942_ = stack[5].m_obj;
lean_object* v_a_1943_ = stack[6].m_obj;
lean_object* v_a_1944_ = stack[7].m_obj;
lean_object* v_res_1948_;
v_res_1948_ = l_Lean_Meta_Sym_abstractFVars(v_e_1937_, v_xs_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
stack->m_obj
 = v_res_1948_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___boxed(lean_object* v_e_1949_, lean_object* v_xs_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_Meta_Sym_abstractFVars(v_e_1949_, v_xs_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
return v_res_1958_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(lean_object* v_x_1959_, uint8_t v_bi_1960_, lean_object* v_t_1961_, lean_object* v_b_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v___y_1971_; lean_object* v___x_1974_; uint8_t v_debug_1975_; 
v___x_1974_ = lean_st_ref_get(v___y_1964_);
v_debug_1975_ = lean_ctor_get_uint8(v___x_1974_, sizeof(void*)*12);
lean_dec(v___x_1974_);
if (v_debug_1975_ == 0)
{
v___y_1971_ = v___y_1964_;
goto v___jp_1970_;
}
else
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1961_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v___x_1977_; 
lean_dec_ref_known(v___x_1976_, 1);
v___x_1977_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_dec_ref_known(v___x_1977_, 1);
v___y_1971_ = v___y_1964_;
goto v___jp_1970_;
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec_ref(v_b_1962_);
lean_dec_ref(v_t_1961_);
lean_dec(v_x_1959_);
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec_ref(v_b_1962_);
lean_dec_ref(v_t_1961_);
lean_dec(v_x_1959_);
v_a_1986_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1976_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1976_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
v___jp_1970_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = l_Lean_Expr_lam___override(v_x_1959_, v_t_1961_, v_b_1962_, v_bi_1960_);
v___x_1973_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1972_, v___y_1971_);
return v___x_1973_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1959_ = stack[0].m_obj;
uint8_t v_bi_1960_ = stack[1].m_num;
lean_object* v_t_1961_ = stack[2].m_obj;
lean_object* v_b_1962_ = stack[3].m_obj;
lean_object* v___y_1963_ = stack[4].m_obj;
lean_object* v___y_1964_ = stack[5].m_obj;
lean_object* v___y_1965_ = stack[6].m_obj;
lean_object* v___y_1966_ = stack[7].m_obj;
lean_object* v___y_1967_ = stack[8].m_obj;
lean_object* v___y_1968_ = stack[9].m_obj;
lean_object* v_res_1994_;
v_res_1994_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v_x_1959_, v_bi_1960_, v_t_1961_, v_b_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
stack->m_obj
 = v_res_1994_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0___boxed(lean_object* v_x_1995_, lean_object* v_bi_1996_, lean_object* v_t_1997_, lean_object* v_b_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
uint8_t v_bi_boxed_2006_; lean_object* v_res_2007_; 
v_bi_boxed_2006_ = lean_unbox(v_bi_1996_);
v_res_2007_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v_x_1995_, v_bi_boxed_2006_, v_t_1997_, v_b_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
return v_res_2007_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(lean_object* v_xs_2008_, lean_object* v_i_2009_, lean_object* v_a_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_zero_2018_; uint8_t v_isZero_2019_; 
v_zero_2018_ = lean_unsigned_to_nat(0u);
v_isZero_2019_ = lean_nat_dec_eq(v_i_2009_, v_zero_2018_);
if (v_isZero_2019_ == 1)
{
lean_object* v___x_2020_; 
lean_dec(v_i_2009_);
lean_dec_ref(v_xs_2008_);
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v_a_2010_);
return v___x_2020_;
}
else
{
lean_object* v_one_2021_; lean_object* v_n_2022_; lean_object* v___y_2024_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v_one_2021_ = lean_unsigned_to_nat(1u);
v_n_2022_ = lean_nat_sub(v_i_2009_, v_one_2021_);
lean_dec(v_i_2009_);
v___x_2027_ = lean_array_fget_borrowed(v_xs_2008_, v_n_2022_);
v___x_2028_ = l_Lean_Expr_fvarId_x21(v___x_2027_);
v___x_2029_ = l_Lean_FVarId_getDecl___redArg(v___x_2028_, v___y_2013_, v___y_2015_, v___y_2016_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2029_, 1);
v___x_2031_ = l_Lean_LocalDecl_type(v_a_2030_);
lean_inc_ref(v_xs_2008_);
lean_inc(v_n_2022_);
v___x_2032_ = l_Lean_Meta_Sym_abstractFVarsPrefix(v___x_2031_, v_n_2022_, v_xs_2008_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; lean_object* v___x_2036_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2032_, 1);
v___x_2034_ = l_Lean_LocalDecl_userName(v_a_2030_);
v___x_2035_ = l_Lean_LocalDecl_binderInfo(v_a_2030_);
lean_dec(v_a_2030_);
v___x_2036_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v___x_2034_, v___x_2035_, v_a_2033_, v_a_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
v___y_2024_ = v___x_2036_;
goto v___jp_2023_;
}
else
{
lean_dec(v_a_2030_);
lean_dec_ref(v_a_2010_);
v___y_2024_ = v___x_2032_;
goto v___jp_2023_;
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v_n_2022_);
lean_dec_ref(v_a_2010_);
lean_dec_ref(v_xs_2008_);
v_a_2037_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2029_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2029_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
v___jp_2023_:
{
if (lean_obj_tag(v___y_2024_) == 0)
{
lean_object* v_a_2025_; 
v_a_2025_ = lean_ctor_get(v___y_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___y_2024_, 1);
v_i_2009_ = v_n_2022_;
v_a_2010_ = v_a_2025_;
goto _start;
}
else
{
lean_dec(v_n_2022_);
lean_dec_ref(v_xs_2008_);
return v___y_2024_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2008_ = stack[0].m_obj;
lean_object* v_i_2009_ = stack[1].m_obj;
lean_object* v_a_2010_ = stack[2].m_obj;
lean_object* v___y_2011_ = stack[3].m_obj;
lean_object* v___y_2012_ = stack[4].m_obj;
lean_object* v___y_2013_ = stack[5].m_obj;
lean_object* v___y_2014_ = stack[6].m_obj;
lean_object* v___y_2015_ = stack[7].m_obj;
lean_object* v___y_2016_ = stack[8].m_obj;
lean_object* v_res_2045_;
v_res_2045_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_2008_, v_i_2009_, v_a_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
stack->m_obj
 = v_res_2045_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg___boxed(lean_object* v_xs_2046_, lean_object* v_i_2047_, lean_object* v_a_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_2046_, v_i_2047_, v_a_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
return v_res_2056_;
}
}
lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS(lean_object* v_xs_2057_, lean_object* v_e_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_xs_2057_);
v___x_2067_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_2058_, v___x_2066_, v_xs_2057_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref_known(v___x_2067_, 1);
v___x_2069_ = lean_array_get_size(v_xs_2057_);
v___x_2070_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_2057_, v___x_2069_, v_a_2068_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
return v___x_2070_;
}
else
{
lean_dec_ref(v_xs_2057_);
return v___x_2067_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_mkLambdaFVarsS_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2057_ = stack[0].m_obj;
lean_object* v_e_2058_ = stack[1].m_obj;
lean_object* v_a_2059_ = stack[2].m_obj;
lean_object* v_a_2060_ = stack[3].m_obj;
lean_object* v_a_2061_ = stack[4].m_obj;
lean_object* v_a_2062_ = stack[5].m_obj;
lean_object* v_a_2063_ = stack[6].m_obj;
lean_object* v_a_2064_ = stack[7].m_obj;
lean_object* v_res_2071_;
v_res_2071_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_2057_, v_e_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
stack->m_obj
 = v_res_2071_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS___boxed(lean_object* v_xs_2072_, lean_object* v_e_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_2072_, v_e_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
return v_res_2081_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(lean_object* v_xs_2082_, lean_object* v_n_2083_, lean_object* v_i_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_2082_, v_i_2084_, v_a_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
return v___x_2094_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2082_ = stack[0].m_obj;
lean_object* v_n_2083_ = stack[1].m_obj;
lean_object* v_i_2084_ = stack[2].m_obj;
lean_object* v_a_2086_ = stack[4].m_obj;
lean_object* v___y_2087_ = stack[5].m_obj;
lean_object* v___y_2088_ = stack[6].m_obj;
lean_object* v___y_2089_ = stack[7].m_obj;
lean_object* v___y_2090_ = stack[8].m_obj;
lean_object* v___y_2091_ = stack[9].m_obj;
lean_object* v___y_2092_ = stack[10].m_obj;
lean_object* v_res_2095_;
v_res_2095_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(v_xs_2082_, v_n_2083_, v_i_2084_, lean_box(0), v_a_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
stack->m_obj
 = v_res_2095_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___boxed(lean_object* v_xs_2096_, lean_object* v_n_2097_, lean_object* v_i_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(v_xs_2096_, v_n_2097_, v_i_2098_, v_a_2099_, v_a_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v_n_2097_);
return v_res_2108_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(lean_object* v_x_2109_, uint8_t v_bi_2110_, lean_object* v_t_2111_, lean_object* v_b_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___y_2121_; lean_object* v___x_2124_; uint8_t v_debug_2125_; 
v___x_2124_ = lean_st_ref_get(v___y_2114_);
v_debug_2125_ = lean_ctor_get_uint8(v___x_2124_, sizeof(void*)*12);
lean_dec(v___x_2124_);
if (v_debug_2125_ == 0)
{
v___y_2121_ = v___y_2114_;
goto v___jp_2120_;
}
else
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2111_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v___x_2127_; 
lean_dec_ref_known(v___x_2126_, 1);
v___x_2127_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_dec_ref_known(v___x_2127_, 1);
v___y_2121_ = v___y_2114_;
goto v___jp_2120_;
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec_ref(v_b_2112_);
lean_dec_ref(v_t_2111_);
lean_dec(v_x_2109_);
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2127_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2127_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec_ref(v_b_2112_);
lean_dec_ref(v_t_2111_);
lean_dec(v_x_2109_);
v_a_2136_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2126_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2126_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
v___jp_2120_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = l_Lean_Expr_forallE___override(v_x_2109_, v_t_2111_, v_b_2112_, v_bi_2110_);
v___x_2123_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2122_, v___y_2121_);
return v___x_2123_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2109_ = stack[0].m_obj;
uint8_t v_bi_2110_ = stack[1].m_num;
lean_object* v_t_2111_ = stack[2].m_obj;
lean_object* v_b_2112_ = stack[3].m_obj;
lean_object* v___y_2113_ = stack[4].m_obj;
lean_object* v___y_2114_ = stack[5].m_obj;
lean_object* v___y_2115_ = stack[6].m_obj;
lean_object* v___y_2116_ = stack[7].m_obj;
lean_object* v___y_2117_ = stack[8].m_obj;
lean_object* v___y_2118_ = stack[9].m_obj;
lean_object* v_res_2144_;
v_res_2144_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v_x_2109_, v_bi_2110_, v_t_2111_, v_b_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
stack->m_obj
 = v_res_2144_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0___boxed(lean_object* v_x_2145_, lean_object* v_bi_2146_, lean_object* v_t_2147_, lean_object* v_b_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
uint8_t v_bi_boxed_2156_; lean_object* v_res_2157_; 
v_bi_boxed_2156_ = lean_unbox(v_bi_2146_);
v_res_2157_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v_x_2145_, v_bi_boxed_2156_, v_t_2147_, v_b_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
return v_res_2157_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(lean_object* v_xs_2158_, lean_object* v_i_2159_, lean_object* v_a_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_zero_2168_; uint8_t v_isZero_2169_; 
v_zero_2168_ = lean_unsigned_to_nat(0u);
v_isZero_2169_ = lean_nat_dec_eq(v_i_2159_, v_zero_2168_);
if (v_isZero_2169_ == 1)
{
lean_object* v___x_2170_; 
lean_dec(v_i_2159_);
lean_dec_ref(v_xs_2158_);
v___x_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2170_, 0, v_a_2160_);
return v___x_2170_;
}
else
{
lean_object* v_one_2171_; lean_object* v_n_2172_; lean_object* v___y_2174_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v_one_2171_ = lean_unsigned_to_nat(1u);
v_n_2172_ = lean_nat_sub(v_i_2159_, v_one_2171_);
lean_dec(v_i_2159_);
v___x_2177_ = lean_array_fget_borrowed(v_xs_2158_, v_n_2172_);
v___x_2178_ = l_Lean_Expr_fvarId_x21(v___x_2177_);
v___x_2179_ = l_Lean_FVarId_getDecl___redArg(v___x_2178_, v___y_2163_, v___y_2165_, v___y_2166_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2179_, 1);
v___x_2181_ = l_Lean_LocalDecl_type(v_a_2180_);
lean_inc_ref(v_xs_2158_);
lean_inc(v_n_2172_);
v___x_2182_ = l_Lean_Meta_Sym_abstractFVarsPrefix(v___x_2181_, v_n_2172_, v_xs_2158_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; lean_object* v___x_2186_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v___x_2184_ = l_Lean_LocalDecl_userName(v_a_2180_);
v___x_2185_ = l_Lean_LocalDecl_binderInfo(v_a_2180_);
lean_dec(v_a_2180_);
v___x_2186_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v___x_2184_, v___x_2185_, v_a_2183_, v_a_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
v___y_2174_ = v___x_2186_;
goto v___jp_2173_;
}
else
{
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2160_);
v___y_2174_ = v___x_2182_;
goto v___jp_2173_;
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_n_2172_);
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_xs_2158_);
v_a_2187_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2179_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2179_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
v___jp_2173_:
{
if (lean_obj_tag(v___y_2174_) == 0)
{
lean_object* v_a_2175_; 
v_a_2175_ = lean_ctor_get(v___y_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___y_2174_, 1);
v_i_2159_ = v_n_2172_;
v_a_2160_ = v_a_2175_;
goto _start;
}
else
{
lean_dec(v_n_2172_);
lean_dec_ref(v_xs_2158_);
return v___y_2174_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2158_ = stack[0].m_obj;
lean_object* v_i_2159_ = stack[1].m_obj;
lean_object* v_a_2160_ = stack[2].m_obj;
lean_object* v___y_2161_ = stack[3].m_obj;
lean_object* v___y_2162_ = stack[4].m_obj;
lean_object* v___y_2163_ = stack[5].m_obj;
lean_object* v___y_2164_ = stack[6].m_obj;
lean_object* v___y_2165_ = stack[7].m_obj;
lean_object* v___y_2166_ = stack[8].m_obj;
lean_object* v_res_2195_;
v_res_2195_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_2158_, v_i_2159_, v_a_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
stack->m_obj
 = v_res_2195_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg___boxed(lean_object* v_xs_2196_, lean_object* v_i_2197_, lean_object* v_a_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_2196_, v_i_2197_, v_a_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
return v_res_2206_;
}
}
lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object* v_xs_2207_, lean_object* v_e_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_xs_2207_);
v___x_2217_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_2208_, v___x_2216_, v_xs_2207_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2219_ = lean_array_get_size(v_xs_2207_);
v___x_2220_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_2207_, v___x_2219_, v_a_2218_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
return v___x_2220_;
}
else
{
lean_dec_ref(v_xs_2207_);
return v___x_2217_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_mkForallFVarsS_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2207_ = stack[0].m_obj;
lean_object* v_e_2208_ = stack[1].m_obj;
lean_object* v_a_2209_ = stack[2].m_obj;
lean_object* v_a_2210_ = stack[3].m_obj;
lean_object* v_a_2211_ = stack[4].m_obj;
lean_object* v_a_2212_ = stack[5].m_obj;
lean_object* v_a_2213_ = stack[6].m_obj;
lean_object* v_a_2214_ = stack[7].m_obj;
lean_object* v_res_2221_;
v_res_2221_ = l_Lean_Meta_Sym_mkForallFVarsS(v_xs_2207_, v_e_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
stack->m_obj
 = v_res_2221_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS___boxed(lean_object* v_xs_2222_, lean_object* v_e_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Meta_Sym_mkForallFVarsS(v_xs_2222_, v_e_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
return v_res_2231_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(lean_object* v_xs_2232_, lean_object* v_n_2233_, lean_object* v_i_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_2232_, v_i_2234_, v_a_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
return v___x_2244_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2232_ = stack[0].m_obj;
lean_object* v_n_2233_ = stack[1].m_obj;
lean_object* v_i_2234_ = stack[2].m_obj;
lean_object* v_a_2236_ = stack[4].m_obj;
lean_object* v___y_2237_ = stack[5].m_obj;
lean_object* v___y_2238_ = stack[6].m_obj;
lean_object* v___y_2239_ = stack[7].m_obj;
lean_object* v___y_2240_ = stack[8].m_obj;
lean_object* v___y_2241_ = stack[9].m_obj;
lean_object* v___y_2242_ = stack[10].m_obj;
lean_object* v_res_2245_;
v_res_2245_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(v_xs_2232_, v_n_2233_, v_i_2234_, lean_box(0), v_a_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
stack->m_obj
 = v_res_2245_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___boxed(lean_object* v_xs_2246_, lean_object* v_n_2247_, lean_object* v_i_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(v_xs_2246_, v_n_2247_, v_i_2248_, v_a_2249_, v_a_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v_n_2247_);
return v_res_2258_;
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
