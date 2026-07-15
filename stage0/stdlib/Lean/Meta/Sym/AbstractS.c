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
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
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
static const lean_closure_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
uint8_t v___y_25665__boxed_290_; lean_object* v_res_291_; 
v___y_25665__boxed_290_ = lean_unbox(v___y_287_);
v_res_291_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v_idx_286_, v___y_25665__boxed_290_, v___y_288_, v___y_289_);
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
lean_object* v___x_304_; lean_object* v___x_2574__overap_305_; lean_object* v___x_306_; 
v___x_304_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0, &l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0);
v___x_2574__overap_305_ = lean_panic_fn_borrowed(v___x_304_, v_msg_296_);
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
lean_inc(v___y_300_);
lean_inc_ref(v___y_299_);
lean_inc(v___y_298_);
lean_inc_ref(v___y_297_);
v___x_306_ = lean_apply_7(v___x_2574__overap_305_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, lean_box(0));
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
lean_object* v___f_328_; lean_object* v___f_329_; lean_object* v___f_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___f_340_; lean_object* v___f_341_; lean_object* v___f_342_; lean_object* v___f_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_25194__overap_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
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
v___x_25194__overap_352_ = lean_panic_fn_borrowed(v___x_351_, v_msg_323_);
lean_dec(v___x_351_);
v___x_353_ = lean_box(v___y_325_);
lean_inc_ref(v___y_326_);
v___x_354_ = lean_apply_4(v___x_25194__overap_352_, v___y_324_, v___x_353_, v___y_326_, v___y_327_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___boxed(lean_object* v_msg_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
uint8_t v___y_25723__boxed_360_; lean_object* v_res_361_; 
v___y_25723__boxed_360_ = lean_unbox(v___y_357_);
v_res_361_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(v_msg_355_, v___y_356_, v___y_25723__boxed_360_, v___y_358_, v___y_359_);
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
uint8_t v___y_25794__boxed_411_; lean_object* v_res_412_; 
v___y_25794__boxed_411_ = lean_unbox(v___y_408_);
v_res_412_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(v_structName_404_, v_idx_405_, v_struct_406_, v___y_407_, v___y_25794__boxed_411_, v___y_409_, v___y_410_);
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
uint8_t v___y_25877__boxed_460_; lean_object* v_res_461_; 
v___y_25877__boxed_460_ = lean_unbox(v___y_457_);
v_res_461_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(v_d_454_, v_e_455_, v___y_456_, v___y_25877__boxed_460_, v___y_458_, v___y_459_);
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
lean_object* v_k_x27_469_; uint8_t v___x_470_; 
v_k_x27_469_ = lean_array_fget_borrowed(v_keys_462_, v_i_464_);
v___x_470_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_465_, v_k_x27_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_472_ = lean_nat_add(v_i_464_, v___x_471_);
lean_dec(v_i_464_);
v_i_464_ = v___x_472_;
goto _start;
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_array_fget_borrowed(v_vals_463_, v_i_464_);
lean_dec(v_i_464_);
lean_inc(v___x_474_);
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_keys_476_, lean_object* v_vals_477_, lean_object* v_i_478_, lean_object* v_k_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_keys_476_, v_vals_477_, v_i_478_, v_k_479_);
lean_dec_ref(v_k_479_);
lean_dec_ref(v_vals_477_);
lean_dec_ref(v_keys_476_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(lean_object* v_x_481_, size_t v_x_482_, lean_object* v_x_483_){
_start:
{
if (lean_obj_tag(v_x_481_) == 0)
{
lean_object* v_es_484_; lean_object* v___x_485_; size_t v___x_486_; size_t v___x_487_; lean_object* v_j_488_; lean_object* v___x_489_; 
v_es_484_ = lean_ctor_get(v_x_481_, 0);
v___x_485_ = lean_box(2);
v___x_486_ = ((size_t)31ULL);
v___x_487_ = lean_usize_land(v_x_482_, v___x_486_);
v_j_488_ = lean_usize_to_nat(v___x_487_);
v___x_489_ = lean_array_get_borrowed(v___x_485_, v_es_484_, v_j_488_);
lean_dec(v_j_488_);
switch(lean_obj_tag(v___x_489_))
{
case 0:
{
lean_object* v_key_490_; lean_object* v_val_491_; uint8_t v___x_492_; 
v_key_490_ = lean_ctor_get(v___x_489_, 0);
v_val_491_ = lean_ctor_get(v___x_489_, 1);
v___x_492_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_483_, v_key_490_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
v___x_493_ = lean_box(0);
return v___x_493_;
}
else
{
lean_object* v___x_494_; 
lean_inc(v_val_491_);
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v_val_491_);
return v___x_494_;
}
}
case 1:
{
lean_object* v_node_495_; size_t v___x_496_; size_t v___x_497_; 
v_node_495_ = lean_ctor_get(v___x_489_, 0);
v___x_496_ = ((size_t)5ULL);
v___x_497_ = lean_usize_shift_right(v_x_482_, v___x_496_);
v_x_481_ = v_node_495_;
v_x_482_ = v___x_497_;
goto _start;
}
default: 
{
lean_object* v___x_499_; 
v___x_499_ = lean_box(0);
return v___x_499_;
}
}
}
else
{
lean_object* v_ks_500_; lean_object* v_vs_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_ks_500_ = lean_ctor_get(v_x_481_, 0);
v_vs_501_ = lean_ctor_get(v_x_481_, 1);
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_ks_500_, v_vs_501_, v___x_502_, v_x_483_);
return v___x_503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg___boxed(lean_object* v_x_504_, lean_object* v_x_505_, lean_object* v_x_506_){
_start:
{
size_t v_x_25978__boxed_507_; lean_object* v_res_508_; 
v_x_25978__boxed_507_ = lean_unbox_usize(v_x_505_);
lean_dec(v_x_505_);
v_res_508_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_504_, v_x_25978__boxed_507_, v_x_506_);
lean_dec_ref(v_x_506_);
lean_dec_ref(v_x_504_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
uint64_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; 
v___x_511_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_510_);
v___x_512_ = lean_uint64_to_usize(v___x_511_);
v___x_513_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_509_, v___x_512_, v_x_510_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg___boxed(lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_x_514_, v_x_515_);
lean_dec_ref(v_x_515_);
lean_dec_ref(v_x_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(lean_object* v_a_517_, lean_object* v_x_518_){
_start:
{
if (lean_obj_tag(v_x_518_) == 0)
{
lean_object* v___x_519_; 
v___x_519_ = lean_box(0);
return v___x_519_;
}
else
{
lean_object* v_key_520_; lean_object* v_value_521_; lean_object* v_tail_522_; uint8_t v___y_524_; lean_object* v_fst_527_; lean_object* v_snd_528_; lean_object* v_fst_529_; lean_object* v_snd_530_; uint8_t v___x_531_; 
v_key_520_ = lean_ctor_get(v_x_518_, 0);
v_value_521_ = lean_ctor_get(v_x_518_, 1);
v_tail_522_ = lean_ctor_get(v_x_518_, 2);
v_fst_527_ = lean_ctor_get(v_key_520_, 0);
v_snd_528_ = lean_ctor_get(v_key_520_, 1);
v_fst_529_ = lean_ctor_get(v_a_517_, 0);
v_snd_530_ = lean_ctor_get(v_a_517_, 1);
v___x_531_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_527_, v_fst_529_);
if (v___x_531_ == 0)
{
v___y_524_ = v___x_531_;
goto v___jp_523_;
}
else
{
uint8_t v___x_532_; 
v___x_532_ = lean_nat_dec_eq(v_snd_528_, v_snd_530_);
v___y_524_ = v___x_532_;
goto v___jp_523_;
}
v___jp_523_:
{
if (v___y_524_ == 0)
{
v_x_518_ = v_tail_522_;
goto _start;
}
else
{
lean_object* v___x_526_; 
lean_inc(v_value_521_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v_value_521_);
return v___x_526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg___boxed(lean_object* v_a_533_, lean_object* v_x_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_a_533_, v_x_534_);
lean_dec(v_x_534_);
lean_dec_ref(v_a_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(lean_object* v_m_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_buckets_538_; lean_object* v_fst_539_; lean_object* v_snd_540_; lean_object* v___x_541_; uint64_t v___x_542_; uint64_t v___x_543_; uint64_t v___x_544_; uint64_t v___x_545_; uint64_t v___x_546_; uint64_t v_fold_547_; uint64_t v___x_548_; uint64_t v___x_549_; uint64_t v___x_550_; size_t v___x_551_; size_t v___x_552_; size_t v___x_553_; size_t v___x_554_; size_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_buckets_538_ = lean_ctor_get(v_m_536_, 1);
v_fst_539_ = lean_ctor_get(v_a_537_, 0);
v_snd_540_ = lean_ctor_get(v_a_537_, 1);
v___x_541_ = lean_array_get_size(v_buckets_538_);
v___x_542_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_539_);
v___x_543_ = lean_uint64_of_nat(v_snd_540_);
v___x_544_ = lean_uint64_mix_hash(v___x_542_, v___x_543_);
v___x_545_ = 32ULL;
v___x_546_ = lean_uint64_shift_right(v___x_544_, v___x_545_);
v_fold_547_ = lean_uint64_xor(v___x_544_, v___x_546_);
v___x_548_ = 16ULL;
v___x_549_ = lean_uint64_shift_right(v_fold_547_, v___x_548_);
v___x_550_ = lean_uint64_xor(v_fold_547_, v___x_549_);
v___x_551_ = lean_uint64_to_usize(v___x_550_);
v___x_552_ = lean_usize_of_nat(v___x_541_);
v___x_553_ = ((size_t)1ULL);
v___x_554_ = lean_usize_sub(v___x_552_, v___x_553_);
v___x_555_ = lean_usize_land(v___x_551_, v___x_554_);
v___x_556_ = lean_array_uget_borrowed(v_buckets_538_, v___x_555_);
v___x_557_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_a_537_, v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_m_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_m_558_, v_a_559_);
lean_dec_ref(v_a_559_);
lean_dec_ref(v_m_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(lean_object* v_x_561_, uint8_t v_bi_562_, lean_object* v_t_563_, lean_object* v_b_564_, lean_object* v___y_565_, uint8_t v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___y_570_; lean_object* v___y_571_; 
if (v___y_566_ == 0)
{
v___y_570_ = v___y_565_;
v___y_571_ = v___y_568_;
goto v___jp_569_;
}
else
{
lean_object* v___x_593_; 
lean_inc_ref(v_t_563_);
v___x_593_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_563_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_595_; 
v_a_594_ = lean_ctor_get(v___x_593_, 1);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 2);
lean_inc_ref(v_b_564_);
v___x_595_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_564_, v___y_566_, v___y_567_, v_a_594_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; 
v_a_596_ = lean_ctor_get(v___x_595_, 1);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 2);
v___y_570_ = v___y_565_;
v___y_571_ = v_a_596_;
goto v___jp_569_;
}
else
{
lean_object* v_a_597_; lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec_ref(v___y_565_);
lean_dec_ref(v_b_564_);
lean_dec_ref(v_t_563_);
lean_dec(v_x_561_);
v_a_597_ = lean_ctor_get(v___x_595_, 0);
v_a_598_ = lean_ctor_get(v___x_595_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_595_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_inc(v_a_597_);
lean_dec(v___x_595_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_597_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v___y_565_);
lean_dec_ref(v_b_564_);
lean_dec_ref(v_t_563_);
lean_dec(v_x_561_);
v_a_606_ = lean_ctor_get(v___x_593_, 0);
v_a_607_ = lean_ctor_get(v___x_593_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_593_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_inc(v_a_606_);
lean_dec(v___x_593_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_606_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
v___jp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = l_Lean_Expr_forallE___override(v_x_561_, v_t_563_, v_b_564_, v_bi_562_);
v___x_573_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_572_, v___y_571_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_583_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
v_a_575_ = lean_ctor_get(v___x_573_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_583_ == 0)
{
v___x_577_ = v___x_573_;
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_inc(v_a_574_);
lean_dec(v___x_573_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_a_574_);
lean_ctor_set(v___x_579_, 1, v___y_570_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_579_);
v___x_581_ = v___x_577_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_a_575_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
else
{
lean_object* v_a_584_; lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v___y_570_);
v_a_584_ = lean_ctor_get(v___x_573_, 0);
v_a_585_ = lean_ctor_get(v___x_573_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_573_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_inc(v_a_584_);
lean_dec(v___x_573_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_584_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8___boxed(lean_object* v_x_615_, lean_object* v_bi_616_, lean_object* v_t_617_, lean_object* v_b_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v_bi_boxed_623_; uint8_t v___y_26106__boxed_624_; lean_object* v_res_625_; 
v_bi_boxed_623_ = lean_unbox(v_bi_616_);
v___y_26106__boxed_624_ = lean_unbox(v___y_620_);
v_res_625_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_x_615_, v_bi_boxed_623_, v_t_617_, v_b_618_, v___y_619_, v___y_26106__boxed_624_, v___y_621_, v___y_622_);
lean_dec_ref(v___y_621_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(lean_object* v_x_626_, uint8_t v_bi_627_, lean_object* v_t_628_, lean_object* v_b_629_, lean_object* v___y_630_, uint8_t v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v___y_635_; lean_object* v___y_636_; 
if (v___y_631_ == 0)
{
v___y_635_ = v___y_630_;
v___y_636_ = v___y_633_;
goto v___jp_634_;
}
else
{
lean_object* v___x_658_; 
lean_inc_ref(v_t_628_);
v___x_658_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_628_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_660_; 
v_a_659_ = lean_ctor_get(v___x_658_, 1);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 2);
lean_inc_ref(v_b_629_);
v___x_660_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_629_, v___y_631_, v___y_632_, v_a_659_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; 
v_a_661_ = lean_ctor_get(v___x_660_, 1);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_660_, 2);
v___y_635_ = v___y_630_;
v___y_636_ = v_a_661_;
goto v___jp_634_;
}
else
{
lean_object* v_a_662_; lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec_ref(v___y_630_);
lean_dec_ref(v_b_629_);
lean_dec_ref(v_t_628_);
lean_dec(v_x_626_);
v_a_662_ = lean_ctor_get(v___x_660_, 0);
v_a_663_ = lean_ctor_get(v___x_660_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_660_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_inc(v_a_662_);
lean_dec(v___x_660_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_662_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
else
{
lean_object* v_a_671_; lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec_ref(v___y_630_);
lean_dec_ref(v_b_629_);
lean_dec_ref(v_t_628_);
lean_dec(v_x_626_);
v_a_671_ = lean_ctor_get(v___x_658_, 0);
v_a_672_ = lean_ctor_get(v___x_658_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_658_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_inc(v_a_671_);
lean_dec(v___x_658_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_671_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_a_672_);
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
v___jp_634_:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = l_Lean_Expr_lam___override(v_x_626_, v_t_628_, v_b_629_, v_bi_627_);
v___x_638_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_637_, v___y_636_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_648_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_a_640_ = lean_ctor_get(v___x_638_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_648_ == 0)
{
v___x_642_ = v___x_638_;
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v_a_639_);
lean_ctor_set(v___x_644_, 1, v___y_635_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_644_);
v___x_646_ = v___x_642_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_a_640_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
else
{
lean_object* v_a_649_; lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref(v___y_635_);
v_a_649_ = lean_ctor_get(v___x_638_, 0);
v_a_650_ = lean_ctor_get(v___x_638_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_638_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_inc(v_a_649_);
lean_dec(v___x_638_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_649_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7___boxed(lean_object* v_x_680_, lean_object* v_bi_681_, lean_object* v_t_682_, lean_object* v_b_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
uint8_t v_bi_boxed_688_; uint8_t v___y_26212__boxed_689_; lean_object* v_res_690_; 
v_bi_boxed_688_ = lean_unbox(v_bi_681_);
v___y_26212__boxed_689_ = lean_unbox(v___y_685_);
v_res_690_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_x_680_, v_bi_boxed_688_, v_t_682_, v_b_683_, v___y_684_, v___y_26212__boxed_689_, v___y_686_, v___y_687_);
lean_dec_ref(v___y_686_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(lean_object* v_x_691_, lean_object* v_t_692_, lean_object* v_v_693_, lean_object* v_b_694_, uint8_t v_nondep_695_, lean_object* v___y_696_, uint8_t v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___y_701_; lean_object* v___y_702_; 
if (v___y_697_ == 0)
{
v___y_701_ = v___y_696_;
v___y_702_ = v___y_699_;
goto v___jp_700_;
}
else
{
lean_object* v___x_724_; 
lean_inc_ref(v_t_692_);
v___x_724_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_692_, v___y_697_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_726_; 
v_a_725_ = lean_ctor_get(v___x_724_, 1);
lean_inc(v_a_725_);
lean_dec_ref_known(v___x_724_, 2);
lean_inc_ref(v_v_693_);
v___x_726_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_693_, v___y_697_, v___y_698_, v_a_725_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_728_; 
v_a_727_ = lean_ctor_get(v___x_726_, 1);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 2);
lean_inc_ref(v_b_694_);
v___x_728_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_694_, v___y_697_, v___y_698_, v_a_727_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; 
v_a_729_ = lean_ctor_get(v___x_728_, 1);
lean_inc(v_a_729_);
lean_dec_ref_known(v___x_728_, 2);
v___y_701_ = v___y_696_;
v___y_702_ = v_a_729_;
goto v___jp_700_;
}
else
{
lean_object* v_a_730_; lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v___y_696_);
lean_dec_ref(v_b_694_);
lean_dec_ref(v_v_693_);
lean_dec_ref(v_t_692_);
lean_dec(v_x_691_);
v_a_730_ = lean_ctor_get(v___x_728_, 0);
v_a_731_ = lean_ctor_get(v___x_728_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_728_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_inc(v_a_730_);
lean_dec(v___x_728_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_730_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
lean_object* v_a_739_; lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref(v___y_696_);
lean_dec_ref(v_b_694_);
lean_dec_ref(v_v_693_);
lean_dec_ref(v_t_692_);
lean_dec(v_x_691_);
v_a_739_ = lean_ctor_get(v___x_726_, 0);
v_a_740_ = lean_ctor_get(v___x_726_, 1);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_726_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_inc(v_a_739_);
lean_dec(v___x_726_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_739_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec_ref(v___y_696_);
lean_dec_ref(v_b_694_);
lean_dec_ref(v_v_693_);
lean_dec_ref(v_t_692_);
lean_dec(v_x_691_);
v_a_748_ = lean_ctor_get(v___x_724_, 0);
v_a_749_ = lean_ctor_get(v___x_724_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_724_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_inc(v_a_748_);
lean_dec(v___x_724_);
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
v___jp_700_:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = l_Lean_Expr_letE___override(v_x_691_, v_t_692_, v_v_693_, v_b_694_, v_nondep_695_);
v___x_704_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_703_, v___y_702_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_714_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
v_a_706_ = lean_ctor_get(v___x_704_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_714_ == 0)
{
v___x_708_ = v___x_704_;
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_inc(v_a_705_);
lean_dec(v___x_704_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_a_705_);
lean_ctor_set(v___x_710_, 1, v___y_701_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_710_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_a_706_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
else
{
lean_object* v_a_715_; lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec_ref(v___y_701_);
v_a_715_ = lean_ctor_get(v___x_704_, 0);
v_a_716_ = lean_ctor_get(v___x_704_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_704_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_inc(v_a_715_);
lean_dec(v___x_704_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_715_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9___boxed(lean_object* v_x_757_, lean_object* v_t_758_, lean_object* v_v_759_, lean_object* v_b_760_, lean_object* v_nondep_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
uint8_t v_nondep_boxed_766_; uint8_t v___y_26318__boxed_767_; lean_object* v_res_768_; 
v_nondep_boxed_766_ = lean_unbox(v_nondep_761_);
v___y_26318__boxed_767_ = lean_unbox(v___y_763_);
v_res_768_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_x_757_, v_t_758_, v_v_759_, v_b_760_, v_nondep_boxed_766_, v___y_762_, v___y_26318__boxed_767_, v___y_764_, v___y_765_);
lean_dec_ref(v___y_764_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(lean_object* v_f_769_, lean_object* v_a_770_, lean_object* v___y_771_, uint8_t v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v___y_776_; lean_object* v___y_777_; 
if (v___y_772_ == 0)
{
v___y_776_ = v___y_771_;
v___y_777_ = v___y_774_;
goto v___jp_775_;
}
else
{
lean_object* v___x_799_; 
lean_inc_ref(v_f_769_);
v___x_799_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_769_, v___y_772_, v___y_773_, v___y_774_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_801_; 
v_a_800_ = lean_ctor_get(v___x_799_, 1);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 2);
lean_inc_ref(v_a_770_);
v___x_801_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_770_, v___y_772_, v___y_773_, v_a_800_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; 
v_a_802_ = lean_ctor_get(v___x_801_, 1);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_801_, 2);
v___y_776_ = v___y_771_;
v___y_777_ = v_a_802_;
goto v___jp_775_;
}
else
{
lean_object* v_a_803_; lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref(v___y_771_);
lean_dec_ref(v_a_770_);
lean_dec_ref(v_f_769_);
v_a_803_ = lean_ctor_get(v___x_801_, 0);
v_a_804_ = lean_ctor_get(v___x_801_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_801_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_inc(v_a_803_);
lean_dec(v___x_801_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_803_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec_ref(v___y_771_);
lean_dec_ref(v_a_770_);
lean_dec_ref(v_f_769_);
v_a_812_ = lean_ctor_get(v___x_799_, 0);
v_a_813_ = lean_ctor_get(v___x_799_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_799_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_inc(v_a_812_);
lean_dec(v___x_799_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_812_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
v___jp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = l_Lean_Expr_app___override(v_f_769_, v_a_770_);
v___x_779_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_778_, v___y_777_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_789_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_a_781_ = lean_ctor_get(v___x_779_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_789_ == 0)
{
v___x_783_ = v___x_779_;
v_isShared_784_ = v_isSharedCheck_789_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_789_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v_a_780_);
lean_ctor_set(v___x_785_, 1, v___y_776_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_785_);
v___x_787_ = v___x_783_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_a_781_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
else
{
lean_object* v_a_790_; lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref(v___y_776_);
v_a_790_ = lean_ctor_get(v___x_779_, 0);
v_a_791_ = lean_ctor_get(v___x_779_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_779_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_inc(v_a_790_);
lean_dec(v___x_779_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_790_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6___boxed(lean_object* v_f_821_, lean_object* v_a_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
uint8_t v___y_26447__boxed_827_; lean_object* v_res_828_; 
v___y_26447__boxed_827_ = lean_unbox(v___y_824_);
v_res_828_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_f_821_, v_a_822_, v___y_823_, v___y_26447__boxed_827_, v___y_825_, v___y_826_);
lean_dec_ref(v___y_825_);
return v_res_828_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_832_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__2));
v___x_833_ = lean_unsigned_to_nat(67u);
v___x_834_ = lean_unsigned_to_nat(35u);
v___x_835_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__1));
v___x_836_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__0));
v___x_837_ = l_mkPanicMessageWithDecl(v___x_836_, v___x_835_, v___x_834_, v___x_833_, v___x_832_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(lean_object* v_minIndex_838_, lean_object* v___x_839_, lean_object* v___x_840_, lean_object* v_start_841_, lean_object* v_xs_842_, lean_object* v___x_843_, lean_object* v_e_844_, lean_object* v_offset_845_, lean_object* v_a_846_, uint8_t v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
switch(lean_obj_tag(v_e_844_))
{
case 5:
{
lean_object* v_fn_850_; lean_object* v_arg_851_; lean_object* v___x_852_; 
v_fn_850_ = lean_ctor_get(v_e_844_, 0);
v_arg_851_ = lean_ctor_get(v_e_844_, 1);
lean_inc(v_offset_845_);
lean_inc_ref(v_fn_850_);
lean_inc_ref(v___x_839_);
v___x_852_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_838_, v___x_839_, v___x_840_, v_start_841_, v_xs_842_, v___x_843_, v_fn_850_, v_offset_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v_a_854_; lean_object* v_fst_855_; lean_object* v_snd_856_; lean_object* v___x_857_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
v_a_854_ = lean_ctor_get(v___x_852_, 1);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_852_, 2);
v_fst_855_ = lean_ctor_get(v_a_853_, 0);
lean_inc(v_fst_855_);
v_snd_856_ = lean_ctor_get(v_a_853_, 1);
lean_inc(v_snd_856_);
lean_dec(v_a_853_);
lean_inc_ref(v_arg_851_);
v___x_857_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_838_, v___x_839_, v___x_840_, v_start_841_, v_xs_842_, v___x_843_, v_arg_851_, v_offset_845_, v_snd_856_, v_a_847_, v_a_848_, v_a_854_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_880_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_a_859_ = lean_ctor_get(v___x_857_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_880_ == 0)
{
v___x_861_ = v___x_857_;
v_isShared_862_ = v_isSharedCheck_880_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_880_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_fst_863_; lean_object* v_snd_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_879_; 
v_fst_863_ = lean_ctor_get(v_a_858_, 0);
v_snd_864_ = lean_ctor_get(v_a_858_, 1);
v_isSharedCheck_879_ = !lean_is_exclusive(v_a_858_);
if (v_isSharedCheck_879_ == 0)
{
v___x_866_ = v_a_858_;
v_isShared_867_ = v_isSharedCheck_879_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_snd_864_);
lean_inc(v_fst_863_);
lean_dec(v_a_858_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_879_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint8_t v___y_869_; uint8_t v___x_877_; 
v___x_877_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_850_, v_fst_855_);
if (v___x_877_ == 0)
{
v___y_869_ = v___x_877_;
goto v___jp_868_;
}
else
{
uint8_t v___x_878_; 
v___x_878_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_851_, v_fst_863_);
v___y_869_ = v___x_878_;
goto v___jp_868_;
}
v___jp_868_:
{
if (v___y_869_ == 0)
{
lean_object* v___x_870_; 
lean_del_object(v___x_866_);
lean_del_object(v___x_861_);
lean_dec_ref_known(v_e_844_, 2);
v___x_870_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_fst_855_, v_fst_863_, v_snd_864_, v_a_847_, v_a_848_, v_a_859_);
return v___x_870_;
}
else
{
lean_object* v___x_872_; 
lean_dec(v_fst_863_);
lean_dec(v_fst_855_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v_e_844_);
v___x_872_ = v___x_866_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_e_844_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_snd_864_);
v___x_872_ = v_reuseFailAlloc_876_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_874_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_872_);
v___x_874_ = v___x_861_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_a_859_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_855_);
lean_dec_ref_known(v_e_844_, 2);
return v___x_857_;
}
}
else
{
lean_dec_ref_known(v_e_844_, 2);
lean_dec(v_offset_845_);
lean_dec_ref(v___x_839_);
return v___x_852_;
}
}
case 6:
{
lean_object* v_binderName_881_; lean_object* v_binderType_882_; lean_object* v_body_883_; uint8_t v_binderInfo_884_; lean_object* v___x_885_; 
v_binderName_881_ = lean_ctor_get(v_e_844_, 0);
v_binderType_882_ = lean_ctor_get(v_e_844_, 1);
v_body_883_ = lean_ctor_get(v_e_844_, 2);
v_binderInfo_884_ = lean_ctor_get_uint8(v_e_844_, sizeof(void*)*3 + 8);
lean_inc(v_offset_845_);
lean_inc_ref(v_binderType_882_);
lean_inc_ref(v___x_839_);
v___x_885_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_838_, v___x_839_, v___x_840_, v_start_841_, v_xs_842_, v___x_843_, v_binderType_882_, v_offset_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v_a_887_; lean_object* v_fst_888_; lean_object* v_snd_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
v_a_887_ = lean_ctor_get(v___x_885_, 1);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_885_, 2);
v_fst_888_ = lean_ctor_get(v_a_886_, 0);
lean_inc(v_fst_888_);
v_snd_889_ = lean_ctor_get(v_a_886_, 1);
lean_inc(v_snd_889_);
lean_dec(v_a_886_);
v___x_890_ = lean_unsigned_to_nat(1u);
v___x_891_ = lean_nat_add(v_offset_845_, v___x_890_);
lean_dec(v_offset_845_);
lean_inc_ref(v_body_883_);
v___x_892_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_838_, v___x_839_, v___x_840_, v_start_841_, v_xs_842_, v___x_843_, v_body_883_, v___x_891_, v_snd_889_, v_a_847_, v_a_848_, v_a_887_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_915_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_a_894_ = lean_ctor_get(v___x_892_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_915_ == 0)
{
v___x_896_ = v___x_892_;
v_isShared_897_ = v_isSharedCheck_915_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_915_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_fst_898_; lean_object* v_snd_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_914_; 
v_fst_898_ = lean_ctor_get(v_a_893_, 0);
v_snd_899_ = lean_ctor_get(v_a_893_, 1);
v_isSharedCheck_914_ = !lean_is_exclusive(v_a_893_);
if (v_isSharedCheck_914_ == 0)
{
v___x_901_ = v_a_893_;
v_isShared_902_ = v_isSharedCheck_914_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_snd_899_);
lean_inc(v_fst_898_);
lean_dec(v_a_893_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_914_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
uint8_t v___y_904_; uint8_t v___x_912_; 
v___x_912_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_882_, v_fst_888_);
if (v___x_912_ == 0)
{
v___y_904_ = v___x_912_;
goto v___jp_903_;
}
else
{
uint8_t v___x_913_; 
v___x_913_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_883_, v_fst_898_);
v___y_904_ = v___x_913_;
goto v___jp_903_;
}
v___jp_903_:
{
if (v___y_904_ == 0)
{
lean_object* v___x_905_; 
lean_inc(v_binderName_881_);
lean_del_object(v___x_901_);
lean_del_object(v___x_896_);
lean_dec_ref_known(v_e_844_, 3);
v___x_905_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_binderName_881_, v_binderInfo_884_, v_fst_888_, v_fst_898_, v_snd_899_, v_a_847_, v_a_848_, v_a_894_);
return v___x_905_;
}
else
{
lean_object* v___x_907_; 
lean_dec(v_fst_898_);
lean_dec(v_fst_888_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v_e_844_);
v___x_907_ = v___x_901_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_e_844_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_snd_899_);
v___x_907_ = v_reuseFailAlloc_911_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_909_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_907_);
v___x_909_ = v___x_896_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_a_894_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_888_);
lean_dec_ref_known(v_e_844_, 3);
return v___x_892_;
}
}
else
{
lean_dec_ref_known(v_e_844_, 3);
lean_dec(v_offset_845_);
lean_dec_ref(v___x_839_);
return v___x_885_;
}
}
case 7:
{
lean_object* v_binderName_916_; lean_object* v_binderType_917_; lean_object* v_body_918_; uint8_t v_binderInfo_919_; lean_object* v___x_920_; 
v_binderName_916_ = lean_ctor_get(v_e_844_, 0);
v_binderType_917_ = lean_ctor_get(v_e_844_, 1);
v_body_918_ = lean_ctor_get(v_e_844_, 2);
v_binderInfo_919_ = lean_ctor_get_uint8(v_e_844_, sizeof(void*)*3 + 8);
lean_inc(v_offset_845_);
lean_inc_ref(v_binderType_917_);
lean_inc_ref(v___x_839_);
v___x_920_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_838_, v___x_839_, v___x_840_, v_start_841_, v_xs_842_, v___x_843_, v_binderType_917_, v_offset_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v_a_922_; lean_object* v_fst_923_; lean_object* v_snd_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
v_a_922_ = lean_ctor_get(v___x_920_, 1);
lean_inc(v_a_922_);
lean_dec_ref_known(v___x_920_, 2);
v_fst_923_ = lean_ctor_get(v_a_921_, 0);
lean_inc(v_fst_923_);
v_snd_924_ = lean_ctor_get(v_a_921_, 1);
lean_inc(v_snd_924_);
lean_dec(v_a_921_);
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_nat_add(v_offset_845_, v___x_925_);
lean_dec(v_offset_845_);
lean_inc_ref(v_body_918_);
v___x_927_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_838_, v___x_839_, v___x_840_, v_start_841_, v_xs_842_, v___x_843_, v_body_918_, v___x_926_, v_snd_924_, v_a_847_, v_a_848_, v_a_922_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_950_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
v_a_929_ = lean_ctor_get(v___x_927_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_950_ == 0)
{
v___x_931_ = v___x_927_;
v_isShared_932_ = v_isSharedCheck_950_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_inc(v_a_928_);
lean_dec(v___x_927_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_950_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_fst_933_; lean_object* v_snd_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_949_; 
v_fst_933_ = lean_ctor_get(v_a_928_, 0);
v_snd_934_ = lean_ctor_get(v_a_928_, 1);
v_isSharedCheck_949_ = !lean_is_exclusive(v_a_928_);
if (v_isSharedCheck_949_ == 0)
{
v___x_936_ = v_a_928_;
v_isShared_937_ = v_isSharedCheck_949_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_snd_934_);
lean_inc(v_fst_933_);
lean_dec(v_a_928_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_949_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
uint8_t v___y_939_; uint8_t v___x_947_; 
v___x_947_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_917_, v_fst_923_);
if (v___x_947_ == 0)
{
v___y_939_ = v___x_947_;
goto v___jp_938_;
}
else
{
uint8_t v___x_948_; 
v___x_948_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_918_, v_fst_933_);
v___y_939_ = v___x_948_;
goto v___jp_938_;
}
v___jp_938_:
{
if (v___y_939_ == 0)
{
lean_object* v___x_940_; 
lean_inc(v_binderName_916_);
lean_del_object(v___x_936_);
lean_del_object(v___x_931_);
lean_dec_ref_known(v_e_844_, 3);
v___x_940_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_binderName_916_, v_binderInfo_919_, v_fst_923_, v_fst_933_, v_snd_934_, v_a_847_, v_a_848_, v_a_929_);
return v___x_940_;
}
else
{
lean_object* v___x_942_; 
lean_dec(v_fst_933_);
lean_dec(v_fst_923_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v_e_844_);
v___x_942_ = v___x_936_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_e_844_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_snd_934_);
v___x_942_ = v_reuseFailAlloc_946_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_944_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_942_);
v___x_944_ = v___x_931_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_a_929_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_923_);
lean_dec_ref_known(v_e_844_, 3);
return v___x_927_;
}
}
else
{
lean_dec_ref_known(v_e_844_, 3);
lean_dec(v_offset_845_);
lean_dec_ref(v___x_839_);
return v___x_920_;
}
}
case 8:
{
lean_object* v_declName_951_; lean_object* v_type_952_; lean_object* v_value_953_; lean_object* v_body_954_; uint8_t v_nondep_955_; lean_object* v___x_956_; 
v_declName_951_ = lean_ctor_get(v_e_844_, 0);
v_type_952_ = lean_ctor_get(v_e_844_, 1);
v_value_953_ = lean_ctor_get(v_e_844_, 2);
v_body_954_ = lean_ctor_get(v_e_844_, 3);
v_nondep_955_ = lean_ctor_get_uint8(v_e_844_, sizeof(void*)*4 + 8);
lean_inc(v_offset_845_);
lean_inc_ref(v_type_952_);
lean_inc_ref(v___x_839_);
v___x_956_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_838_, v___x_839_, v___x_840_, v_start_841_, v_xs_842_, v___x_843_, v_type_952_, v_offset_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v_a_958_; lean_object* v_fst_959_; lean_object* v_snd_960_; lean_object* v___x_961_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
v_a_958_ = lean_ctor_get(v___x_956_, 1);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_956_, 2);
v_fst_959_ = lean_ctor_get(v_a_957_, 0);
lean_inc(v_fst_959_);
v_snd_960_ = lean_ctor_get(v_a_957_, 1);
lean_inc(v_snd_960_);
lean_dec(v_a_957_);
lean_inc(v_offset_845_);
lean_inc_ref(v_value_953_);
lean_inc_ref(v___x_839_);
v___x_961_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_838_, v___x_839_, v___x_840_, v_start_841_, v_xs_842_, v___x_843_, v_value_953_, v_offset_845_, v_snd_960_, v_a_847_, v_a_848_, v_a_958_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v_a_963_; lean_object* v_fst_964_; lean_object* v_snd_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
v_a_963_ = lean_ctor_get(v___x_961_, 1);
lean_inc(v_a_963_);
lean_dec_ref_known(v___x_961_, 2);
v_fst_964_ = lean_ctor_get(v_a_962_, 0);
lean_inc(v_fst_964_);
v_snd_965_ = lean_ctor_get(v_a_962_, 1);
lean_inc(v_snd_965_);
lean_dec(v_a_962_);
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = lean_nat_add(v_offset_845_, v___x_966_);
lean_dec(v_offset_845_);
lean_inc_ref(v_body_954_);
v___x_968_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_838_, v___x_839_, v___x_840_, v_start_841_, v_xs_842_, v___x_843_, v_body_954_, v___x_967_, v_snd_965_, v_a_847_, v_a_848_, v_a_963_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_993_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_a_970_ = lean_ctor_get(v___x_968_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_993_ == 0)
{
v___x_972_ = v___x_968_;
v_isShared_973_ = v_isSharedCheck_993_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_993_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v_fst_974_; lean_object* v_snd_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_992_; 
v_fst_974_ = lean_ctor_get(v_a_969_, 0);
v_snd_975_ = lean_ctor_get(v_a_969_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v_a_969_);
if (v_isSharedCheck_992_ == 0)
{
v___x_977_ = v_a_969_;
v_isShared_978_ = v_isSharedCheck_992_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_snd_975_);
lean_inc(v_fst_974_);
lean_dec(v_a_969_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_992_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
uint8_t v___y_980_; uint8_t v___x_990_; 
v___x_990_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_952_, v_fst_959_);
if (v___x_990_ == 0)
{
v___y_980_ = v___x_990_;
goto v___jp_979_;
}
else
{
uint8_t v___x_991_; 
v___x_991_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_953_, v_fst_964_);
v___y_980_ = v___x_991_;
goto v___jp_979_;
}
v___jp_979_:
{
if (v___y_980_ == 0)
{
lean_object* v___x_981_; 
lean_inc(v_declName_951_);
lean_del_object(v___x_977_);
lean_del_object(v___x_972_);
lean_dec_ref_known(v_e_844_, 4);
v___x_981_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_951_, v_fst_959_, v_fst_964_, v_fst_974_, v_nondep_955_, v_snd_975_, v_a_847_, v_a_848_, v_a_970_);
return v___x_981_;
}
else
{
uint8_t v___x_982_; 
v___x_982_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_954_, v_fst_974_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; 
lean_inc(v_declName_951_);
lean_del_object(v___x_977_);
lean_del_object(v___x_972_);
lean_dec_ref_known(v_e_844_, 4);
v___x_983_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_951_, v_fst_959_, v_fst_964_, v_fst_974_, v_nondep_955_, v_snd_975_, v_a_847_, v_a_848_, v_a_970_);
return v___x_983_;
}
else
{
lean_object* v___x_985_; 
lean_dec(v_fst_974_);
lean_dec(v_fst_964_);
lean_dec(v_fst_959_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v_e_844_);
v___x_985_ = v___x_977_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_e_844_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_snd_975_);
v___x_985_ = v_reuseFailAlloc_989_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_987_; 
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_985_);
v___x_987_ = v___x_972_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_a_970_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
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
lean_dec(v_fst_964_);
lean_dec(v_fst_959_);
lean_dec_ref_known(v_e_844_, 4);
return v___x_968_;
}
}
else
{
lean_dec(v_fst_959_);
lean_dec_ref_known(v_e_844_, 4);
lean_dec(v_offset_845_);
lean_dec_ref(v___x_839_);
return v___x_961_;
}
}
else
{
lean_dec_ref_known(v_e_844_, 4);
lean_dec(v_offset_845_);
lean_dec_ref(v___x_839_);
return v___x_956_;
}
}
case 10:
{
lean_object* v_data_994_; lean_object* v_expr_995_; lean_object* v___x_996_; 
v_data_994_ = lean_ctor_get(v_e_844_, 0);
v_expr_995_ = lean_ctor_get(v_e_844_, 1);
lean_inc_ref(v_expr_995_);
v___x_996_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_838_, v___x_839_, v___x_840_, v_start_841_, v_xs_842_, v___x_843_, v_expr_995_, v_offset_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1016_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_a_998_ = lean_ctor_get(v___x_996_, 1);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1000_ = v___x_996_;
v_isShared_1001_ = v_isSharedCheck_1016_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1016_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v_fst_1002_; lean_object* v_snd_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1015_; 
v_fst_1002_ = lean_ctor_get(v_a_997_, 0);
v_snd_1003_ = lean_ctor_get(v_a_997_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_a_997_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1005_ = v_a_997_;
v_isShared_1006_ = v_isSharedCheck_1015_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_snd_1003_);
lean_inc(v_fst_1002_);
lean_dec(v_a_997_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1015_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
uint8_t v___x_1007_; 
v___x_1007_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_995_, v_fst_1002_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
lean_inc(v_data_994_);
lean_del_object(v___x_1005_);
lean_del_object(v___x_1000_);
lean_dec_ref_known(v_e_844_, 2);
v___x_1008_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(v_data_994_, v_fst_1002_, v_snd_1003_, v_a_847_, v_a_848_, v_a_998_);
return v___x_1008_;
}
else
{
lean_object* v___x_1010_; 
lean_dec(v_fst_1002_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v_e_844_);
v___x_1010_ = v___x_1005_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_e_844_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_snd_1003_);
v___x_1010_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1012_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1010_);
v___x_1012_ = v___x_1000_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_a_998_);
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
else
{
lean_dec_ref_known(v_e_844_, 2);
return v___x_996_;
}
}
case 11:
{
lean_object* v_typeName_1017_; lean_object* v_idx_1018_; lean_object* v_struct_1019_; lean_object* v___x_1020_; 
v_typeName_1017_ = lean_ctor_get(v_e_844_, 0);
v_idx_1018_ = lean_ctor_get(v_e_844_, 1);
v_struct_1019_ = lean_ctor_get(v_e_844_, 2);
lean_inc_ref(v_struct_1019_);
v___x_1020_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_838_, v___x_839_, v___x_840_, v_start_841_, v_xs_842_, v___x_843_, v_struct_1019_, v_offset_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1040_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_a_1022_ = lean_ctor_get(v___x_1020_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1024_ = v___x_1020_;
v_isShared_1025_ = v_isSharedCheck_1040_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1040_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v_fst_1026_; lean_object* v_snd_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1039_; 
v_fst_1026_ = lean_ctor_get(v_a_1021_, 0);
v_snd_1027_ = lean_ctor_get(v_a_1021_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_a_1021_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1029_ = v_a_1021_;
v_isShared_1030_ = v_isSharedCheck_1039_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_snd_1027_);
lean_inc(v_fst_1026_);
lean_dec(v_a_1021_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1039_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
uint8_t v___x_1031_; 
v___x_1031_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1019_, v_fst_1026_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; 
lean_inc(v_idx_1018_);
lean_inc(v_typeName_1017_);
lean_del_object(v___x_1029_);
lean_del_object(v___x_1024_);
lean_dec_ref_known(v_e_844_, 3);
v___x_1032_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(v_typeName_1017_, v_idx_1018_, v_fst_1026_, v_snd_1027_, v_a_847_, v_a_848_, v_a_1022_);
return v___x_1032_;
}
else
{
lean_object* v___x_1034_; 
lean_dec(v_fst_1026_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v_e_844_);
v___x_1034_ = v___x_1029_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_e_844_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_snd_1027_);
v___x_1034_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1036_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1034_);
v___x_1036_ = v___x_1024_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_a_1022_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_844_, 3);
return v___x_1020_;
}
}
default: 
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_dec(v_offset_845_);
lean_dec_ref(v_e_844_);
lean_dec_ref(v___x_839_);
v___x_1041_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3);
v___x_1042_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(v___x_1041_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
return v___x_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(lean_object* v_minIndex_1043_, lean_object* v___x_1044_, lean_object* v___x_1045_, lean_object* v_start_1046_, lean_object* v_xs_1047_, lean_object* v___x_1048_, lean_object* v_e_1049_, lean_object* v_offset_1050_, lean_object* v_a_1051_, uint8_t v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_key_1055_; lean_object* v_a_1057_; lean_object* v___y_1071_; lean_object* v___y_1076_; lean_object* v___x_1081_; 
lean_inc(v_offset_1050_);
lean_inc_ref(v_e_1049_);
v_key_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1055_, 0, v_e_1049_);
lean_ctor_set(v_key_1055_, 1, v_offset_1050_);
v___x_1081_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_a_1051_, v_key_1055_);
if (lean_obj_tag(v___x_1081_) == 1)
{
lean_object* v_val_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec_ref_known(v_key_1055_, 2);
lean_dec(v_offset_1050_);
lean_dec_ref(v_e_1049_);
lean_dec_ref(v___x_1044_);
v_val_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_val_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v_val_1082_);
lean_ctor_set(v___x_1083_, 1, v_a_1051_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_a_1054_);
return v___x_1084_;
}
else
{
lean_dec(v___x_1081_);
switch(lean_obj_tag(v_e_1049_))
{
case 1:
{
lean_object* v_fvarId_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec_ref(v___x_1044_);
v_fvarId_1085_ = lean_ctor_get(v_e_1049_, 0);
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = lean_unsigned_to_nat(1u);
v___x_1088_ = lean_nat_sub(v___x_1045_, v___x_1087_);
v___x_1089_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_1046_, v_xs_1047_, v_fvarId_1085_, v___x_1086_, v___x_1088_);
if (lean_obj_tag(v___x_1089_) == 1)
{
lean_object* v_val_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_dec_ref_known(v_e_1049_, 1);
v_val_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_val_1090_);
lean_dec_ref_known(v___x_1089_, 1);
v___x_1091_ = lean_nat_add(v_offset_1050_, v_val_1090_);
lean_dec(v_val_1090_);
lean_dec(v_offset_1050_);
v___x_1092_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v___x_1091_, v_a_1054_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v_a_1094_; lean_object* v___x_1095_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
v_a_1094_ = lean_ctor_get(v___x_1092_, 1);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1092_, 2);
v___x_1095_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1055_, v_a_1093_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1094_);
return v___x_1095_;
}
else
{
lean_object* v_a_1096_; lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref_known(v_key_1055_, 2);
lean_dec_ref(v_a_1051_);
v_a_1096_ = lean_ctor_get(v___x_1092_, 0);
v_a_1097_ = lean_ctor_get(v___x_1092_, 1);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1092_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_inc(v_a_1096_);
lean_dec(v___x_1092_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1096_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
else
{
lean_object* v___x_1105_; 
lean_dec(v___x_1089_);
lean_dec(v_offset_1050_);
v___x_1105_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1055_, v_e_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1105_;
}
}
case 9:
{
lean_object* v___x_1106_; 
lean_dec(v_offset_1050_);
lean_dec_ref(v___x_1044_);
v___x_1106_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1055_, v_e_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1106_;
}
case 2:
{
lean_object* v___x_1107_; 
lean_dec(v_offset_1050_);
lean_dec_ref(v___x_1044_);
v___x_1107_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1055_, v_e_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1107_;
}
case 0:
{
lean_object* v___x_1108_; 
lean_dec(v_offset_1050_);
lean_dec_ref(v___x_1044_);
v___x_1108_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1055_, v_e_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1108_;
}
case 4:
{
lean_object* v___x_1109_; 
lean_dec(v_offset_1050_);
lean_dec_ref(v___x_1044_);
v___x_1109_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1055_, v_e_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1109_;
}
case 3:
{
lean_object* v___x_1110_; 
lean_dec(v_offset_1050_);
lean_dec_ref(v___x_1044_);
v___x_1110_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1055_, v_e_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1110_;
}
default: 
{
uint8_t v___x_1111_; 
v___x_1111_ = l_Lean_Expr_hasFVar(v_e_1049_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
lean_dec(v_offset_1050_);
lean_dec_ref(v___x_1044_);
v___x_1112_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1055_, v_e_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1112_;
}
else
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v___x_1048_, v_e_1049_);
if (lean_obj_tag(v___x_1113_) == 1)
{
lean_object* v_val_1114_; 
v_val_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_val_1114_);
lean_dec_ref_known(v___x_1113_, 1);
if (lean_obj_tag(v_val_1114_) == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1116_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v___x_1115_);
v___y_1076_ = v___x_1116_;
goto v___jp_1075_;
}
else
{
lean_object* v_val_1117_; 
v_val_1117_ = lean_ctor_get(v_val_1114_, 0);
lean_inc(v_val_1117_);
lean_dec_ref_known(v_val_1114_, 1);
v___y_1076_ = v_val_1117_;
goto v___jp_1075_;
}
}
else
{
lean_dec(v___x_1113_);
v_a_1057_ = v_a_1054_;
goto v___jp_1056_;
}
}
}
}
}
v___jp_1056_:
{
switch(lean_obj_tag(v_e_1049_))
{
case 9:
{
lean_object* v___x_1058_; 
lean_dec(v_offset_1050_);
lean_dec_ref(v___x_1044_);
v___x_1058_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1055_, v_e_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1057_);
return v___x_1058_;
}
case 2:
{
lean_object* v___x_1059_; 
lean_dec(v_offset_1050_);
lean_dec_ref(v___x_1044_);
v___x_1059_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1055_, v_e_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1057_);
return v___x_1059_;
}
case 0:
{
lean_object* v___x_1060_; 
lean_dec(v_offset_1050_);
lean_dec_ref(v___x_1044_);
v___x_1060_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1055_, v_e_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1057_);
return v___x_1060_;
}
case 1:
{
lean_object* v___x_1061_; 
lean_dec(v_offset_1050_);
lean_dec_ref(v___x_1044_);
v___x_1061_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1055_, v_e_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1057_);
return v___x_1061_;
}
case 4:
{
lean_object* v___x_1062_; 
lean_dec(v_offset_1050_);
lean_dec_ref(v___x_1044_);
v___x_1062_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1055_, v_e_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1057_);
return v___x_1062_;
}
case 3:
{
lean_object* v___x_1063_; 
lean_dec(v_offset_1050_);
lean_dec_ref(v___x_1044_);
v___x_1063_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1055_, v_e_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1057_);
return v___x_1063_;
}
default: 
{
lean_object* v___x_1064_; 
v___x_1064_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v_minIndex_1043_, v___x_1044_, v___x_1045_, v_start_1046_, v_xs_1047_, v___x_1048_, v_e_1049_, v_offset_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1057_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v_a_1066_; lean_object* v_fst_1067_; lean_object* v_snd_1068_; lean_object* v___x_1069_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
v_a_1066_ = lean_ctor_get(v___x_1064_, 1);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1064_, 2);
v_fst_1067_ = lean_ctor_get(v_a_1065_, 0);
lean_inc(v_fst_1067_);
v_snd_1068_ = lean_ctor_get(v_a_1065_, 1);
lean_inc(v_snd_1068_);
lean_dec(v_a_1065_);
v___x_1069_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1055_, v_fst_1067_, v_snd_1068_, v_a_1052_, v_a_1053_, v_a_1066_);
return v___x_1069_;
}
else
{
lean_dec_ref_known(v_key_1055_, 2);
return v___x_1064_;
}
}
}
}
v___jp_1070_:
{
lean_object* v_maxIndex_1072_; uint8_t v___x_1073_; 
v_maxIndex_1072_ = l_Lean_LocalDecl_index(v___y_1071_);
lean_dec_ref(v___y_1071_);
v___x_1073_ = lean_nat_dec_lt(v_maxIndex_1072_, v_minIndex_1043_);
lean_dec(v_maxIndex_1072_);
if (v___x_1073_ == 0)
{
v_a_1057_ = v_a_1054_;
goto v___jp_1056_;
}
else
{
lean_object* v___x_1074_; 
lean_dec(v_offset_1050_);
lean_dec_ref(v___x_1044_);
v___x_1074_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1055_, v_e_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1074_;
}
}
v___jp_1075_:
{
lean_object* v___x_1077_; 
lean_inc_ref(v___x_1044_);
v___x_1077_ = lean_local_ctx_find(v___x_1044_, v___y_1076_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1079_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1078_);
v___y_1071_ = v___x_1079_;
goto v___jp_1070_;
}
else
{
lean_object* v_val_1080_; 
v_val_1080_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_val_1080_);
lean_dec_ref_known(v___x_1077_, 1);
v___y_1071_ = v_val_1080_;
goto v___jp_1070_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5___boxed(lean_object* v_minIndex_1118_, lean_object* v___x_1119_, lean_object* v___x_1120_, lean_object* v_start_1121_, lean_object* v_xs_1122_, lean_object* v___x_1123_, lean_object* v_e_1124_, lean_object* v_offset_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
uint8_t v_a_boxed_1130_; lean_object* v_res_1131_; 
v_a_boxed_1130_ = lean_unbox(v_a_1127_);
v_res_1131_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_1118_, v___x_1119_, v___x_1120_, v_start_1121_, v_xs_1122_, v___x_1123_, v_e_1124_, v_offset_1125_, v_a_1126_, v_a_boxed_1130_, v_a_1128_, v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec_ref(v___x_1123_);
lean_dec_ref(v_xs_1122_);
lean_dec(v_start_1121_);
lean_dec(v___x_1120_);
lean_dec(v_minIndex_1118_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___boxed(lean_object* v_minIndex_1132_, lean_object* v___x_1133_, lean_object* v___x_1134_, lean_object* v_start_1135_, lean_object* v_xs_1136_, lean_object* v___x_1137_, lean_object* v_e_1138_, lean_object* v_offset_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
uint8_t v_a_boxed_1144_; lean_object* v_res_1145_; 
v_a_boxed_1144_ = lean_unbox(v_a_1141_);
v_res_1145_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v_minIndex_1132_, v___x_1133_, v___x_1134_, v_start_1135_, v_xs_1136_, v___x_1137_, v_e_1138_, v_offset_1139_, v_a_1140_, v_a_boxed_1144_, v_a_1142_, v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec_ref(v___x_1137_);
lean_dec_ref(v_xs_1136_);
lean_dec(v_start_1135_);
lean_dec(v___x_1134_);
lean_dec(v_minIndex_1132_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___lam__0(lean_object* v_e_1146_, lean_object* v_lctx_1147_, lean_object* v___x_1148_, lean_object* v_start_1149_, lean_object* v_xs_1150_, lean_object* v_maxFVar_1151_, uint8_t v_debug_1152_, uint8_t v___x_1153_, lean_object* v___x_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1204_; lean_object* v___x_1225_; 
lean_inc_ref(v_lctx_1147_);
v___x_1225_ = lean_local_ctx_find(v_lctx_1147_, v___x_1154_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1227_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1226_);
v___y_1204_ = v___x_1227_;
goto v___jp_1203_;
}
else
{
lean_object* v_val_1228_; 
v_val_1228_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_val_1228_);
lean_dec_ref_known(v___x_1225_, 1);
v___y_1204_ = v_val_1228_;
goto v___jp_1203_;
}
v___jp_1157_:
{
switch(lean_obj_tag(v_e_1146_))
{
case 9:
{
lean_object* v___x_1160_; 
lean_dec(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v_lctx_1147_);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v_e_1146_);
lean_ctor_set(v___x_1160_, 1, v___y_1156_);
return v___x_1160_;
}
case 2:
{
lean_object* v___x_1161_; 
lean_dec(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v_lctx_1147_);
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_e_1146_);
lean_ctor_set(v___x_1161_, 1, v___y_1156_);
return v___x_1161_;
}
case 0:
{
lean_object* v___x_1162_; 
lean_dec(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v_lctx_1147_);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v_e_1146_);
lean_ctor_set(v___x_1162_, 1, v___y_1156_);
return v___x_1162_;
}
case 1:
{
lean_object* v___x_1163_; 
lean_dec(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v_lctx_1147_);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v_e_1146_);
lean_ctor_set(v___x_1163_, 1, v___y_1156_);
return v___x_1163_;
}
case 4:
{
lean_object* v___x_1164_; 
lean_dec(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v_lctx_1147_);
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v_e_1146_);
lean_ctor_set(v___x_1164_, 1, v___y_1156_);
return v___x_1164_;
}
case 3:
{
lean_object* v___x_1165_; 
lean_dec(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v_lctx_1147_);
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v_e_1146_);
lean_ctor_set(v___x_1165_, 1, v___y_1156_);
return v___x_1165_;
}
default: 
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0);
lean_inc(v___y_1158_);
v___x_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___y_1158_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v___y_1159_, v_lctx_1147_, v___x_1148_, v_start_1149_, v_xs_1150_, v_maxFVar_1151_, v_e_1146_, v___y_1158_, v___x_1167_, v_debug_1152_, v___y_1155_, v___y_1156_);
lean_dec(v___y_1159_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1178_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_a_1170_ = lean_ctor_get(v___x_1168_, 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1172_ = v___x_1168_;
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v_fst_1174_; lean_object* v___x_1176_; 
v_fst_1174_ = lean_ctor_get(v_a_1169_, 0);
lean_inc(v_fst_1174_);
lean_dec(v_a_1169_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v_fst_1174_);
v___x_1176_ = v___x_1172_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_fst_1174_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_a_1170_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
v_a_1179_ = lean_ctor_get(v___x_1168_, 0);
v_a_1180_ = lean_ctor_get(v___x_1168_, 1);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1168_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_inc(v_a_1179_);
lean_dec(v___x_1168_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1179_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
}
v___jp_1188_:
{
lean_object* v_maxIndex_1192_; uint8_t v___x_1193_; 
v_maxIndex_1192_ = l_Lean_LocalDecl_index(v___y_1191_);
lean_dec_ref(v___y_1191_);
v___x_1193_ = lean_nat_dec_lt(v_maxIndex_1192_, v___y_1190_);
lean_dec(v_maxIndex_1192_);
if (v___x_1193_ == 0)
{
v___y_1158_ = v___y_1189_;
v___y_1159_ = v___y_1190_;
goto v___jp_1157_;
}
else
{
lean_object* v___x_1194_; 
lean_dec(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v_lctx_1147_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v_e_1146_);
lean_ctor_set(v___x_1194_, 1, v___y_1156_);
return v___x_1194_;
}
}
v___jp_1195_:
{
lean_object* v___x_1199_; 
lean_inc_ref(v_lctx_1147_);
v___x_1199_ = lean_local_ctx_find(v_lctx_1147_, v___y_1198_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1201_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1200_);
v___y_1189_ = v___y_1196_;
v___y_1190_ = v___y_1197_;
v___y_1191_ = v___x_1201_;
goto v___jp_1188_;
}
else
{
lean_object* v_val_1202_; 
v_val_1202_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_val_1202_);
lean_dec_ref_known(v___x_1199_, 1);
v___y_1189_ = v___y_1196_;
v___y_1190_ = v___y_1197_;
v___y_1191_ = v_val_1202_;
goto v___jp_1188_;
}
}
v___jp_1203_:
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1146_))
{
case 1:
{
lean_object* v_fvarId_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_lctx_1147_);
v_fvarId_1206_ = lean_ctor_get(v_e_1146_, 0);
v___x_1207_ = lean_unsigned_to_nat(1u);
v___x_1208_ = lean_nat_sub(v___x_1148_, v___x_1207_);
v___x_1209_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_1149_, v_xs_1150_, v_fvarId_1206_, v___x_1205_, v___x_1208_);
if (lean_obj_tag(v___x_1209_) == 1)
{
lean_object* v_val_1210_; lean_object* v___x_1211_; 
lean_dec_ref_known(v_e_1146_, 1);
v_val_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_val_1210_);
lean_dec_ref_known(v___x_1209_, 1);
v___x_1211_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v_val_1210_, v___y_1156_);
return v___x_1211_;
}
else
{
lean_object* v___x_1212_; 
lean_dec(v___x_1209_);
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v_e_1146_);
lean_ctor_set(v___x_1212_, 1, v___y_1156_);
return v___x_1212_;
}
}
case 9:
{
lean_object* v___x_1213_; 
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_lctx_1147_);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v_e_1146_);
lean_ctor_set(v___x_1213_, 1, v___y_1156_);
return v___x_1213_;
}
case 2:
{
lean_object* v___x_1214_; 
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_lctx_1147_);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v_e_1146_);
lean_ctor_set(v___x_1214_, 1, v___y_1156_);
return v___x_1214_;
}
case 0:
{
lean_object* v___x_1215_; 
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_lctx_1147_);
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v_e_1146_);
lean_ctor_set(v___x_1215_, 1, v___y_1156_);
return v___x_1215_;
}
case 4:
{
lean_object* v___x_1216_; 
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_lctx_1147_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_e_1146_);
lean_ctor_set(v___x_1216_, 1, v___y_1156_);
return v___x_1216_;
}
case 3:
{
lean_object* v___x_1217_; 
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_lctx_1147_);
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v_e_1146_);
lean_ctor_set(v___x_1217_, 1, v___y_1156_);
return v___x_1217_;
}
default: 
{
if (v___x_1153_ == 0)
{
lean_object* v___x_1218_; 
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_lctx_1147_);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v_e_1146_);
lean_ctor_set(v___x_1218_, 1, v___y_1156_);
return v___x_1218_;
}
else
{
lean_object* v_minIndex_1219_; lean_object* v___x_1220_; 
v_minIndex_1219_ = l_Lean_LocalDecl_index(v___y_1204_);
lean_dec_ref(v___y_1204_);
v___x_1220_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_maxFVar_1151_, v_e_1146_);
if (lean_obj_tag(v___x_1220_) == 1)
{
lean_object* v_val_1221_; 
v_val_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_val_1221_);
lean_dec_ref_known(v___x_1220_, 1);
if (lean_obj_tag(v_val_1221_) == 0)
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1223_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v___x_1222_);
v___y_1196_ = v___x_1205_;
v___y_1197_ = v_minIndex_1219_;
v___y_1198_ = v___x_1223_;
goto v___jp_1195_;
}
else
{
lean_object* v_val_1224_; 
v_val_1224_ = lean_ctor_get(v_val_1221_, 0);
lean_inc(v_val_1224_);
lean_dec_ref_known(v_val_1221_, 1);
v___y_1196_ = v___x_1205_;
v___y_1197_ = v_minIndex_1219_;
v___y_1198_ = v_val_1224_;
goto v___jp_1195_;
}
}
else
{
lean_dec(v___x_1220_);
v___y_1158_ = v___x_1205_;
v___y_1159_ = v_minIndex_1219_;
goto v___jp_1157_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___lam__0___boxed(lean_object* v_e_1229_, lean_object* v_lctx_1230_, lean_object* v___x_1231_, lean_object* v_start_1232_, lean_object* v_xs_1233_, lean_object* v_maxFVar_1234_, lean_object* v_debug_1235_, lean_object* v___x_1236_, lean_object* v___x_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
uint8_t v_debug_boxed_1240_; uint8_t v___x_27213__boxed_1241_; lean_object* v_res_1242_; 
v_debug_boxed_1240_ = lean_unbox(v_debug_1235_);
v___x_27213__boxed_1241_ = lean_unbox(v___x_1236_);
v_res_1242_ = l_Lean_Meta_Sym_abstractFVarsRange___lam__0(v_e_1229_, v_lctx_1230_, v___x_1231_, v_start_1232_, v_xs_1233_, v_maxFVar_1234_, v_debug_boxed_1240_, v___x_27213__boxed_1241_, v___x_1237_, v___y_1238_, v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec_ref(v_maxFVar_1234_);
lean_dec_ref(v_xs_1233_);
lean_dec(v_start_1232_);
lean_dec(v___x_1231_);
return v_res_1242_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_abstractFVarsRange___closed__2(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1245_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__2));
v___x_1246_ = lean_unsigned_to_nat(16u);
v___x_1247_ = lean_unsigned_to_nat(62u);
v___x_1248_ = ((lean_object*)(l_Lean_Meta_Sym_abstractFVarsRange___closed__1));
v___x_1249_ = ((lean_object*)(l_Lean_Meta_Sym_abstractFVarsRange___closed__0));
v___x_1250_ = l_mkPanicMessageWithDecl(v___x_1249_, v___x_1248_, v___x_1247_, v___x_1246_, v___x_1245_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange(lean_object* v_e_1251_, lean_object* v_start_1252_, lean_object* v_xs_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
uint8_t v___x_1261_; 
v___x_1261_ = l_Lean_Expr_hasFVar(v_e_1251_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; 
lean_dec_ref(v_xs_1253_);
lean_dec(v_start_1252_);
v___x_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1262_, 0, v_e_1251_);
return v___x_1262_;
}
else
{
lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = lean_array_get_size(v_xs_1253_);
v___x_1264_ = lean_nat_dec_lt(v_start_1252_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_dec_ref(v_xs_1253_);
lean_dec(v_start_1252_);
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v_e_1251_);
return v___x_1265_;
}
else
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v_lctx_1269_; lean_object* v_maxFVar_1270_; uint8_t v_debug_1271_; lean_object* v_env_1272_; uint8_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___f_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1266_ = lean_st_ref_get(v_a_1255_);
v___x_1267_ = lean_st_ref_get(v_a_1255_);
v___x_1268_ = lean_st_ref_get(v_a_1259_);
v_lctx_1269_ = lean_ctor_get(v_a_1256_, 2);
v_maxFVar_1270_ = lean_ctor_get(v___x_1266_, 1);
lean_inc_ref(v_maxFVar_1270_);
lean_dec(v___x_1266_);
v_debug_1271_ = lean_ctor_get_uint8(v___x_1267_, sizeof(void*)*11);
lean_dec(v___x_1267_);
v_env_1272_ = lean_ctor_get(v___x_1268_, 0);
lean_inc_ref(v_env_1272_);
lean_dec(v___x_1268_);
v___x_1273_ = 0;
v___x_1274_ = lean_array_fget_borrowed(v_xs_1253_, v_start_1252_);
v___x_1275_ = l_Lean_Expr_fvarId_x21(v___x_1274_);
v___x_1276_ = lean_box(v_debug_1271_);
v___x_1277_ = lean_box(v___x_1261_);
lean_inc_ref(v_lctx_1269_);
v___f_1278_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_abstractFVarsRange___lam__0___boxed), 11, 9);
lean_closure_set(v___f_1278_, 0, v_e_1251_);
lean_closure_set(v___f_1278_, 1, v_lctx_1269_);
lean_closure_set(v___f_1278_, 2, v___x_1263_);
lean_closure_set(v___f_1278_, 3, v_start_1252_);
lean_closure_set(v___f_1278_, 4, v_xs_1253_);
lean_closure_set(v___f_1278_, 5, v_maxFVar_1270_);
lean_closure_set(v___f_1278_, 6, v___x_1276_);
lean_closure_set(v___f_1278_, 7, v___x_1277_);
lean_closure_set(v___f_1278_, 8, v___x_1275_);
v___x_1279_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1279_, 0, v_env_1272_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*1, v___x_1273_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*1 + 1, v___x_1273_);
v___x_1280_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1278_, v___x_1279_, v_a_1255_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1291_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1291_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1291_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
if (lean_obj_tag(v_a_1281_) == 0)
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_dec_ref_known(v_a_1281_, 1);
lean_del_object(v___x_1283_);
v___x_1285_ = lean_obj_once(&l_Lean_Meta_Sym_abstractFVarsRange___closed__2, &l_Lean_Meta_Sym_abstractFVarsRange___closed__2_once, _init_l_Lean_Meta_Sym_abstractFVarsRange___closed__2);
v___x_1286_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v___x_1285_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1286_;
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; 
v_a_1287_ = lean_ctor_get(v_a_1281_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v_a_1281_, 1);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v_a_1287_);
v___x_1289_ = v___x_1283_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
v_a_1292_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1280_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1280_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___boxed(lean_object* v_e_1300_, lean_object* v_start_1301_, lean_object* v_xs_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1300_, v_start_1301_, v_xs_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(lean_object* v_00_u03b2_1311_, lean_object* v_x_1312_, lean_object* v_x_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_x_1312_, v_x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___boxed(lean_object* v_00_u03b2_1315_, lean_object* v_x_1316_, lean_object* v_x_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(v_00_u03b2_1315_, v_x_1316_, v_x_1317_);
lean_dec_ref(v_x_1317_);
lean_dec_ref(v_x_1316_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2(lean_object* v_00_u03b2_1319_, lean_object* v_x_1320_, size_t v_x_1321_, lean_object* v_x_1322_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_1320_, v_x_1321_, v_x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_, lean_object* v_x_1327_){
_start:
{
size_t v_x_27503__boxed_1328_; lean_object* v_res_1329_; 
v_x_27503__boxed_1328_ = lean_unbox_usize(v_x_1326_);
lean_dec(v_x_1326_);
v_res_1329_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2(v_00_u03b2_1324_, v_x_1325_, v_x_27503__boxed_1328_, v_x_1327_);
lean_dec_ref(v_x_1327_);
lean_dec_ref(v_x_1325_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_1330_, lean_object* v_keys_1331_, lean_object* v_vals_1332_, lean_object* v_heq_1333_, lean_object* v_i_1334_, lean_object* v_k_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_keys_1331_, v_vals_1332_, v_i_1334_, v_k_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1337_, lean_object* v_keys_1338_, lean_object* v_vals_1339_, lean_object* v_heq_1340_, lean_object* v_i_1341_, lean_object* v_k_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5(v_00_u03b2_1337_, v_keys_1338_, v_vals_1339_, v_heq_1340_, v_i_1341_, v_k_1342_);
lean_dec_ref(v_k_1342_);
lean_dec_ref(v_vals_1339_);
lean_dec_ref(v_keys_1338_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_1344_, lean_object* v_m_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_m_1345_, v_a_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1348_, lean_object* v_m_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8(v_00_u03b2_1348_, v_m_1349_, v_a_1350_);
lean_dec_ref(v_a_1350_);
lean_dec_ref(v_m_1349_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16(lean_object* v_00_u03b2_1352_, lean_object* v_a_1353_, lean_object* v_x_1354_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_a_1353_, v_x_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___boxed(lean_object* v_00_u03b2_1356_, lean_object* v_a_1357_, lean_object* v_x_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16(v_00_u03b2_1356_, v_a_1357_, v_x_1358_);
lean_dec(v_x_1358_);
lean_dec_ref(v_a_1357_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars(lean_object* v_e_1360_, lean_object* v_xs_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_unsigned_to_nat(0u);
v___x_1370_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1360_, v___x_1369_, v_xs_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___boxed(lean_object* v_e_1371_, lean_object* v_xs_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_Meta_Sym_abstractFVars(v_e_1371_, v_xs_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(lean_object* v_x_1381_, uint8_t v_bi_1382_, lean_object* v_t_1383_, lean_object* v_b_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___y_1393_; lean_object* v___x_1396_; uint8_t v_debug_1397_; 
v___x_1396_ = lean_st_ref_get(v___y_1386_);
v_debug_1397_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*11);
lean_dec(v___x_1396_);
if (v_debug_1397_ == 0)
{
v___y_1393_ = v___y_1386_;
goto v___jp_1392_;
}
else
{
lean_object* v___x_1398_; 
lean_inc_ref(v_t_1383_);
v___x_1398_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1383_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v___x_1399_; 
lean_dec_ref_known(v___x_1398_, 1);
lean_inc_ref(v_b_1384_);
v___x_1399_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_dec_ref_known(v___x_1399_, 1);
v___y_1393_ = v___y_1386_;
goto v___jp_1392_;
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec_ref(v_b_1384_);
lean_dec_ref(v_t_1383_);
lean_dec(v_x_1381_);
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec_ref(v_b_1384_);
lean_dec_ref(v_t_1383_);
lean_dec(v_x_1381_);
v_a_1408_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1398_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1398_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
v___jp_1392_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = l_Lean_Expr_lam___override(v_x_1381_, v_t_1383_, v_b_1384_, v_bi_1382_);
v___x_1395_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1394_, v___y_1393_);
return v___x_1395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0___boxed(lean_object* v_x_1416_, lean_object* v_bi_1417_, lean_object* v_t_1418_, lean_object* v_b_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
uint8_t v_bi_boxed_1427_; lean_object* v_res_1428_; 
v_bi_boxed_1427_ = lean_unbox(v_bi_1417_);
v_res_1428_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v_x_1416_, v_bi_boxed_1427_, v_t_1418_, v_b_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(lean_object* v_xs_1429_, lean_object* v_i_1430_, lean_object* v_a_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_zero_1439_; uint8_t v_isZero_1440_; 
v_zero_1439_ = lean_unsigned_to_nat(0u);
v_isZero_1440_ = lean_nat_dec_eq(v_i_1430_, v_zero_1439_);
if (v_isZero_1440_ == 1)
{
lean_object* v___x_1441_; 
lean_dec(v_i_1430_);
lean_dec_ref(v_xs_1429_);
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v_a_1431_);
return v___x_1441_;
}
else
{
lean_object* v_one_1442_; lean_object* v_n_1443_; lean_object* v___y_1445_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v_one_1442_ = lean_unsigned_to_nat(1u);
v_n_1443_ = lean_nat_sub(v_i_1430_, v_one_1442_);
lean_dec(v_i_1430_);
v___x_1448_ = lean_array_fget_borrowed(v_xs_1429_, v_n_1443_);
v___x_1449_ = l_Lean_Expr_fvarId_x21(v___x_1448_);
v___x_1450_ = l_Lean_FVarId_getDecl___redArg(v___x_1449_, v___y_1434_, v___y_1436_, v___y_1437_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1450_, 1);
v___x_1452_ = l_Lean_LocalDecl_type(v_a_1451_);
lean_inc_ref(v_xs_1429_);
lean_inc(v_n_1443_);
v___x_1453_ = l_Lean_Meta_Sym_abstractFVarsRange(v___x_1452_, v_n_1443_, v_xs_1429_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; lean_object* v___x_1457_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1453_, 1);
v___x_1455_ = l_Lean_LocalDecl_userName(v_a_1451_);
v___x_1456_ = l_Lean_LocalDecl_binderInfo(v_a_1451_);
lean_dec(v_a_1451_);
v___x_1457_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v___x_1455_, v___x_1456_, v_a_1454_, v_a_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
v___y_1445_ = v___x_1457_;
goto v___jp_1444_;
}
else
{
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1431_);
v___y_1445_ = v___x_1453_;
goto v___jp_1444_;
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_n_1443_);
lean_dec_ref(v_a_1431_);
lean_dec_ref(v_xs_1429_);
v_a_1458_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1450_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1450_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
v___jp_1444_:
{
if (lean_obj_tag(v___y_1445_) == 0)
{
lean_object* v_a_1446_; 
v_a_1446_ = lean_ctor_get(v___y_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___y_1445_, 1);
v_i_1430_ = v_n_1443_;
v_a_1431_ = v_a_1446_;
goto _start;
}
else
{
lean_dec(v_n_1443_);
lean_dec_ref(v_xs_1429_);
return v___y_1445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg___boxed(lean_object* v_xs_1466_, lean_object* v_i_1467_, lean_object* v_a_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1466_, v_i_1467_, v_a_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS(lean_object* v_xs_1477_, lean_object* v_e_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_xs_1477_);
v___x_1487_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1478_, v___x_1486_, v_xs_1477_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref_known(v___x_1487_, 1);
v___x_1489_ = lean_array_get_size(v_xs_1477_);
v___x_1490_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1477_, v___x_1489_, v_a_1488_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
return v___x_1490_;
}
else
{
lean_dec_ref(v_xs_1477_);
return v___x_1487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS___boxed(lean_object* v_xs_1491_, lean_object* v_e_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_1491_, v_e_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(lean_object* v_xs_1501_, lean_object* v_n_1502_, lean_object* v_i_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1501_, v_i_1503_, v_a_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___boxed(lean_object* v_xs_1514_, lean_object* v_n_1515_, lean_object* v_i_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(v_xs_1514_, v_n_1515_, v_i_1516_, v_a_1517_, v_a_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v_n_1515_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(lean_object* v_x_1527_, uint8_t v_bi_1528_, lean_object* v_t_1529_, lean_object* v_b_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___y_1539_; lean_object* v___x_1542_; uint8_t v_debug_1543_; 
v___x_1542_ = lean_st_ref_get(v___y_1532_);
v_debug_1543_ = lean_ctor_get_uint8(v___x_1542_, sizeof(void*)*11);
lean_dec(v___x_1542_);
if (v_debug_1543_ == 0)
{
v___y_1539_ = v___y_1532_;
goto v___jp_1538_;
}
else
{
lean_object* v___x_1544_; 
lean_inc_ref(v_t_1529_);
v___x_1544_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1529_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v___x_1545_; 
lean_dec_ref_known(v___x_1544_, 1);
lean_inc_ref(v_b_1530_);
v___x_1545_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_dec_ref_known(v___x_1545_, 1);
v___y_1539_ = v___y_1532_;
goto v___jp_1538_;
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec_ref(v_b_1530_);
lean_dec_ref(v_t_1529_);
lean_dec(v_x_1527_);
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec_ref(v_b_1530_);
lean_dec_ref(v_t_1529_);
lean_dec(v_x_1527_);
v_a_1554_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1544_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1544_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
v___jp_1538_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = l_Lean_Expr_forallE___override(v_x_1527_, v_t_1529_, v_b_1530_, v_bi_1528_);
v___x_1541_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1540_, v___y_1539_);
return v___x_1541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0___boxed(lean_object* v_x_1562_, lean_object* v_bi_1563_, lean_object* v_t_1564_, lean_object* v_b_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
uint8_t v_bi_boxed_1573_; lean_object* v_res_1574_; 
v_bi_boxed_1573_ = lean_unbox(v_bi_1563_);
v_res_1574_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v_x_1562_, v_bi_boxed_1573_, v_t_1564_, v_b_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(lean_object* v_xs_1575_, lean_object* v_i_1576_, lean_object* v_a_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_zero_1585_; uint8_t v_isZero_1586_; 
v_zero_1585_ = lean_unsigned_to_nat(0u);
v_isZero_1586_ = lean_nat_dec_eq(v_i_1576_, v_zero_1585_);
if (v_isZero_1586_ == 1)
{
lean_object* v___x_1587_; 
lean_dec(v_i_1576_);
lean_dec_ref(v_xs_1575_);
v___x_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1587_, 0, v_a_1577_);
return v___x_1587_;
}
else
{
lean_object* v_one_1588_; lean_object* v_n_1589_; lean_object* v___y_1591_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_one_1588_ = lean_unsigned_to_nat(1u);
v_n_1589_ = lean_nat_sub(v_i_1576_, v_one_1588_);
lean_dec(v_i_1576_);
v___x_1594_ = lean_array_fget_borrowed(v_xs_1575_, v_n_1589_);
v___x_1595_ = l_Lean_Expr_fvarId_x21(v___x_1594_);
v___x_1596_ = l_Lean_FVarId_getDecl___redArg(v___x_1595_, v___y_1580_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
lean_dec_ref_known(v___x_1596_, 1);
v___x_1598_ = l_Lean_LocalDecl_type(v_a_1597_);
lean_inc_ref(v_xs_1575_);
lean_inc(v_n_1589_);
v___x_1599_ = l_Lean_Meta_Sym_abstractFVarsRange(v___x_1598_, v_n_1589_, v_xs_1575_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; lean_object* v___x_1603_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v___x_1599_, 1);
v___x_1601_ = l_Lean_LocalDecl_userName(v_a_1597_);
v___x_1602_ = l_Lean_LocalDecl_binderInfo(v_a_1597_);
lean_dec(v_a_1597_);
v___x_1603_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v___x_1601_, v___x_1602_, v_a_1600_, v_a_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
v___y_1591_ = v___x_1603_;
goto v___jp_1590_;
}
else
{
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1577_);
v___y_1591_ = v___x_1599_;
goto v___jp_1590_;
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_n_1589_);
lean_dec_ref(v_a_1577_);
lean_dec_ref(v_xs_1575_);
v_a_1604_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1596_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1596_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
v___jp_1590_:
{
if (lean_obj_tag(v___y_1591_) == 0)
{
lean_object* v_a_1592_; 
v_a_1592_ = lean_ctor_get(v___y_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___y_1591_, 1);
v_i_1576_ = v_n_1589_;
v_a_1577_ = v_a_1592_;
goto _start;
}
else
{
lean_dec(v_n_1589_);
lean_dec_ref(v_xs_1575_);
return v___y_1591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg___boxed(lean_object* v_xs_1612_, lean_object* v_i_1613_, lean_object* v_a_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1612_, v_i_1613_, v_a_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object* v_xs_1623_, lean_object* v_e_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_xs_1623_);
v___x_1633_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1624_, v___x_1632_, v_xs_1623_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1635_ = lean_array_get_size(v_xs_1623_);
v___x_1636_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1623_, v___x_1635_, v_a_1634_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
return v___x_1636_;
}
else
{
lean_dec_ref(v_xs_1623_);
return v___x_1633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS___boxed(lean_object* v_xs_1637_, lean_object* v_e_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_Meta_Sym_mkForallFVarsS(v_xs_1637_, v_e_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(lean_object* v_xs_1647_, lean_object* v_n_1648_, lean_object* v_i_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1647_, v_i_1649_, v_a_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___boxed(lean_object* v_xs_1660_, lean_object* v_n_1661_, lean_object* v_i_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(v_xs_1660_, v_n_1661_, v_i_1662_, v_a_1663_, v_a_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v_n_1661_);
return v_res_1672_;
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
