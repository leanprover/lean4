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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v___x_43_; lean_object* v___x_2511__overap_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_43_ = lean_nat_add(v_offset_19_, v_val_39_);
lean_dec(v_val_39_);
v___x_2511__overap_44_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v___x_13_, v___x_43_);
v___x_45_ = lean_box(v___y_20_);
lean_inc_ref(v___y_21_);
v___x_46_ = lean_apply_3(v___x_2511__overap_44_, v___x_45_, v___y_21_, v___y_22_);
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
uint8_t v___x_81_; uint8_t v___x_82_; 
lean_dec_ref(v___x_13_);
lean_dec_ref(v_toDeBruijn_x3f_12_);
v___x_81_ = l_Lean_Expr_hasFVar(v_e_18_);
v___x_82_ = lean_bool_not(v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___f_83_; lean_object* v___f_84_; lean_object* v___x_85_; 
v___f_83_ = ((lean_object*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4));
v___f_84_ = ((lean_object*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5));
lean_inc_ref(v_e_18_);
v___x_85_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_83_, v___f_84_, v_maxFVar_14_, v_e_18_);
if (lean_obj_tag(v___x_85_) == 1)
{
lean_object* v_val_86_; 
v_val_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc(v_val_86_);
lean_dec_ref_known(v___x_85_, 1);
if (lean_obj_tag(v_val_86_) == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_box(0);
v___x_88_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_89_ = l_panic___redArg(v___x_87_, v___x_88_);
v___y_32_ = v___x_89_;
goto v___jp_31_;
}
else
{
lean_object* v_val_90_; 
v_val_90_ = lean_ctor_get(v_val_86_, 0);
lean_inc(v_val_90_);
lean_dec_ref_known(v_val_86_, 1);
v___y_32_ = v_val_90_;
goto v___jp_31_;
}
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v___x_85_);
lean_dec_ref(v_e_18_);
lean_dec_ref(v_lctx_16_);
v___x_91_ = lean_box(0);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set(v___x_92_, 1, v___y_22_);
return v___x_92_;
}
}
else
{
lean_object* v___x_93_; lean_object* v___x_94_; 
lean_dec_ref(v_lctx_16_);
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v_e_18_);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___y_22_);
return v___x_94_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed(lean_object* v_toDeBruijn_x3f_95_, lean_object* v___x_96_, lean_object* v_maxFVar_97_, lean_object* v_minIndex_98_, lean_object* v_lctx_99_, lean_object* v___x_100_, lean_object* v_e_101_, lean_object* v_offset_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
uint8_t v___y_2607__boxed_106_; lean_object* v_res_107_; 
v___y_2607__boxed_106_ = lean_unbox(v___y_103_);
v_res_107_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(v_toDeBruijn_x3f_95_, v___x_96_, v_maxFVar_97_, v_minIndex_98_, v_lctx_99_, v___x_100_, v_e_101_, v_offset_102_, v___y_2607__boxed_106_, v___y_104_, v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v_offset_102_);
lean_dec_ref(v___x_100_);
lean_dec(v_minIndex_98_);
lean_dec_ref(v_maxFVar_97_);
return v_res_107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_box(0);
v___x_109_ = lean_unsigned_to_nat(16u);
v___x_110_ = lean_mk_array(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0);
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___x_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(lean_object* v_e_114_, lean_object* v_lctx_115_, lean_object* v_maxFVar_116_, lean_object* v_minFVarId_117_, lean_object* v_toDeBruijn_x3f_118_, uint8_t v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___y_125_; lean_object* v___x_226_; 
v___x_122_ = l_Lean_instInhabitedLocalDecl_default;
v___x_123_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
lean_inc_ref(v_lctx_115_);
v___x_226_ = lean_local_ctx_find(v_lctx_115_, v_minFVarId_117_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_228_ = l_panic___redArg(v___x_122_, v___x_227_);
v___y_125_ = v___x_228_;
goto v___jp_124_;
}
else
{
lean_object* v_val_229_; 
v_val_229_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_val_229_);
lean_dec_ref_known(v___x_226_, 1);
v___y_125_ = v_val_229_;
goto v___jp_124_;
}
v___jp_124_:
{
lean_object* v_minIndex_126_; lean_object* v___f_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_minIndex_126_ = l_Lean_LocalDecl_index(v___y_125_);
lean_dec_ref(v___y_125_);
lean_inc_ref(v_lctx_115_);
lean_inc(v_minIndex_126_);
lean_inc_ref(v_maxFVar_116_);
lean_inc_ref(v_toDeBruijn_x3f_118_);
v___f_127_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed), 11, 6);
lean_closure_set(v___f_127_, 0, v_toDeBruijn_x3f_118_);
lean_closure_set(v___f_127_, 1, v___x_123_);
lean_closure_set(v___f_127_, 2, v_maxFVar_116_);
lean_closure_set(v___f_127_, 3, v_minIndex_126_);
lean_closure_set(v___f_127_, 4, v_lctx_115_);
lean_closure_set(v___f_127_, 5, v___x_122_);
v___x_128_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_e_114_);
v___x_129_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(v_toDeBruijn_x3f_118_, v___x_123_, v_maxFVar_116_, v_minIndex_126_, v_lctx_115_, v___x_122_, v_e_114_, v___x_128_, v_a_119_, v_a_120_, v_a_121_);
lean_dec(v_minIndex_126_);
lean_dec_ref(v_maxFVar_116_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_a_130_);
if (lean_obj_tag(v_a_130_) == 1)
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_139_; 
lean_dec_ref(v___f_127_);
lean_dec_ref(v_e_114_);
v_a_131_ = lean_ctor_get(v___x_129_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_139_ == 0)
{
lean_object* v_unused_140_; 
v_unused_140_ = lean_ctor_get(v___x_129_, 0);
lean_dec(v_unused_140_);
v___x_133_ = v___x_129_;
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_129_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v_val_135_; lean_object* v___x_137_; 
v_val_135_ = lean_ctor_get(v_a_130_, 0);
lean_inc(v_val_135_);
lean_dec_ref_known(v_a_130_, 1);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v_val_135_);
v___x_137_ = v___x_133_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_val_135_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_a_131_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
else
{
lean_dec(v_a_130_);
switch(lean_obj_tag(v_e_114_))
{
case 9:
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
lean_dec_ref(v___f_127_);
v_a_141_ = lean_ctor_get(v___x_129_, 1);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_148_ == 0)
{
lean_object* v_unused_149_; 
v_unused_149_ = lean_ctor_get(v___x_129_, 0);
lean_dec(v_unused_149_);
v___x_143_ = v___x_129_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_129_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v_e_114_);
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_e_114_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
case 2:
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
lean_dec_ref(v___f_127_);
v_a_150_ = lean_ctor_get(v___x_129_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; 
v_unused_158_ = lean_ctor_get(v___x_129_, 0);
lean_dec(v_unused_158_);
v___x_152_ = v___x_129_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_129_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v_e_114_);
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_e_114_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
case 0:
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
lean_dec_ref(v___f_127_);
v_a_159_ = lean_ctor_get(v___x_129_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_166_ == 0)
{
lean_object* v_unused_167_; 
v_unused_167_ = lean_ctor_get(v___x_129_, 0);
lean_dec(v_unused_167_);
v___x_161_ = v___x_129_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_129_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v_e_114_);
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_e_114_);
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
case 1:
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
lean_dec_ref(v___f_127_);
v_a_168_ = lean_ctor_get(v___x_129_, 1);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_175_ == 0)
{
lean_object* v_unused_176_; 
v_unused_176_ = lean_ctor_get(v___x_129_, 0);
lean_dec(v_unused_176_);
v___x_170_ = v___x_129_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_129_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v_e_114_);
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_e_114_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
case 4:
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_dec_ref(v___f_127_);
v_a_177_ = lean_ctor_get(v___x_129_, 1);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; 
v_unused_185_ = lean_ctor_get(v___x_129_, 0);
lean_dec(v_unused_185_);
v___x_179_ = v___x_129_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_129_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v_e_114_);
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_e_114_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
case 3:
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
lean_dec_ref(v___f_127_);
v_a_186_ = lean_ctor_get(v___x_129_, 1);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; 
v_unused_194_ = lean_ctor_get(v___x_129_, 0);
lean_dec(v_unused_194_);
v___x_188_ = v___x_129_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_129_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v_e_114_);
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_e_114_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
default: 
{
lean_object* v_a_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_a_195_ = lean_ctor_get(v___x_129_, 1);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_129_, 2);
v___x_196_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1);
v___x_197_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_114_, v___x_128_, v___f_127_, v___x_196_, v_a_119_, v_a_120_, v_a_195_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_207_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
v_a_199_ = lean_ctor_get(v___x_197_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_207_ == 0)
{
v___x_201_ = v___x_197_;
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_inc(v_a_198_);
lean_dec(v___x_197_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v_fst_203_; lean_object* v___x_205_; 
v_fst_203_ = lean_ctor_get(v_a_198_, 0);
lean_inc(v_fst_203_);
lean_dec(v_a_198_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v_fst_203_);
v___x_205_ = v___x_201_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_fst_203_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_a_199_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
else
{
lean_object* v_a_208_; lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
v_a_208_ = lean_ctor_get(v___x_197_, 0);
v_a_209_ = lean_ctor_get(v___x_197_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_197_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_inc(v_a_208_);
lean_dec(v___x_197_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_208_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_217_; lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec_ref(v___f_127_);
lean_dec_ref(v_e_114_);
v_a_217_ = lean_ctor_get(v___x_129_, 0);
v_a_218_ = lean_ctor_get(v___x_129_, 1);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_129_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_inc(v_a_217_);
lean_dec(v___x_129_);
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
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_217_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_a_218_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___boxed(lean_object* v_e_230_, lean_object* v_lctx_231_, lean_object* v_maxFVar_232_, lean_object* v_minFVarId_233_, lean_object* v_toDeBruijn_x3f_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
uint8_t v_a_boxed_238_; lean_object* v_res_239_; 
v_a_boxed_238_ = lean_unbox(v_a_235_);
v_res_239_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(v_e_230_, v_lctx_231_, v_maxFVar_232_, v_minFVarId_233_, v_toDeBruijn_x3f_234_, v_a_boxed_238_, v_a_236_, v_a_237_);
lean_dec_ref(v_a_236_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(lean_object* v_start_240_, lean_object* v_xs_241_, lean_object* v_fvarId_242_, lean_object* v_bidx_243_, lean_object* v_i_244_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_245_ = lean_array_fget_borrowed(v_xs_241_, v_i_244_);
v___x_246_ = l_Lean_Expr_fvarId_x21(v___x_245_);
v___x_247_ = l_Lean_instBEqFVarId_beq(v___x_246_, v_fvarId_242_);
lean_dec(v___x_246_);
if (v___x_247_ == 0)
{
uint8_t v___x_248_; 
v___x_248_ = lean_nat_dec_lt(v_start_240_, v_i_244_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; 
lean_dec(v_i_244_);
lean_dec(v_bidx_243_);
v___x_249_ = lean_box(0);
return v___x_249_;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_unsigned_to_nat(1u);
v___x_251_ = lean_nat_add(v_bidx_243_, v___x_250_);
lean_dec(v_bidx_243_);
v___x_252_ = lean_nat_sub(v_i_244_, v___x_250_);
lean_dec(v_i_244_);
v_bidx_243_ = v___x_251_;
v_i_244_ = v___x_252_;
goto _start;
}
}
else
{
lean_object* v___x_254_; 
lean_dec(v_i_244_);
v___x_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_254_, 0, v_bidx_243_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg___boxed(lean_object* v_start_255_, lean_object* v_xs_256_, lean_object* v_fvarId_257_, lean_object* v_bidx_258_, lean_object* v_i_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_255_, v_xs_256_, v_fvarId_257_, v_bidx_258_, v_i_259_);
lean_dec(v_fvarId_257_);
lean_dec_ref(v_xs_256_);
lean_dec(v_start_255_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(lean_object* v_start_261_, lean_object* v_xs_262_, lean_object* v_fvarId_263_, lean_object* v_bidx_264_, lean_object* v_i_265_, lean_object* v_h_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_261_, v_xs_262_, v_fvarId_263_, v_bidx_264_, v_i_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___boxed(lean_object* v_start_268_, lean_object* v_xs_269_, lean_object* v_fvarId_270_, lean_object* v_bidx_271_, lean_object* v_i_272_, lean_object* v_h_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(v_start_268_, v_xs_269_, v_fvarId_270_, v_bidx_271_, v_i_272_, v_h_273_);
lean_dec(v_fvarId_270_);
lean_dec_ref(v_xs_269_);
lean_dec(v_start_268_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(lean_object* v_msg_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = l_Lean_instInhabitedLocalDecl_default;
v___x_277_ = lean_panic_fn_borrowed(v___x_276_, v_msg_275_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(lean_object* v_idx_278_, lean_object* v___y_279_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = l_Lean_Expr_bvar___override(v_idx_278_);
v___x_281_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_280_, v___y_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(lean_object* v_idx_282_, uint8_t v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v_idx_282_, v___y_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___boxed(lean_object* v_idx_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
uint8_t v___y_25569__boxed_291_; lean_object* v_res_292_; 
v___y_25569__boxed_291_ = lean_unbox(v___y_288_);
v_res_292_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v_idx_287_, v___y_25569__boxed_291_, v___y_289_, v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(lean_object* v_msg_293_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_box(0);
v___x_295_ = lean_panic_fn_borrowed(v___x_294_, v_msg_293_);
return v___x_295_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0(void){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(lean_object* v_msg_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_2475__overap_306_; lean_object* v___x_307_; 
v___x_305_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0, &l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0);
v___x_2475__overap_306_ = lean_panic_fn_borrowed(v___x_305_, v_msg_297_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
lean_inc(v___y_301_);
lean_inc_ref(v___y_300_);
lean_inc(v___y_299_);
lean_inc_ref(v___y_298_);
v___x_307_ = lean_apply_7(v___x_2475__overap_306_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, lean_box(0));
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___boxed(lean_object* v_msg_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v_msg_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(lean_object* v_msg_324_, lean_object* v___y_325_, uint8_t v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v___f_329_; lean_object* v___f_330_; lean_object* v___f_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___f_341_; lean_object* v___f_342_; lean_object* v___f_343_; lean_object* v___f_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_25097__overap_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___f_329_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__0));
v___f_330_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__1));
v___f_331_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__2));
v___x_332_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__3));
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___f_329_);
v___x_334_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__4));
v___x_335_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__5));
v___x_336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_336_, 0, v___x_333_);
lean_ctor_set(v___x_336_, 1, v___x_334_);
lean_ctor_set(v___x_336_, 2, v___f_330_);
lean_ctor_set(v___x_336_, 3, v___f_331_);
lean_ctor_set(v___x_336_, 4, v___x_335_);
v___x_337_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___closed__6));
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = l_ReaderT_instMonad___redArg(v___x_338_);
v___x_340_ = l_ReaderT_instMonad___redArg(v___x_339_);
lean_inc_ref_n(v___x_340_, 6);
v___f_341_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_341_, 0, v___x_340_);
v___f_342_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_342_, 0, v___x_340_);
v___f_343_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_343_, 0, v___x_340_);
v___f_344_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_344_, 0, v___x_340_);
v___x_345_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_345_, 0, lean_box(0));
lean_closure_set(v___x_345_, 1, lean_box(0));
lean_closure_set(v___x_345_, 2, v___x_340_);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___f_341_);
v___x_347_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_347_, 0, lean_box(0));
lean_closure_set(v___x_347_, 1, lean_box(0));
lean_closure_set(v___x_347_, 2, v___x_340_);
v___x_348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_348_, 0, v___x_346_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
lean_ctor_set(v___x_348_, 2, v___f_342_);
lean_ctor_set(v___x_348_, 3, v___f_343_);
lean_ctor_set(v___x_348_, 4, v___f_344_);
v___x_349_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_349_, 0, lean_box(0));
lean_closure_set(v___x_349_, 1, lean_box(0));
lean_closure_set(v___x_349_, 2, v___x_340_);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = l_Lean_instInhabitedExpr;
v___x_352_ = l_instInhabitedOfMonad___redArg(v___x_350_, v___x_351_);
v___x_25097__overap_353_ = lean_panic_fn_borrowed(v___x_352_, v_msg_324_);
lean_dec(v___x_352_);
v___x_354_ = lean_box(v___y_326_);
lean_inc_ref(v___y_327_);
v___x_355_ = lean_apply_4(v___x_25097__overap_353_, v___y_325_, v___x_354_, v___y_327_, v___y_328_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12___boxed(lean_object* v_msg_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
uint8_t v___y_25627__boxed_361_; lean_object* v_res_362_; 
v___y_25627__boxed_361_ = lean_unbox(v___y_358_);
v_res_362_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(v_msg_356_, v___y_357_, v___y_25627__boxed_361_, v___y_359_, v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(lean_object* v_structName_363_, lean_object* v_idx_364_, lean_object* v_struct_365_, lean_object* v___y_366_, uint8_t v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
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
lean_inc_ref(v_struct_365_);
v___x_394_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_365_, v___y_367_, v___y_368_, v___y_369_);
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
lean_dec_ref(v_struct_365_);
lean_dec(v_idx_364_);
lean_dec(v_structName_363_);
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
v___x_373_ = l_Lean_Expr_proj___override(v_structName_363_, v_idx_364_, v_struct_365_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11___boxed(lean_object* v_structName_405_, lean_object* v_idx_406_, lean_object* v_struct_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
uint8_t v___y_25698__boxed_412_; lean_object* v_res_413_; 
v___y_25698__boxed_412_ = lean_unbox(v___y_409_);
v_res_413_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(v_structName_405_, v_idx_406_, v_struct_407_, v___y_408_, v___y_25698__boxed_412_, v___y_410_, v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(lean_object* v_d_414_, lean_object* v_e_415_, lean_object* v___y_416_, uint8_t v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
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
lean_inc_ref(v_e_415_);
v___x_444_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_415_, v___y_417_, v___y_418_, v___y_419_);
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
lean_dec_ref(v_e_415_);
lean_dec(v_d_414_);
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
v___x_423_ = l_Lean_Expr_mdata___override(v_d_414_, v_e_415_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10___boxed(lean_object* v_d_455_, lean_object* v_e_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
uint8_t v___y_25781__boxed_461_; lean_object* v_res_462_; 
v___y_25781__boxed_461_ = lean_unbox(v___y_458_);
v_res_462_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(v_d_455_, v_e_456_, v___y_457_, v___y_25781__boxed_461_, v___y_459_, v___y_460_);
lean_dec_ref(v___y_459_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(lean_object* v_keys_463_, lean_object* v_vals_464_, lean_object* v_i_465_, lean_object* v_k_466_){
_start:
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = lean_array_get_size(v_keys_463_);
v___x_468_ = lean_nat_dec_lt(v_i_465_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; 
lean_dec(v_i_465_);
v___x_469_ = lean_box(0);
return v___x_469_;
}
else
{
lean_object* v_k_x27_470_; uint8_t v___x_471_; 
v_k_x27_470_ = lean_array_fget_borrowed(v_keys_463_, v_i_465_);
v___x_471_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_466_, v_k_x27_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = lean_nat_add(v_i_465_, v___x_472_);
lean_dec(v_i_465_);
v_i_465_ = v___x_473_;
goto _start;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_array_fget_borrowed(v_vals_464_, v_i_465_);
lean_dec(v_i_465_);
lean_inc(v___x_475_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_keys_477_, lean_object* v_vals_478_, lean_object* v_i_479_, lean_object* v_k_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_keys_477_, v_vals_478_, v_i_479_, v_k_480_);
lean_dec_ref(v_k_480_);
lean_dec_ref(v_vals_478_);
lean_dec_ref(v_keys_477_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(lean_object* v_x_482_, size_t v_x_483_, lean_object* v_x_484_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
lean_object* v_es_485_; lean_object* v___x_486_; size_t v___x_487_; size_t v___x_488_; lean_object* v_j_489_; lean_object* v___x_490_; 
v_es_485_ = lean_ctor_get(v_x_482_, 0);
v___x_486_ = lean_box(2);
v___x_487_ = ((size_t)31ULL);
v___x_488_ = lean_usize_land(v_x_483_, v___x_487_);
v_j_489_ = lean_usize_to_nat(v___x_488_);
v___x_490_ = lean_array_get_borrowed(v___x_486_, v_es_485_, v_j_489_);
lean_dec(v_j_489_);
switch(lean_obj_tag(v___x_490_))
{
case 0:
{
lean_object* v_key_491_; lean_object* v_val_492_; uint8_t v___x_493_; 
v_key_491_ = lean_ctor_get(v___x_490_, 0);
v_val_492_ = lean_ctor_get(v___x_490_, 1);
v___x_493_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_484_, v_key_491_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
v___x_494_ = lean_box(0);
return v___x_494_;
}
else
{
lean_object* v___x_495_; 
lean_inc(v_val_492_);
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v_val_492_);
return v___x_495_;
}
}
case 1:
{
lean_object* v_node_496_; size_t v___x_497_; size_t v___x_498_; 
v_node_496_ = lean_ctor_get(v___x_490_, 0);
v___x_497_ = ((size_t)5ULL);
v___x_498_ = lean_usize_shift_right(v_x_483_, v___x_497_);
v_x_482_ = v_node_496_;
v_x_483_ = v___x_498_;
goto _start;
}
default: 
{
lean_object* v___x_500_; 
v___x_500_ = lean_box(0);
return v___x_500_;
}
}
}
else
{
lean_object* v_ks_501_; lean_object* v_vs_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_ks_501_ = lean_ctor_get(v_x_482_, 0);
v_vs_502_ = lean_ctor_get(v_x_482_, 1);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_ks_501_, v_vs_502_, v___x_503_, v_x_484_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg___boxed(lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
size_t v_x_25882__boxed_508_; lean_object* v_res_509_; 
v_x_25882__boxed_508_ = lean_unbox_usize(v_x_506_);
lean_dec(v_x_506_);
v_res_509_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_505_, v_x_25882__boxed_508_, v_x_507_);
lean_dec_ref(v_x_507_);
lean_dec_ref(v_x_505_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
uint64_t v___x_512_; size_t v___x_513_; lean_object* v___x_514_; 
v___x_512_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_511_);
v___x_513_ = lean_uint64_to_usize(v___x_512_);
v___x_514_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_510_, v___x_513_, v_x_511_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg___boxed(lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_x_515_, v_x_516_);
lean_dec_ref(v_x_516_);
lean_dec_ref(v_x_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(lean_object* v_a_518_, lean_object* v_x_519_){
_start:
{
if (lean_obj_tag(v_x_519_) == 0)
{
lean_object* v___x_520_; 
v___x_520_ = lean_box(0);
return v___x_520_;
}
else
{
lean_object* v_key_521_; lean_object* v_value_522_; lean_object* v_tail_523_; uint8_t v___y_525_; lean_object* v_fst_528_; lean_object* v_snd_529_; lean_object* v_fst_530_; lean_object* v_snd_531_; uint8_t v___x_532_; 
v_key_521_ = lean_ctor_get(v_x_519_, 0);
v_value_522_ = lean_ctor_get(v_x_519_, 1);
v_tail_523_ = lean_ctor_get(v_x_519_, 2);
v_fst_528_ = lean_ctor_get(v_key_521_, 0);
v_snd_529_ = lean_ctor_get(v_key_521_, 1);
v_fst_530_ = lean_ctor_get(v_a_518_, 0);
v_snd_531_ = lean_ctor_get(v_a_518_, 1);
v___x_532_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_528_, v_fst_530_);
if (v___x_532_ == 0)
{
v___y_525_ = v___x_532_;
goto v___jp_524_;
}
else
{
uint8_t v___x_533_; 
v___x_533_ = lean_nat_dec_eq(v_snd_529_, v_snd_531_);
v___y_525_ = v___x_533_;
goto v___jp_524_;
}
v___jp_524_:
{
if (v___y_525_ == 0)
{
v_x_519_ = v_tail_523_;
goto _start;
}
else
{
lean_object* v___x_527_; 
lean_inc(v_value_522_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v_value_522_);
return v___x_527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg___boxed(lean_object* v_a_534_, lean_object* v_x_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_a_534_, v_x_535_);
lean_dec(v_x_535_);
lean_dec_ref(v_a_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(lean_object* v_m_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_buckets_539_; lean_object* v_fst_540_; lean_object* v_snd_541_; lean_object* v___x_542_; uint64_t v___x_543_; uint64_t v___x_544_; uint64_t v___x_545_; uint64_t v___x_546_; uint64_t v___x_547_; uint64_t v_fold_548_; uint64_t v___x_549_; uint64_t v___x_550_; uint64_t v___x_551_; size_t v___x_552_; size_t v___x_553_; size_t v___x_554_; size_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_buckets_539_ = lean_ctor_get(v_m_537_, 1);
v_fst_540_ = lean_ctor_get(v_a_538_, 0);
v_snd_541_ = lean_ctor_get(v_a_538_, 1);
v___x_542_ = lean_array_get_size(v_buckets_539_);
v___x_543_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_540_);
v___x_544_ = lean_uint64_of_nat(v_snd_541_);
v___x_545_ = lean_uint64_mix_hash(v___x_543_, v___x_544_);
v___x_546_ = 32ULL;
v___x_547_ = lean_uint64_shift_right(v___x_545_, v___x_546_);
v_fold_548_ = lean_uint64_xor(v___x_545_, v___x_547_);
v___x_549_ = 16ULL;
v___x_550_ = lean_uint64_shift_right(v_fold_548_, v___x_549_);
v___x_551_ = lean_uint64_xor(v_fold_548_, v___x_550_);
v___x_552_ = lean_uint64_to_usize(v___x_551_);
v___x_553_ = lean_usize_of_nat(v___x_542_);
v___x_554_ = ((size_t)1ULL);
v___x_555_ = lean_usize_sub(v___x_553_, v___x_554_);
v___x_556_ = lean_usize_land(v___x_552_, v___x_555_);
v___x_557_ = lean_array_uget_borrowed(v_buckets_539_, v___x_556_);
v___x_558_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_a_538_, v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_m_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_m_559_, v_a_560_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_m_559_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(lean_object* v_x_562_, uint8_t v_bi_563_, lean_object* v_t_564_, lean_object* v_b_565_, lean_object* v___y_566_, uint8_t v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___y_571_; lean_object* v___y_572_; 
if (v___y_567_ == 0)
{
v___y_571_ = v___y_566_;
v___y_572_ = v___y_569_;
goto v___jp_570_;
}
else
{
lean_object* v___x_594_; 
lean_inc_ref(v_t_564_);
v___x_594_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_564_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_596_; 
v_a_595_ = lean_ctor_get(v___x_594_, 1);
lean_inc(v_a_595_);
lean_dec_ref_known(v___x_594_, 2);
lean_inc_ref(v_b_565_);
v___x_596_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_565_, v___y_567_, v___y_568_, v_a_595_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; 
v_a_597_ = lean_ctor_get(v___x_596_, 1);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 2);
v___y_571_ = v___y_566_;
v___y_572_ = v_a_597_;
goto v___jp_570_;
}
else
{
lean_object* v_a_598_; lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_dec_ref(v___y_566_);
lean_dec_ref(v_b_565_);
lean_dec_ref(v_t_564_);
lean_dec(v_x_562_);
v_a_598_ = lean_ctor_get(v___x_596_, 0);
v_a_599_ = lean_ctor_get(v___x_596_, 1);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_596_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_inc(v_a_598_);
lean_dec(v___x_596_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_598_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
else
{
lean_object* v_a_607_; lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v___y_566_);
lean_dec_ref(v_b_565_);
lean_dec_ref(v_t_564_);
lean_dec(v_x_562_);
v_a_607_ = lean_ctor_get(v___x_594_, 0);
v_a_608_ = lean_ctor_get(v___x_594_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_594_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_inc(v_a_607_);
lean_dec(v___x_594_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_607_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
v___jp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = l_Lean_Expr_forallE___override(v_x_562_, v_t_564_, v_b_565_, v_bi_563_);
v___x_574_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_573_, v___y_572_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_584_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_a_576_ = lean_ctor_get(v___x_574_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_584_ == 0)
{
v___x_578_ = v___x_574_;
v_isShared_579_ = v_isSharedCheck_584_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_584_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_a_575_);
lean_ctor_set(v___x_580_, 1, v___y_571_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_580_);
v___x_582_ = v___x_578_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_a_576_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
else
{
lean_object* v_a_585_; lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec_ref(v___y_571_);
v_a_585_ = lean_ctor_get(v___x_574_, 0);
v_a_586_ = lean_ctor_get(v___x_574_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_574_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_inc(v_a_585_);
lean_dec(v___x_574_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_585_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8___boxed(lean_object* v_x_616_, lean_object* v_bi_617_, lean_object* v_t_618_, lean_object* v_b_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
uint8_t v_bi_boxed_624_; uint8_t v___y_26010__boxed_625_; lean_object* v_res_626_; 
v_bi_boxed_624_ = lean_unbox(v_bi_617_);
v___y_26010__boxed_625_ = lean_unbox(v___y_621_);
v_res_626_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_x_616_, v_bi_boxed_624_, v_t_618_, v_b_619_, v___y_620_, v___y_26010__boxed_625_, v___y_622_, v___y_623_);
lean_dec_ref(v___y_622_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(lean_object* v_x_627_, uint8_t v_bi_628_, lean_object* v_t_629_, lean_object* v_b_630_, lean_object* v___y_631_, uint8_t v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v___y_636_; lean_object* v___y_637_; 
if (v___y_632_ == 0)
{
v___y_636_ = v___y_631_;
v___y_637_ = v___y_634_;
goto v___jp_635_;
}
else
{
lean_object* v___x_659_; 
lean_inc_ref(v_t_629_);
v___x_659_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_629_, v___y_632_, v___y_633_, v___y_634_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_661_; 
v_a_660_ = lean_ctor_get(v___x_659_, 1);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_659_, 2);
lean_inc_ref(v_b_630_);
v___x_661_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_630_, v___y_632_, v___y_633_, v_a_660_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; 
v_a_662_ = lean_ctor_get(v___x_661_, 1);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 2);
v___y_636_ = v___y_631_;
v___y_637_ = v_a_662_;
goto v___jp_635_;
}
else
{
lean_object* v_a_663_; lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec_ref(v___y_631_);
lean_dec_ref(v_b_630_);
lean_dec_ref(v_t_629_);
lean_dec(v_x_627_);
v_a_663_ = lean_ctor_get(v___x_661_, 0);
v_a_664_ = lean_ctor_get(v___x_661_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_661_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_inc(v_a_663_);
lean_dec(v___x_661_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_663_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
else
{
lean_object* v_a_672_; lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v___y_631_);
lean_dec_ref(v_b_630_);
lean_dec_ref(v_t_629_);
lean_dec(v_x_627_);
v_a_672_ = lean_ctor_get(v___x_659_, 0);
v_a_673_ = lean_ctor_get(v___x_659_, 1);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_659_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_inc(v_a_672_);
lean_dec(v___x_659_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_672_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_a_673_);
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
v___jp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = l_Lean_Expr_lam___override(v_x_627_, v_t_629_, v_b_630_, v_bi_628_);
v___x_639_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_638_, v___y_637_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_649_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_a_641_ = lean_ctor_get(v___x_639_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_649_ == 0)
{
v___x_643_ = v___x_639_;
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v_a_640_);
lean_ctor_set(v___x_645_, 1, v___y_636_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_645_);
v___x_647_ = v___x_643_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_a_641_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
else
{
lean_object* v_a_650_; lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref(v___y_636_);
v_a_650_ = lean_ctor_get(v___x_639_, 0);
v_a_651_ = lean_ctor_get(v___x_639_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_639_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_inc(v_a_650_);
lean_dec(v___x_639_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_650_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_a_651_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7___boxed(lean_object* v_x_681_, lean_object* v_bi_682_, lean_object* v_t_683_, lean_object* v_b_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
uint8_t v_bi_boxed_689_; uint8_t v___y_26116__boxed_690_; lean_object* v_res_691_; 
v_bi_boxed_689_ = lean_unbox(v_bi_682_);
v___y_26116__boxed_690_ = lean_unbox(v___y_686_);
v_res_691_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_x_681_, v_bi_boxed_689_, v_t_683_, v_b_684_, v___y_685_, v___y_26116__boxed_690_, v___y_687_, v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(lean_object* v_x_692_, lean_object* v_t_693_, lean_object* v_v_694_, lean_object* v_b_695_, uint8_t v_nondep_696_, lean_object* v___y_697_, uint8_t v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___y_702_; lean_object* v___y_703_; 
if (v___y_698_ == 0)
{
v___y_702_ = v___y_697_;
v___y_703_ = v___y_700_;
goto v___jp_701_;
}
else
{
lean_object* v___x_725_; 
lean_inc_ref(v_t_693_);
v___x_725_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_693_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; 
v_a_726_ = lean_ctor_get(v___x_725_, 1);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 2);
lean_inc_ref(v_v_694_);
v___x_727_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_694_, v___y_698_, v___y_699_, v_a_726_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; 
v_a_728_ = lean_ctor_get(v___x_727_, 1);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 2);
lean_inc_ref(v_b_695_);
v___x_729_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_695_, v___y_698_, v___y_699_, v_a_728_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; 
v_a_730_ = lean_ctor_get(v___x_729_, 1);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 2);
v___y_702_ = v___y_697_;
v___y_703_ = v_a_730_;
goto v___jp_701_;
}
else
{
lean_object* v_a_731_; lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref(v___y_697_);
lean_dec_ref(v_b_695_);
lean_dec_ref(v_v_694_);
lean_dec_ref(v_t_693_);
lean_dec(v_x_692_);
v_a_731_ = lean_ctor_get(v___x_729_, 0);
v_a_732_ = lean_ctor_get(v___x_729_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_729_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_inc(v_a_731_);
lean_dec(v___x_729_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_731_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
else
{
lean_object* v_a_740_; lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec_ref(v___y_697_);
lean_dec_ref(v_b_695_);
lean_dec_ref(v_v_694_);
lean_dec_ref(v_t_693_);
lean_dec(v_x_692_);
v_a_740_ = lean_ctor_get(v___x_727_, 0);
v_a_741_ = lean_ctor_get(v___x_727_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_727_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_inc(v_a_740_);
lean_dec(v___x_727_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_740_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_object* v_a_749_; lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec_ref(v___y_697_);
lean_dec_ref(v_b_695_);
lean_dec_ref(v_v_694_);
lean_dec_ref(v_t_693_);
lean_dec(v_x_692_);
v_a_749_ = lean_ctor_get(v___x_725_, 0);
v_a_750_ = lean_ctor_get(v___x_725_, 1);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_725_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_inc(v_a_749_);
lean_dec(v___x_725_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_749_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
v___jp_701_:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = l_Lean_Expr_letE___override(v_x_692_, v_t_693_, v_v_694_, v_b_695_, v_nondep_696_);
v___x_705_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_704_, v___y_703_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_715_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_a_707_ = lean_ctor_get(v___x_705_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_715_ == 0)
{
v___x_709_ = v___x_705_;
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v_a_706_);
lean_ctor_set(v___x_711_, 1, v___y_702_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_a_707_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
else
{
lean_object* v_a_716_; lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec_ref(v___y_702_);
v_a_716_ = lean_ctor_get(v___x_705_, 0);
v_a_717_ = lean_ctor_get(v___x_705_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_705_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_inc(v_a_716_);
lean_dec(v___x_705_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_716_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9___boxed(lean_object* v_x_758_, lean_object* v_t_759_, lean_object* v_v_760_, lean_object* v_b_761_, lean_object* v_nondep_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
uint8_t v_nondep_boxed_767_; uint8_t v___y_26222__boxed_768_; lean_object* v_res_769_; 
v_nondep_boxed_767_ = lean_unbox(v_nondep_762_);
v___y_26222__boxed_768_ = lean_unbox(v___y_764_);
v_res_769_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_x_758_, v_t_759_, v_v_760_, v_b_761_, v_nondep_boxed_767_, v___y_763_, v___y_26222__boxed_768_, v___y_765_, v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(lean_object* v_f_770_, lean_object* v_a_771_, lean_object* v___y_772_, uint8_t v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___y_777_; lean_object* v___y_778_; 
if (v___y_773_ == 0)
{
v___y_777_ = v___y_772_;
v___y_778_ = v___y_775_;
goto v___jp_776_;
}
else
{
lean_object* v___x_800_; 
lean_inc_ref(v_f_770_);
v___x_800_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_770_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_802_; 
v_a_801_ = lean_ctor_get(v___x_800_, 1);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_800_, 2);
lean_inc_ref(v_a_771_);
v___x_802_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_771_, v___y_773_, v___y_774_, v_a_801_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; 
v_a_803_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_802_, 2);
v___y_777_ = v___y_772_;
v___y_778_ = v_a_803_;
goto v___jp_776_;
}
else
{
lean_object* v_a_804_; lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec_ref(v___y_772_);
lean_dec_ref(v_a_771_);
lean_dec_ref(v_f_770_);
v_a_804_ = lean_ctor_get(v___x_802_, 0);
v_a_805_ = lean_ctor_get(v___x_802_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_802_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_inc(v_a_804_);
lean_dec(v___x_802_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_804_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_object* v_a_813_; lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec_ref(v___y_772_);
lean_dec_ref(v_a_771_);
lean_dec_ref(v_f_770_);
v_a_813_ = lean_ctor_get(v___x_800_, 0);
v_a_814_ = lean_ctor_get(v___x_800_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_800_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_inc(v_a_813_);
lean_dec(v___x_800_);
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
v___jp_776_:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = l_Lean_Expr_app___override(v_f_770_, v_a_771_);
v___x_780_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_779_, v___y_778_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_790_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_a_782_ = lean_ctor_get(v___x_780_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_790_ == 0)
{
v___x_784_ = v___x_780_;
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v_a_781_);
lean_ctor_set(v___x_786_, 1, v___y_777_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_786_);
v___x_788_ = v___x_784_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_a_782_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
else
{
lean_object* v_a_791_; lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec_ref(v___y_777_);
v_a_791_ = lean_ctor_get(v___x_780_, 0);
v_a_792_ = lean_ctor_get(v___x_780_, 1);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_780_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_inc(v_a_791_);
lean_dec(v___x_780_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_791_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6___boxed(lean_object* v_f_822_, lean_object* v_a_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
uint8_t v___y_26351__boxed_828_; lean_object* v_res_829_; 
v___y_26351__boxed_828_ = lean_unbox(v___y_825_);
v_res_829_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_f_822_, v_a_823_, v___y_824_, v___y_26351__boxed_828_, v___y_826_, v___y_827_);
lean_dec_ref(v___y_826_);
return v_res_829_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_833_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__2));
v___x_834_ = lean_unsigned_to_nat(67u);
v___x_835_ = lean_unsigned_to_nat(35u);
v___x_836_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__1));
v___x_837_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__0));
v___x_838_ = l_mkPanicMessageWithDecl(v___x_837_, v___x_836_, v___x_835_, v___x_834_, v___x_833_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(lean_object* v_minIndex_839_, lean_object* v___x_840_, lean_object* v___x_841_, lean_object* v_start_842_, lean_object* v_xs_843_, lean_object* v___x_844_, lean_object* v_e_845_, lean_object* v_offset_846_, lean_object* v_a_847_, uint8_t v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
switch(lean_obj_tag(v_e_845_))
{
case 5:
{
lean_object* v_fn_851_; lean_object* v_arg_852_; lean_object* v___x_853_; 
v_fn_851_ = lean_ctor_get(v_e_845_, 0);
v_arg_852_ = lean_ctor_get(v_e_845_, 1);
lean_inc(v_offset_846_);
lean_inc_ref(v_fn_851_);
lean_inc_ref(v___x_840_);
v___x_853_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_839_, v___x_840_, v___x_841_, v_start_842_, v_xs_843_, v___x_844_, v_fn_851_, v_offset_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v_a_855_; lean_object* v_fst_856_; lean_object* v_snd_857_; lean_object* v___x_858_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
v_a_855_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_853_, 2);
v_fst_856_ = lean_ctor_get(v_a_854_, 0);
lean_inc(v_fst_856_);
v_snd_857_ = lean_ctor_get(v_a_854_, 1);
lean_inc(v_snd_857_);
lean_dec(v_a_854_);
lean_inc_ref(v_arg_852_);
v___x_858_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_839_, v___x_840_, v___x_841_, v_start_842_, v_xs_843_, v___x_844_, v_arg_852_, v_offset_846_, v_snd_857_, v_a_848_, v_a_849_, v_a_855_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_881_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_a_860_ = lean_ctor_get(v___x_858_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_881_ == 0)
{
v___x_862_ = v___x_858_;
v_isShared_863_ = v_isSharedCheck_881_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_881_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v_fst_864_; lean_object* v_snd_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_880_; 
v_fst_864_ = lean_ctor_get(v_a_859_, 0);
v_snd_865_ = lean_ctor_get(v_a_859_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v_a_859_);
if (v_isSharedCheck_880_ == 0)
{
v___x_867_ = v_a_859_;
v_isShared_868_ = v_isSharedCheck_880_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_snd_865_);
lean_inc(v_fst_864_);
lean_dec(v_a_859_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_880_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
uint8_t v___y_870_; uint8_t v___x_878_; 
v___x_878_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_851_, v_fst_856_);
if (v___x_878_ == 0)
{
v___y_870_ = v___x_878_;
goto v___jp_869_;
}
else
{
uint8_t v___x_879_; 
v___x_879_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_852_, v_fst_864_);
v___y_870_ = v___x_879_;
goto v___jp_869_;
}
v___jp_869_:
{
if (v___y_870_ == 0)
{
lean_object* v___x_871_; 
lean_del_object(v___x_867_);
lean_del_object(v___x_862_);
lean_dec_ref_known(v_e_845_, 2);
v___x_871_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__6(v_fst_856_, v_fst_864_, v_snd_865_, v_a_848_, v_a_849_, v_a_860_);
return v___x_871_;
}
else
{
lean_object* v___x_873_; 
lean_dec(v_fst_864_);
lean_dec(v_fst_856_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v_e_845_);
v___x_873_ = v___x_867_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_e_845_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_snd_865_);
v___x_873_ = v_reuseFailAlloc_877_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_875_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_873_);
v___x_875_ = v___x_862_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_a_860_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_856_);
lean_dec_ref_known(v_e_845_, 2);
return v___x_858_;
}
}
else
{
lean_dec_ref_known(v_e_845_, 2);
lean_dec(v_offset_846_);
lean_dec_ref(v___x_840_);
return v___x_853_;
}
}
case 6:
{
lean_object* v_binderName_882_; lean_object* v_binderType_883_; lean_object* v_body_884_; uint8_t v_binderInfo_885_; lean_object* v___x_886_; 
v_binderName_882_ = lean_ctor_get(v_e_845_, 0);
v_binderType_883_ = lean_ctor_get(v_e_845_, 1);
v_body_884_ = lean_ctor_get(v_e_845_, 2);
v_binderInfo_885_ = lean_ctor_get_uint8(v_e_845_, sizeof(void*)*3 + 8);
lean_inc(v_offset_846_);
lean_inc_ref(v_binderType_883_);
lean_inc_ref(v___x_840_);
v___x_886_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_839_, v___x_840_, v___x_841_, v_start_842_, v_xs_843_, v___x_844_, v_binderType_883_, v_offset_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v_a_888_; lean_object* v_fst_889_; lean_object* v_snd_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
v_a_888_ = lean_ctor_get(v___x_886_, 1);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_886_, 2);
v_fst_889_ = lean_ctor_get(v_a_887_, 0);
lean_inc(v_fst_889_);
v_snd_890_ = lean_ctor_get(v_a_887_, 1);
lean_inc(v_snd_890_);
lean_dec(v_a_887_);
v___x_891_ = lean_unsigned_to_nat(1u);
v___x_892_ = lean_nat_add(v_offset_846_, v___x_891_);
lean_dec(v_offset_846_);
lean_inc_ref(v_body_884_);
v___x_893_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_839_, v___x_840_, v___x_841_, v_start_842_, v_xs_843_, v___x_844_, v_body_884_, v___x_892_, v_snd_890_, v_a_848_, v_a_849_, v_a_888_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_916_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_a_895_ = lean_ctor_get(v___x_893_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_916_ == 0)
{
v___x_897_ = v___x_893_;
v_isShared_898_ = v_isSharedCheck_916_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_916_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_fst_899_; lean_object* v_snd_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_915_; 
v_fst_899_ = lean_ctor_get(v_a_894_, 0);
v_snd_900_ = lean_ctor_get(v_a_894_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v_a_894_);
if (v_isSharedCheck_915_ == 0)
{
v___x_902_ = v_a_894_;
v_isShared_903_ = v_isSharedCheck_915_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_snd_900_);
lean_inc(v_fst_899_);
lean_dec(v_a_894_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_915_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
uint8_t v___y_905_; uint8_t v___x_913_; 
v___x_913_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_883_, v_fst_889_);
if (v___x_913_ == 0)
{
v___y_905_ = v___x_913_;
goto v___jp_904_;
}
else
{
uint8_t v___x_914_; 
v___x_914_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_884_, v_fst_899_);
v___y_905_ = v___x_914_;
goto v___jp_904_;
}
v___jp_904_:
{
if (v___y_905_ == 0)
{
lean_object* v___x_906_; 
lean_inc(v_binderName_882_);
lean_del_object(v___x_902_);
lean_del_object(v___x_897_);
lean_dec_ref_known(v_e_845_, 3);
v___x_906_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__7(v_binderName_882_, v_binderInfo_885_, v_fst_889_, v_fst_899_, v_snd_900_, v_a_848_, v_a_849_, v_a_895_);
return v___x_906_;
}
else
{
lean_object* v___x_908_; 
lean_dec(v_fst_899_);
lean_dec(v_fst_889_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v_e_845_);
v___x_908_ = v___x_902_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_e_845_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_snd_900_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_910_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_908_);
v___x_910_ = v___x_897_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_a_895_);
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
}
}
else
{
lean_dec(v_fst_889_);
lean_dec_ref_known(v_e_845_, 3);
return v___x_893_;
}
}
else
{
lean_dec_ref_known(v_e_845_, 3);
lean_dec(v_offset_846_);
lean_dec_ref(v___x_840_);
return v___x_886_;
}
}
case 7:
{
lean_object* v_binderName_917_; lean_object* v_binderType_918_; lean_object* v_body_919_; uint8_t v_binderInfo_920_; lean_object* v___x_921_; 
v_binderName_917_ = lean_ctor_get(v_e_845_, 0);
v_binderType_918_ = lean_ctor_get(v_e_845_, 1);
v_body_919_ = lean_ctor_get(v_e_845_, 2);
v_binderInfo_920_ = lean_ctor_get_uint8(v_e_845_, sizeof(void*)*3 + 8);
lean_inc(v_offset_846_);
lean_inc_ref(v_binderType_918_);
lean_inc_ref(v___x_840_);
v___x_921_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_839_, v___x_840_, v___x_841_, v_start_842_, v_xs_843_, v___x_844_, v_binderType_918_, v_offset_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v_a_923_; lean_object* v_fst_924_; lean_object* v_snd_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
v_a_923_ = lean_ctor_get(v___x_921_, 1);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_921_, 2);
v_fst_924_ = lean_ctor_get(v_a_922_, 0);
lean_inc(v_fst_924_);
v_snd_925_ = lean_ctor_get(v_a_922_, 1);
lean_inc(v_snd_925_);
lean_dec(v_a_922_);
v___x_926_ = lean_unsigned_to_nat(1u);
v___x_927_ = lean_nat_add(v_offset_846_, v___x_926_);
lean_dec(v_offset_846_);
lean_inc_ref(v_body_919_);
v___x_928_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_839_, v___x_840_, v___x_841_, v_start_842_, v_xs_843_, v___x_844_, v_body_919_, v___x_927_, v_snd_925_, v_a_848_, v_a_849_, v_a_923_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_951_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
v_a_930_ = lean_ctor_get(v___x_928_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_951_ == 0)
{
v___x_932_ = v___x_928_;
v_isShared_933_ = v_isSharedCheck_951_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_inc(v_a_929_);
lean_dec(v___x_928_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_951_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_fst_934_; lean_object* v_snd_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_950_; 
v_fst_934_ = lean_ctor_get(v_a_929_, 0);
v_snd_935_ = lean_ctor_get(v_a_929_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_a_929_);
if (v_isSharedCheck_950_ == 0)
{
v___x_937_ = v_a_929_;
v_isShared_938_ = v_isSharedCheck_950_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_snd_935_);
lean_inc(v_fst_934_);
lean_dec(v_a_929_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_950_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
uint8_t v___y_940_; uint8_t v___x_948_; 
v___x_948_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_918_, v_fst_924_);
if (v___x_948_ == 0)
{
v___y_940_ = v___x_948_;
goto v___jp_939_;
}
else
{
uint8_t v___x_949_; 
v___x_949_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_919_, v_fst_934_);
v___y_940_ = v___x_949_;
goto v___jp_939_;
}
v___jp_939_:
{
if (v___y_940_ == 0)
{
lean_object* v___x_941_; 
lean_inc(v_binderName_917_);
lean_del_object(v___x_937_);
lean_del_object(v___x_932_);
lean_dec_ref_known(v_e_845_, 3);
v___x_941_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__8(v_binderName_917_, v_binderInfo_920_, v_fst_924_, v_fst_934_, v_snd_935_, v_a_848_, v_a_849_, v_a_930_);
return v___x_941_;
}
else
{
lean_object* v___x_943_; 
lean_dec(v_fst_934_);
lean_dec(v_fst_924_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v_e_845_);
v___x_943_ = v___x_937_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_e_845_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_snd_935_);
v___x_943_ = v_reuseFailAlloc_947_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_945_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_943_);
v___x_945_ = v___x_932_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_a_930_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_924_);
lean_dec_ref_known(v_e_845_, 3);
return v___x_928_;
}
}
else
{
lean_dec_ref_known(v_e_845_, 3);
lean_dec(v_offset_846_);
lean_dec_ref(v___x_840_);
return v___x_921_;
}
}
case 8:
{
lean_object* v_declName_952_; lean_object* v_type_953_; lean_object* v_value_954_; lean_object* v_body_955_; uint8_t v_nondep_956_; lean_object* v___x_957_; 
v_declName_952_ = lean_ctor_get(v_e_845_, 0);
v_type_953_ = lean_ctor_get(v_e_845_, 1);
v_value_954_ = lean_ctor_get(v_e_845_, 2);
v_body_955_ = lean_ctor_get(v_e_845_, 3);
v_nondep_956_ = lean_ctor_get_uint8(v_e_845_, sizeof(void*)*4 + 8);
lean_inc(v_offset_846_);
lean_inc_ref(v_type_953_);
lean_inc_ref(v___x_840_);
v___x_957_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_839_, v___x_840_, v___x_841_, v_start_842_, v_xs_843_, v___x_844_, v_type_953_, v_offset_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v_a_959_; lean_object* v_fst_960_; lean_object* v_snd_961_; lean_object* v___x_962_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
v_a_959_ = lean_ctor_get(v___x_957_, 1);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_957_, 2);
v_fst_960_ = lean_ctor_get(v_a_958_, 0);
lean_inc(v_fst_960_);
v_snd_961_ = lean_ctor_get(v_a_958_, 1);
lean_inc(v_snd_961_);
lean_dec(v_a_958_);
lean_inc(v_offset_846_);
lean_inc_ref(v_value_954_);
lean_inc_ref(v___x_840_);
v___x_962_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_839_, v___x_840_, v___x_841_, v_start_842_, v_xs_843_, v___x_844_, v_value_954_, v_offset_846_, v_snd_961_, v_a_848_, v_a_849_, v_a_959_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v_a_964_; lean_object* v_fst_965_; lean_object* v_snd_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
v_a_964_ = lean_ctor_get(v___x_962_, 1);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_962_, 2);
v_fst_965_ = lean_ctor_get(v_a_963_, 0);
lean_inc(v_fst_965_);
v_snd_966_ = lean_ctor_get(v_a_963_, 1);
lean_inc(v_snd_966_);
lean_dec(v_a_963_);
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = lean_nat_add(v_offset_846_, v___x_967_);
lean_dec(v_offset_846_);
lean_inc_ref(v_body_955_);
v___x_969_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_839_, v___x_840_, v___x_841_, v_start_842_, v_xs_843_, v___x_844_, v_body_955_, v___x_968_, v_snd_966_, v_a_848_, v_a_849_, v_a_964_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_994_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_a_971_ = lean_ctor_get(v___x_969_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_994_ == 0)
{
v___x_973_ = v___x_969_;
v_isShared_974_ = v_isSharedCheck_994_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_994_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v_fst_975_; lean_object* v_snd_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_993_; 
v_fst_975_ = lean_ctor_get(v_a_970_, 0);
v_snd_976_ = lean_ctor_get(v_a_970_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v_a_970_);
if (v_isSharedCheck_993_ == 0)
{
v___x_978_ = v_a_970_;
v_isShared_979_ = v_isSharedCheck_993_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_snd_976_);
lean_inc(v_fst_975_);
lean_dec(v_a_970_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_993_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
uint8_t v___y_981_; uint8_t v___x_991_; 
v___x_991_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_953_, v_fst_960_);
if (v___x_991_ == 0)
{
v___y_981_ = v___x_991_;
goto v___jp_980_;
}
else
{
uint8_t v___x_992_; 
v___x_992_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_954_, v_fst_965_);
v___y_981_ = v___x_992_;
goto v___jp_980_;
}
v___jp_980_:
{
if (v___y_981_ == 0)
{
lean_object* v___x_982_; 
lean_inc(v_declName_952_);
lean_del_object(v___x_978_);
lean_del_object(v___x_973_);
lean_dec_ref_known(v_e_845_, 4);
v___x_982_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_952_, v_fst_960_, v_fst_965_, v_fst_975_, v_nondep_956_, v_snd_976_, v_a_848_, v_a_849_, v_a_971_);
return v___x_982_;
}
else
{
uint8_t v___x_983_; 
v___x_983_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_955_, v_fst_975_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; 
lean_inc(v_declName_952_);
lean_del_object(v___x_978_);
lean_del_object(v___x_973_);
lean_dec_ref_known(v_e_845_, 4);
v___x_984_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__9(v_declName_952_, v_fst_960_, v_fst_965_, v_fst_975_, v_nondep_956_, v_snd_976_, v_a_848_, v_a_849_, v_a_971_);
return v___x_984_;
}
else
{
lean_object* v___x_986_; 
lean_dec(v_fst_975_);
lean_dec(v_fst_965_);
lean_dec(v_fst_960_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v_e_845_);
v___x_986_ = v___x_978_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_e_845_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_snd_976_);
v___x_986_ = v_reuseFailAlloc_990_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_988_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_986_);
v___x_988_ = v___x_973_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_a_971_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
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
lean_dec(v_fst_965_);
lean_dec(v_fst_960_);
lean_dec_ref_known(v_e_845_, 4);
return v___x_969_;
}
}
else
{
lean_dec(v_fst_960_);
lean_dec_ref_known(v_e_845_, 4);
lean_dec(v_offset_846_);
lean_dec_ref(v___x_840_);
return v___x_962_;
}
}
else
{
lean_dec_ref_known(v_e_845_, 4);
lean_dec(v_offset_846_);
lean_dec_ref(v___x_840_);
return v___x_957_;
}
}
case 10:
{
lean_object* v_data_995_; lean_object* v_expr_996_; lean_object* v___x_997_; 
v_data_995_ = lean_ctor_get(v_e_845_, 0);
v_expr_996_ = lean_ctor_get(v_e_845_, 1);
lean_inc_ref(v_expr_996_);
v___x_997_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_839_, v___x_840_, v___x_841_, v_start_842_, v_xs_843_, v___x_844_, v_expr_996_, v_offset_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1017_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_a_999_ = lean_ctor_get(v___x_997_, 1);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1001_ = v___x_997_;
v_isShared_1002_ = v_isSharedCheck_1017_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1017_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v_fst_1003_; lean_object* v_snd_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1016_; 
v_fst_1003_ = lean_ctor_get(v_a_998_, 0);
v_snd_1004_ = lean_ctor_get(v_a_998_, 1);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_a_998_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1006_ = v_a_998_;
v_isShared_1007_ = v_isSharedCheck_1016_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_snd_1004_);
lean_inc(v_fst_1003_);
lean_dec(v_a_998_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1016_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
uint8_t v___x_1008_; 
v___x_1008_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_996_, v_fst_1003_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
lean_inc(v_data_995_);
lean_del_object(v___x_1006_);
lean_del_object(v___x_1001_);
lean_dec_ref_known(v_e_845_, 2);
v___x_1009_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__10(v_data_995_, v_fst_1003_, v_snd_1004_, v_a_848_, v_a_849_, v_a_999_);
return v___x_1009_;
}
else
{
lean_object* v___x_1011_; 
lean_dec(v_fst_1003_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v_e_845_);
v___x_1011_ = v___x_1006_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_e_845_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_snd_1004_);
v___x_1011_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1013_; 
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1011_);
v___x_1013_ = v___x_1001_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_a_999_);
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
else
{
lean_dec_ref_known(v_e_845_, 2);
return v___x_997_;
}
}
case 11:
{
lean_object* v_typeName_1018_; lean_object* v_idx_1019_; lean_object* v_struct_1020_; lean_object* v___x_1021_; 
v_typeName_1018_ = lean_ctor_get(v_e_845_, 0);
v_idx_1019_ = lean_ctor_get(v_e_845_, 1);
v_struct_1020_ = lean_ctor_get(v_e_845_, 2);
lean_inc_ref(v_struct_1020_);
v___x_1021_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_839_, v___x_840_, v___x_841_, v_start_842_, v_xs_843_, v___x_844_, v_struct_1020_, v_offset_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1041_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_a_1023_ = lean_ctor_get(v___x_1021_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1025_ = v___x_1021_;
v_isShared_1026_ = v_isSharedCheck_1041_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1041_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_fst_1027_; lean_object* v_snd_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1040_; 
v_fst_1027_ = lean_ctor_get(v_a_1022_, 0);
v_snd_1028_ = lean_ctor_get(v_a_1022_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_a_1022_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1030_ = v_a_1022_;
v_isShared_1031_ = v_isSharedCheck_1040_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_snd_1028_);
lean_inc(v_fst_1027_);
lean_dec(v_a_1022_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1040_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
uint8_t v___x_1032_; 
v___x_1032_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1020_, v_fst_1027_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
lean_inc(v_idx_1019_);
lean_inc(v_typeName_1018_);
lean_del_object(v___x_1030_);
lean_del_object(v___x_1025_);
lean_dec_ref_known(v_e_845_, 3);
v___x_1033_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__11(v_typeName_1018_, v_idx_1019_, v_fst_1027_, v_snd_1028_, v_a_848_, v_a_849_, v_a_1023_);
return v___x_1033_;
}
else
{
lean_object* v___x_1035_; 
lean_dec(v_fst_1027_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v_e_845_);
v___x_1035_ = v___x_1030_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_e_845_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_snd_1028_);
v___x_1035_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1035_);
v___x_1037_ = v___x_1025_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_a_1023_);
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
else
{
lean_dec_ref_known(v_e_845_, 3);
return v___x_1021_;
}
}
default: 
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_dec(v_offset_846_);
lean_dec_ref(v_e_845_);
lean_dec_ref(v___x_840_);
v___x_1042_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__3);
v___x_1043_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__12(v___x_1042_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
return v___x_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(lean_object* v_minIndex_1044_, lean_object* v___x_1045_, lean_object* v___x_1046_, lean_object* v_start_1047_, lean_object* v_xs_1048_, lean_object* v___x_1049_, lean_object* v_e_1050_, lean_object* v_offset_1051_, lean_object* v_a_1052_, uint8_t v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_key_1056_; lean_object* v_a_1058_; lean_object* v___y_1072_; lean_object* v___y_1077_; lean_object* v___x_1082_; 
lean_inc(v_offset_1051_);
lean_inc_ref(v_e_1050_);
v_key_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1056_, 0, v_e_1050_);
lean_ctor_set(v_key_1056_, 1, v_offset_1051_);
v___x_1082_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_a_1052_, v_key_1056_);
if (lean_obj_tag(v___x_1082_) == 1)
{
lean_object* v_val_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec_ref_known(v_key_1056_, 2);
lean_dec(v_offset_1051_);
lean_dec_ref(v_e_1050_);
lean_dec_ref(v___x_1045_);
v_val_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_val_1083_);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_val_1083_);
lean_ctor_set(v___x_1084_, 1, v_a_1052_);
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set(v___x_1085_, 1, v_a_1055_);
return v___x_1085_;
}
else
{
lean_dec(v___x_1082_);
switch(lean_obj_tag(v_e_1050_))
{
case 1:
{
lean_object* v_fvarId_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_dec_ref(v___x_1045_);
v_fvarId_1086_ = lean_ctor_get(v_e_1050_, 0);
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = lean_unsigned_to_nat(1u);
v___x_1089_ = lean_nat_sub(v___x_1046_, v___x_1088_);
v___x_1090_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_1047_, v_xs_1048_, v_fvarId_1086_, v___x_1087_, v___x_1089_);
if (lean_obj_tag(v___x_1090_) == 1)
{
lean_object* v_val_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_dec_ref_known(v_e_1050_, 1);
v_val_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_val_1091_);
lean_dec_ref_known(v___x_1090_, 1);
v___x_1092_ = lean_nat_add(v_offset_1051_, v_val_1091_);
lean_dec(v_val_1091_);
lean_dec(v_offset_1051_);
v___x_1093_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v___x_1092_, v_a_1055_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v_a_1095_; lean_object* v___x_1096_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
v_a_1095_ = lean_ctor_get(v___x_1093_, 1);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1093_, 2);
v___x_1096_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1056_, v_a_1094_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1095_);
return v___x_1096_;
}
else
{
lean_object* v_a_1097_; lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref_known(v_key_1056_, 2);
lean_dec_ref(v_a_1052_);
v_a_1097_ = lean_ctor_get(v___x_1093_, 0);
v_a_1098_ = lean_ctor_get(v___x_1093_, 1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1093_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_inc(v_a_1097_);
lean_dec(v___x_1093_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1097_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
lean_object* v___x_1106_; 
lean_dec(v___x_1090_);
lean_dec(v_offset_1051_);
v___x_1106_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1056_, v_e_1050_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
return v___x_1106_;
}
}
case 9:
{
lean_object* v___x_1107_; 
lean_dec(v_offset_1051_);
lean_dec_ref(v___x_1045_);
v___x_1107_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1056_, v_e_1050_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
return v___x_1107_;
}
case 2:
{
lean_object* v___x_1108_; 
lean_dec(v_offset_1051_);
lean_dec_ref(v___x_1045_);
v___x_1108_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1056_, v_e_1050_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
return v___x_1108_;
}
case 0:
{
lean_object* v___x_1109_; 
lean_dec(v_offset_1051_);
lean_dec_ref(v___x_1045_);
v___x_1109_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1056_, v_e_1050_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
return v___x_1109_;
}
case 4:
{
lean_object* v___x_1110_; 
lean_dec(v_offset_1051_);
lean_dec_ref(v___x_1045_);
v___x_1110_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1056_, v_e_1050_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
return v___x_1110_;
}
case 3:
{
lean_object* v___x_1111_; 
lean_dec(v_offset_1051_);
lean_dec_ref(v___x_1045_);
v___x_1111_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1056_, v_e_1050_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
return v___x_1111_;
}
default: 
{
uint8_t v___x_1112_; uint8_t v___x_1113_; 
v___x_1112_ = l_Lean_Expr_hasFVar(v_e_1050_);
v___x_1113_ = lean_bool_not(v___x_1112_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v___x_1049_, v_e_1050_);
if (lean_obj_tag(v___x_1114_) == 1)
{
lean_object* v_val_1115_; 
v_val_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_val_1115_);
lean_dec_ref_known(v___x_1114_, 1);
if (lean_obj_tag(v_val_1115_) == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1117_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v___x_1116_);
v___y_1077_ = v___x_1117_;
goto v___jp_1076_;
}
else
{
lean_object* v_val_1118_; 
v_val_1118_ = lean_ctor_get(v_val_1115_, 0);
lean_inc(v_val_1118_);
lean_dec_ref_known(v_val_1115_, 1);
v___y_1077_ = v_val_1118_;
goto v___jp_1076_;
}
}
else
{
lean_dec(v___x_1114_);
v_a_1058_ = v_a_1055_;
goto v___jp_1057_;
}
}
else
{
lean_object* v___x_1119_; 
lean_dec(v_offset_1051_);
lean_dec_ref(v___x_1045_);
v___x_1119_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1056_, v_e_1050_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
return v___x_1119_;
}
}
}
}
v___jp_1057_:
{
switch(lean_obj_tag(v_e_1050_))
{
case 9:
{
lean_object* v___x_1059_; 
lean_dec(v_offset_1051_);
lean_dec_ref(v___x_1045_);
v___x_1059_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1056_, v_e_1050_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1058_);
return v___x_1059_;
}
case 2:
{
lean_object* v___x_1060_; 
lean_dec(v_offset_1051_);
lean_dec_ref(v___x_1045_);
v___x_1060_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1056_, v_e_1050_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1058_);
return v___x_1060_;
}
case 0:
{
lean_object* v___x_1061_; 
lean_dec(v_offset_1051_);
lean_dec_ref(v___x_1045_);
v___x_1061_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1056_, v_e_1050_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1058_);
return v___x_1061_;
}
case 1:
{
lean_object* v___x_1062_; 
lean_dec(v_offset_1051_);
lean_dec_ref(v___x_1045_);
v___x_1062_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1056_, v_e_1050_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1058_);
return v___x_1062_;
}
case 4:
{
lean_object* v___x_1063_; 
lean_dec(v_offset_1051_);
lean_dec_ref(v___x_1045_);
v___x_1063_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1056_, v_e_1050_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1058_);
return v___x_1063_;
}
case 3:
{
lean_object* v___x_1064_; 
lean_dec(v_offset_1051_);
lean_dec_ref(v___x_1045_);
v___x_1064_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1056_, v_e_1050_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1058_);
return v___x_1064_;
}
default: 
{
lean_object* v___x_1065_; 
v___x_1065_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v_minIndex_1044_, v___x_1045_, v___x_1046_, v_start_1047_, v_xs_1048_, v___x_1049_, v_e_1050_, v_offset_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1058_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v_a_1067_; lean_object* v_fst_1068_; lean_object* v_snd_1069_; lean_object* v___x_1070_; 
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
v___x_1070_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1056_, v_fst_1068_, v_snd_1069_, v_a_1053_, v_a_1054_, v_a_1067_);
return v___x_1070_;
}
else
{
lean_dec_ref_known(v_key_1056_, 2);
return v___x_1065_;
}
}
}
}
v___jp_1071_:
{
lean_object* v_maxIndex_1073_; uint8_t v___x_1074_; 
v_maxIndex_1073_ = l_Lean_LocalDecl_index(v___y_1072_);
lean_dec_ref(v___y_1072_);
v___x_1074_ = lean_nat_dec_lt(v_maxIndex_1073_, v_minIndex_1044_);
lean_dec(v_maxIndex_1073_);
if (v___x_1074_ == 0)
{
v_a_1058_ = v_a_1055_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1075_; 
lean_dec(v_offset_1051_);
lean_dec_ref(v___x_1045_);
v___x_1075_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1056_, v_e_1050_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
return v___x_1075_;
}
}
v___jp_1076_:
{
lean_object* v___x_1078_; 
lean_inc_ref(v___x_1045_);
v___x_1078_ = lean_local_ctx_find(v___x_1045_, v___y_1077_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1080_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1079_);
v___y_1072_ = v___x_1080_;
goto v___jp_1071_;
}
else
{
lean_object* v_val_1081_; 
v_val_1081_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_val_1081_);
lean_dec_ref_known(v___x_1078_, 1);
v___y_1072_ = v_val_1081_;
goto v___jp_1071_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5___boxed(lean_object* v_minIndex_1120_, lean_object* v___x_1121_, lean_object* v___x_1122_, lean_object* v_start_1123_, lean_object* v_xs_1124_, lean_object* v___x_1125_, lean_object* v_e_1126_, lean_object* v_offset_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
uint8_t v_a_boxed_1132_; lean_object* v_res_1133_; 
v_a_boxed_1132_ = lean_unbox(v_a_1129_);
v_res_1133_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5(v_minIndex_1120_, v___x_1121_, v___x_1122_, v_start_1123_, v_xs_1124_, v___x_1125_, v_e_1126_, v_offset_1127_, v_a_1128_, v_a_boxed_1132_, v_a_1130_, v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec_ref(v___x_1125_);
lean_dec_ref(v_xs_1124_);
lean_dec(v_start_1123_);
lean_dec(v___x_1122_);
lean_dec(v_minIndex_1120_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___boxed(lean_object* v_minIndex_1134_, lean_object* v___x_1135_, lean_object* v___x_1136_, lean_object* v_start_1137_, lean_object* v_xs_1138_, lean_object* v___x_1139_, lean_object* v_e_1140_, lean_object* v_offset_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
uint8_t v_a_boxed_1146_; lean_object* v_res_1147_; 
v_a_boxed_1146_ = lean_unbox(v_a_1143_);
v_res_1147_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v_minIndex_1134_, v___x_1135_, v___x_1136_, v_start_1137_, v_xs_1138_, v___x_1139_, v_e_1140_, v_offset_1141_, v_a_1142_, v_a_boxed_1146_, v_a_1144_, v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec_ref(v___x_1139_);
lean_dec_ref(v_xs_1138_);
lean_dec(v_start_1137_);
lean_dec(v___x_1136_);
lean_dec(v_minIndex_1134_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___lam__0(lean_object* v_e_1148_, lean_object* v_lctx_1149_, lean_object* v___x_1150_, lean_object* v_start_1151_, lean_object* v_xs_1152_, lean_object* v_maxFVar_1153_, uint8_t v_debug_1154_, uint8_t v___x_1155_, lean_object* v___x_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1206_; lean_object* v___x_1227_; 
lean_inc_ref(v_lctx_1149_);
v___x_1227_ = lean_local_ctx_find(v_lctx_1149_, v___x_1156_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1229_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1228_);
v___y_1206_ = v___x_1229_;
goto v___jp_1205_;
}
else
{
lean_object* v_val_1230_; 
v_val_1230_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_val_1230_);
lean_dec_ref_known(v___x_1227_, 1);
v___y_1206_ = v_val_1230_;
goto v___jp_1205_;
}
v___jp_1159_:
{
switch(lean_obj_tag(v_e_1148_))
{
case 9:
{
lean_object* v___x_1162_; 
lean_dec(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v_lctx_1149_);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v_e_1148_);
lean_ctor_set(v___x_1162_, 1, v___y_1158_);
return v___x_1162_;
}
case 2:
{
lean_object* v___x_1163_; 
lean_dec(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v_lctx_1149_);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v_e_1148_);
lean_ctor_set(v___x_1163_, 1, v___y_1158_);
return v___x_1163_;
}
case 0:
{
lean_object* v___x_1164_; 
lean_dec(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v_lctx_1149_);
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v_e_1148_);
lean_ctor_set(v___x_1164_, 1, v___y_1158_);
return v___x_1164_;
}
case 1:
{
lean_object* v___x_1165_; 
lean_dec(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v_lctx_1149_);
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v_e_1148_);
lean_ctor_set(v___x_1165_, 1, v___y_1158_);
return v___x_1165_;
}
case 4:
{
lean_object* v___x_1166_; 
lean_dec(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v_lctx_1149_);
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v_e_1148_);
lean_ctor_set(v___x_1166_, 1, v___y_1158_);
return v___x_1166_;
}
case 3:
{
lean_object* v___x_1167_; 
lean_dec(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v_lctx_1149_);
v___x_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1167_, 0, v_e_1148_);
lean_ctor_set(v___x_1167_, 1, v___y_1158_);
return v___x_1167_;
}
default: 
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1168_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0);
lean_inc(v___y_1161_);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___y_1161_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v___y_1160_, v_lctx_1149_, v___x_1150_, v_start_1151_, v_xs_1152_, v_maxFVar_1153_, v_e_1148_, v___y_1161_, v___x_1169_, v_debug_1154_, v___y_1157_, v___y_1158_);
lean_dec(v___y_1160_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1180_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_a_1172_ = lean_ctor_get(v___x_1170_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1174_ = v___x_1170_;
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_fst_1176_; lean_object* v___x_1178_; 
v_fst_1176_ = lean_ctor_get(v_a_1171_, 0);
lean_inc(v_fst_1176_);
lean_dec(v_a_1171_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v_fst_1176_);
v___x_1178_ = v___x_1174_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_fst_1176_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_a_1172_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
v_a_1181_ = lean_ctor_get(v___x_1170_, 0);
v_a_1182_ = lean_ctor_get(v___x_1170_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1170_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_inc(v_a_1181_);
lean_dec(v___x_1170_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1181_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
}
v___jp_1190_:
{
lean_object* v_maxIndex_1194_; uint8_t v___x_1195_; 
v_maxIndex_1194_ = l_Lean_LocalDecl_index(v___y_1193_);
lean_dec_ref(v___y_1193_);
v___x_1195_ = lean_nat_dec_lt(v_maxIndex_1194_, v___y_1191_);
lean_dec(v_maxIndex_1194_);
if (v___x_1195_ == 0)
{
v___y_1160_ = v___y_1191_;
v___y_1161_ = v___y_1192_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1196_; 
lean_dec(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v_lctx_1149_);
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v_e_1148_);
lean_ctor_set(v___x_1196_, 1, v___y_1158_);
return v___x_1196_;
}
}
v___jp_1197_:
{
lean_object* v___x_1201_; 
lean_inc_ref(v_lctx_1149_);
v___x_1201_ = lean_local_ctx_find(v_lctx_1149_, v___y_1200_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1203_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(v___x_1202_);
v___y_1191_ = v___y_1198_;
v___y_1192_ = v___y_1199_;
v___y_1193_ = v___x_1203_;
goto v___jp_1190_;
}
else
{
lean_object* v_val_1204_; 
v_val_1204_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_val_1204_);
lean_dec_ref_known(v___x_1201_, 1);
v___y_1191_ = v___y_1198_;
v___y_1192_ = v___y_1199_;
v___y_1193_ = v_val_1204_;
goto v___jp_1190_;
}
}
v___jp_1205_:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1148_))
{
case 1:
{
lean_object* v_fvarId_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec_ref(v___y_1206_);
lean_dec_ref(v_lctx_1149_);
v_fvarId_1208_ = lean_ctor_get(v_e_1148_, 0);
v___x_1209_ = lean_unsigned_to_nat(1u);
v___x_1210_ = lean_nat_sub(v___x_1150_, v___x_1209_);
v___x_1211_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_1151_, v_xs_1152_, v_fvarId_1208_, v___x_1207_, v___x_1210_);
if (lean_obj_tag(v___x_1211_) == 1)
{
lean_object* v_val_1212_; lean_object* v___x_1213_; 
lean_dec_ref_known(v_e_1148_, 1);
v_val_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_val_1212_);
lean_dec_ref_known(v___x_1211_, 1);
v___x_1213_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1___redArg(v_val_1212_, v___y_1158_);
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; 
lean_dec(v___x_1211_);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v_e_1148_);
lean_ctor_set(v___x_1214_, 1, v___y_1158_);
return v___x_1214_;
}
}
case 9:
{
lean_object* v___x_1215_; 
lean_dec_ref(v___y_1206_);
lean_dec_ref(v_lctx_1149_);
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v_e_1148_);
lean_ctor_set(v___x_1215_, 1, v___y_1158_);
return v___x_1215_;
}
case 2:
{
lean_object* v___x_1216_; 
lean_dec_ref(v___y_1206_);
lean_dec_ref(v_lctx_1149_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_e_1148_);
lean_ctor_set(v___x_1216_, 1, v___y_1158_);
return v___x_1216_;
}
case 0:
{
lean_object* v___x_1217_; 
lean_dec_ref(v___y_1206_);
lean_dec_ref(v_lctx_1149_);
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v_e_1148_);
lean_ctor_set(v___x_1217_, 1, v___y_1158_);
return v___x_1217_;
}
case 4:
{
lean_object* v___x_1218_; 
lean_dec_ref(v___y_1206_);
lean_dec_ref(v_lctx_1149_);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v_e_1148_);
lean_ctor_set(v___x_1218_, 1, v___y_1158_);
return v___x_1218_;
}
case 3:
{
lean_object* v___x_1219_; 
lean_dec_ref(v___y_1206_);
lean_dec_ref(v_lctx_1149_);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v_e_1148_);
lean_ctor_set(v___x_1219_, 1, v___y_1158_);
return v___x_1219_;
}
default: 
{
if (v___x_1155_ == 0)
{
lean_object* v_minIndex_1220_; lean_object* v___x_1221_; 
v_minIndex_1220_ = l_Lean_LocalDecl_index(v___y_1206_);
lean_dec_ref(v___y_1206_);
v___x_1221_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_maxFVar_1153_, v_e_1148_);
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
v___y_1198_ = v_minIndex_1220_;
v___y_1199_ = v___x_1207_;
v___y_1200_ = v___x_1224_;
goto v___jp_1197_;
}
else
{
lean_object* v_val_1225_; 
v_val_1225_ = lean_ctor_get(v_val_1222_, 0);
lean_inc(v_val_1225_);
lean_dec_ref_known(v_val_1222_, 1);
v___y_1198_ = v_minIndex_1220_;
v___y_1199_ = v___x_1207_;
v___y_1200_ = v_val_1225_;
goto v___jp_1197_;
}
}
else
{
lean_dec(v___x_1221_);
v___y_1160_ = v_minIndex_1220_;
v___y_1161_ = v___x_1207_;
goto v___jp_1159_;
}
}
else
{
lean_object* v___x_1226_; 
lean_dec_ref(v___y_1206_);
lean_dec_ref(v_lctx_1149_);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v_e_1148_);
lean_ctor_set(v___x_1226_, 1, v___y_1158_);
return v___x_1226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___lam__0___boxed(lean_object* v_e_1231_, lean_object* v_lctx_1232_, lean_object* v___x_1233_, lean_object* v_start_1234_, lean_object* v_xs_1235_, lean_object* v_maxFVar_1236_, lean_object* v_debug_1237_, lean_object* v___x_1238_, lean_object* v___x_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
uint8_t v_debug_boxed_1242_; uint8_t v___x_27119__boxed_1243_; lean_object* v_res_1244_; 
v_debug_boxed_1242_ = lean_unbox(v_debug_1237_);
v___x_27119__boxed_1243_ = lean_unbox(v___x_1238_);
v_res_1244_ = l_Lean_Meta_Sym_abstractFVarsRange___lam__0(v_e_1231_, v_lctx_1232_, v___x_1233_, v_start_1234_, v_xs_1235_, v_maxFVar_1236_, v_debug_boxed_1242_, v___x_27119__boxed_1243_, v___x_1239_, v___y_1240_, v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec_ref(v_maxFVar_1236_);
lean_dec_ref(v_xs_1235_);
lean_dec(v_start_1234_);
lean_dec(v___x_1233_);
return v_res_1244_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_abstractFVarsRange___closed__2(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1247_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4___closed__2));
v___x_1248_ = lean_unsigned_to_nat(16u);
v___x_1249_ = lean_unsigned_to_nat(62u);
v___x_1250_ = ((lean_object*)(l_Lean_Meta_Sym_abstractFVarsRange___closed__1));
v___x_1251_ = ((lean_object*)(l_Lean_Meta_Sym_abstractFVarsRange___closed__0));
v___x_1252_ = l_mkPanicMessageWithDecl(v___x_1251_, v___x_1250_, v___x_1249_, v___x_1248_, v___x_1247_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange(lean_object* v_e_1253_, lean_object* v_start_1254_, lean_object* v_xs_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
uint8_t v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = l_Lean_Expr_hasFVar(v_e_1253_);
v___x_1264_ = lean_bool_not(v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1265_ = lean_array_get_size(v_xs_1255_);
v___x_1266_ = lean_nat_dec_lt(v_start_1254_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref(v_xs_1255_);
lean_dec(v_start_1254_);
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_e_1253_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v_lctx_1271_; lean_object* v_maxFVar_1272_; uint8_t v_debug_1273_; lean_object* v_env_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___f_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1268_ = lean_st_ref_get(v_a_1257_);
v___x_1269_ = lean_st_ref_get(v_a_1257_);
v___x_1270_ = lean_st_ref_get(v_a_1261_);
v_lctx_1271_ = lean_ctor_get(v_a_1258_, 2);
v_maxFVar_1272_ = lean_ctor_get(v___x_1268_, 1);
lean_inc_ref(v_maxFVar_1272_);
lean_dec(v___x_1268_);
v_debug_1273_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*11);
lean_dec(v___x_1269_);
v_env_1274_ = lean_ctor_get(v___x_1270_, 0);
lean_inc_ref(v_env_1274_);
lean_dec(v___x_1270_);
v___x_1275_ = lean_array_fget_borrowed(v_xs_1255_, v_start_1254_);
v___x_1276_ = l_Lean_Expr_fvarId_x21(v___x_1275_);
v___x_1277_ = lean_box(v_debug_1273_);
v___x_1278_ = lean_box(v___x_1264_);
lean_inc_ref(v_lctx_1271_);
v___f_1279_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_abstractFVarsRange___lam__0___boxed), 11, 9);
lean_closure_set(v___f_1279_, 0, v_e_1253_);
lean_closure_set(v___f_1279_, 1, v_lctx_1271_);
lean_closure_set(v___f_1279_, 2, v___x_1265_);
lean_closure_set(v___f_1279_, 3, v_start_1254_);
lean_closure_set(v___f_1279_, 4, v_xs_1255_);
lean_closure_set(v___f_1279_, 5, v_maxFVar_1272_);
lean_closure_set(v___f_1279_, 6, v___x_1277_);
lean_closure_set(v___f_1279_, 7, v___x_1278_);
lean_closure_set(v___f_1279_, 8, v___x_1276_);
v___x_1280_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1280_, 0, v_env_1274_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*1, v___x_1264_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*1 + 1, v___x_1264_);
v___x_1281_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1279_, v___x_1280_, v_a_1257_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1292_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1292_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1292_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
if (lean_obj_tag(v_a_1282_) == 0)
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec_ref_known(v_a_1282_, 1);
lean_del_object(v___x_1284_);
v___x_1286_ = lean_obj_once(&l_Lean_Meta_Sym_abstractFVarsRange___closed__2, &l_Lean_Meta_Sym_abstractFVarsRange___closed__2_once, _init_l_Lean_Meta_Sym_abstractFVarsRange___closed__2);
v___x_1287_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v___x_1286_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
return v___x_1287_;
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; 
v_a_1288_ = lean_ctor_get(v_a_1282_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v_a_1282_, 1);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v_a_1288_);
v___x_1290_ = v___x_1284_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
v_a_1293_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1281_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1281_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
else
{
lean_object* v___x_1301_; 
lean_dec_ref(v_xs_1255_);
lean_dec(v_start_1254_);
v___x_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1301_, 0, v_e_1253_);
return v___x_1301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___boxed(lean_object* v_e_1302_, lean_object* v_start_1303_, lean_object* v_xs_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1302_, v_start_1303_, v_xs_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(lean_object* v_00_u03b2_1313_, lean_object* v_x_1314_, lean_object* v_x_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_x_1314_, v_x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___boxed(lean_object* v_00_u03b2_1317_, lean_object* v_x_1318_, lean_object* v_x_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(v_00_u03b2_1317_, v_x_1318_, v_x_1319_);
lean_dec_ref(v_x_1319_);
lean_dec_ref(v_x_1318_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2(lean_object* v_00_u03b2_1321_, lean_object* v_x_1322_, size_t v_x_1323_, lean_object* v_x_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___redArg(v_x_1322_, v_x_1323_, v_x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1326_, lean_object* v_x_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_){
_start:
{
size_t v_x_27409__boxed_1330_; lean_object* v_res_1331_; 
v_x_27409__boxed_1330_ = lean_unbox_usize(v_x_1328_);
lean_dec(v_x_1328_);
v_res_1331_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2(v_00_u03b2_1326_, v_x_1327_, v_x_27409__boxed_1330_, v_x_1329_);
lean_dec_ref(v_x_1329_);
lean_dec_ref(v_x_1327_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_1332_, lean_object* v_keys_1333_, lean_object* v_vals_1334_, lean_object* v_heq_1335_, lean_object* v_i_1336_, lean_object* v_k_1337_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___redArg(v_keys_1333_, v_vals_1334_, v_i_1336_, v_k_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1339_, lean_object* v_keys_1340_, lean_object* v_vals_1341_, lean_object* v_heq_1342_, lean_object* v_i_1343_, lean_object* v_k_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2_spec__2_spec__5(v_00_u03b2_1339_, v_keys_1340_, v_vals_1341_, v_heq_1342_, v_i_1343_, v_k_1344_);
lean_dec_ref(v_k_1344_);
lean_dec_ref(v_vals_1341_);
lean_dec_ref(v_keys_1340_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_1346_, lean_object* v_m_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___redArg(v_m_1347_, v_a_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1350_, lean_object* v_m_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8(v_00_u03b2_1350_, v_m_1351_, v_a_1352_);
lean_dec_ref(v_a_1352_);
lean_dec_ref(v_m_1351_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16(lean_object* v_00_u03b2_1354_, lean_object* v_a_1355_, lean_object* v_x_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___redArg(v_a_1355_, v_x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16___boxed(lean_object* v_00_u03b2_1358_, lean_object* v_a_1359_, lean_object* v_x_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4_spec__5_spec__8_spec__16(v_00_u03b2_1358_, v_a_1359_, v_x_1360_);
lean_dec(v_x_1360_);
lean_dec_ref(v_a_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars(lean_object* v_e_1362_, lean_object* v_xs_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_unsigned_to_nat(0u);
v___x_1372_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1362_, v___x_1371_, v_xs_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___boxed(lean_object* v_e_1373_, lean_object* v_xs_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Lean_Meta_Sym_abstractFVars(v_e_1373_, v_xs_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(lean_object* v_x_1383_, uint8_t v_bi_1384_, lean_object* v_t_1385_, lean_object* v_b_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v___y_1395_; lean_object* v___x_1398_; uint8_t v_debug_1399_; 
v___x_1398_ = lean_st_ref_get(v___y_1388_);
v_debug_1399_ = lean_ctor_get_uint8(v___x_1398_, sizeof(void*)*11);
lean_dec(v___x_1398_);
if (v_debug_1399_ == 0)
{
v___y_1395_ = v___y_1388_;
goto v___jp_1394_;
}
else
{
lean_object* v___x_1400_; 
lean_inc_ref(v_t_1385_);
v___x_1400_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1385_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v___x_1401_; 
lean_dec_ref_known(v___x_1400_, 1);
lean_inc_ref(v_b_1386_);
v___x_1401_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_dec_ref_known(v___x_1401_, 1);
v___y_1395_ = v___y_1388_;
goto v___jp_1394_;
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_dec_ref(v_b_1386_);
lean_dec_ref(v_t_1385_);
lean_dec(v_x_1383_);
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
lean_dec_ref(v_b_1386_);
lean_dec_ref(v_t_1385_);
lean_dec(v_x_1383_);
v_a_1410_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1400_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1400_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
v___jp_1394_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = l_Lean_Expr_lam___override(v_x_1383_, v_t_1385_, v_b_1386_, v_bi_1384_);
v___x_1397_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1396_, v___y_1395_);
return v___x_1397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0___boxed(lean_object* v_x_1418_, lean_object* v_bi_1419_, lean_object* v_t_1420_, lean_object* v_b_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
uint8_t v_bi_boxed_1429_; lean_object* v_res_1430_; 
v_bi_boxed_1429_ = lean_unbox(v_bi_1419_);
v_res_1430_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v_x_1418_, v_bi_boxed_1429_, v_t_1420_, v_b_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(lean_object* v_xs_1431_, lean_object* v_i_1432_, lean_object* v_a_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_zero_1441_; uint8_t v_isZero_1442_; 
v_zero_1441_ = lean_unsigned_to_nat(0u);
v_isZero_1442_ = lean_nat_dec_eq(v_i_1432_, v_zero_1441_);
if (v_isZero_1442_ == 1)
{
lean_object* v___x_1443_; 
lean_dec(v_i_1432_);
lean_dec_ref(v_xs_1431_);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v_a_1433_);
return v___x_1443_;
}
else
{
lean_object* v_one_1444_; lean_object* v_n_1445_; lean_object* v___y_1447_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_one_1444_ = lean_unsigned_to_nat(1u);
v_n_1445_ = lean_nat_sub(v_i_1432_, v_one_1444_);
lean_dec(v_i_1432_);
v___x_1450_ = lean_array_fget_borrowed(v_xs_1431_, v_n_1445_);
v___x_1451_ = l_Lean_Expr_fvarId_x21(v___x_1450_);
v___x_1452_ = l_Lean_FVarId_getDecl___redArg(v___x_1451_, v___y_1436_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1453_);
lean_dec_ref_known(v___x_1452_, 1);
v___x_1454_ = l_Lean_LocalDecl_type(v_a_1453_);
lean_inc_ref(v_xs_1431_);
lean_inc(v_n_1445_);
v___x_1455_ = l_Lean_Meta_Sym_abstractFVarsRange(v___x_1454_, v_n_1445_, v_xs_1431_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
v___x_1457_ = l_Lean_LocalDecl_userName(v_a_1453_);
v___x_1458_ = l_Lean_LocalDecl_binderInfo(v_a_1453_);
lean_dec(v_a_1453_);
v___x_1459_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v___x_1457_, v___x_1458_, v_a_1456_, v_a_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
v___y_1447_ = v___x_1459_;
goto v___jp_1446_;
}
else
{
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1433_);
v___y_1447_ = v___x_1455_;
goto v___jp_1446_;
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec(v_n_1445_);
lean_dec_ref(v_a_1433_);
lean_dec_ref(v_xs_1431_);
v_a_1460_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1452_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1452_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
v___jp_1446_:
{
if (lean_obj_tag(v___y_1447_) == 0)
{
lean_object* v_a_1448_; 
v_a_1448_ = lean_ctor_get(v___y_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___y_1447_, 1);
v_i_1432_ = v_n_1445_;
v_a_1433_ = v_a_1448_;
goto _start;
}
else
{
lean_dec(v_n_1445_);
lean_dec_ref(v_xs_1431_);
return v___y_1447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg___boxed(lean_object* v_xs_1468_, lean_object* v_i_1469_, lean_object* v_a_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1468_, v_i_1469_, v_a_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS(lean_object* v_xs_1479_, lean_object* v_e_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_xs_1479_);
v___x_1489_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1480_, v___x_1488_, v_xs_1479_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1489_, 1);
v___x_1491_ = lean_array_get_size(v_xs_1479_);
v___x_1492_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1479_, v___x_1491_, v_a_1490_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
return v___x_1492_;
}
else
{
lean_dec_ref(v_xs_1479_);
return v___x_1489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS___boxed(lean_object* v_xs_1493_, lean_object* v_e_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_1493_, v_e_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(lean_object* v_xs_1503_, lean_object* v_n_1504_, lean_object* v_i_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1503_, v_i_1505_, v_a_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___boxed(lean_object* v_xs_1516_, lean_object* v_n_1517_, lean_object* v_i_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(v_xs_1516_, v_n_1517_, v_i_1518_, v_a_1519_, v_a_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v_n_1517_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(lean_object* v_x_1529_, uint8_t v_bi_1530_, lean_object* v_t_1531_, lean_object* v_b_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___y_1541_; lean_object* v___x_1544_; uint8_t v_debug_1545_; 
v___x_1544_ = lean_st_ref_get(v___y_1534_);
v_debug_1545_ = lean_ctor_get_uint8(v___x_1544_, sizeof(void*)*11);
lean_dec(v___x_1544_);
if (v_debug_1545_ == 0)
{
v___y_1541_ = v___y_1534_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1546_; 
lean_inc_ref(v_t_1531_);
v___x_1546_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1531_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v___x_1547_; 
lean_dec_ref_known(v___x_1546_, 1);
lean_inc_ref(v_b_1532_);
v___x_1547_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_dec_ref_known(v___x_1547_, 1);
v___y_1541_ = v___y_1534_;
goto v___jp_1540_;
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec_ref(v_b_1532_);
lean_dec_ref(v_t_1531_);
lean_dec(v_x_1529_);
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec_ref(v_b_1532_);
lean_dec_ref(v_t_1531_);
lean_dec(v_x_1529_);
v_a_1556_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1546_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1546_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
v___jp_1540_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = l_Lean_Expr_forallE___override(v_x_1529_, v_t_1531_, v_b_1532_, v_bi_1530_);
v___x_1543_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1542_, v___y_1541_);
return v___x_1543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0___boxed(lean_object* v_x_1564_, lean_object* v_bi_1565_, lean_object* v_t_1566_, lean_object* v_b_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
uint8_t v_bi_boxed_1575_; lean_object* v_res_1576_; 
v_bi_boxed_1575_ = lean_unbox(v_bi_1565_);
v_res_1576_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v_x_1564_, v_bi_boxed_1575_, v_t_1566_, v_b_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(lean_object* v_xs_1577_, lean_object* v_i_1578_, lean_object* v_a_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_zero_1587_; uint8_t v_isZero_1588_; 
v_zero_1587_ = lean_unsigned_to_nat(0u);
v_isZero_1588_ = lean_nat_dec_eq(v_i_1578_, v_zero_1587_);
if (v_isZero_1588_ == 1)
{
lean_object* v___x_1589_; 
lean_dec(v_i_1578_);
lean_dec_ref(v_xs_1577_);
v___x_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1589_, 0, v_a_1579_);
return v___x_1589_;
}
else
{
lean_object* v_one_1590_; lean_object* v_n_1591_; lean_object* v___y_1593_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v_one_1590_ = lean_unsigned_to_nat(1u);
v_n_1591_ = lean_nat_sub(v_i_1578_, v_one_1590_);
lean_dec(v_i_1578_);
v___x_1596_ = lean_array_fget_borrowed(v_xs_1577_, v_n_1591_);
v___x_1597_ = l_Lean_Expr_fvarId_x21(v___x_1596_);
v___x_1598_ = l_Lean_FVarId_getDecl___redArg(v___x_1597_, v___y_1582_, v___y_1584_, v___y_1585_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v___x_1600_ = l_Lean_LocalDecl_type(v_a_1599_);
lean_inc_ref(v_xs_1577_);
lean_inc(v_n_1591_);
v___x_1601_ = l_Lean_Meta_Sym_abstractFVarsRange(v___x_1600_, v_n_1591_, v_xs_1577_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; lean_object* v___x_1605_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1603_ = l_Lean_LocalDecl_userName(v_a_1599_);
v___x_1604_ = l_Lean_LocalDecl_binderInfo(v_a_1599_);
lean_dec(v_a_1599_);
v___x_1605_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v___x_1603_, v___x_1604_, v_a_1602_, v_a_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
v___y_1593_ = v___x_1605_;
goto v___jp_1592_;
}
else
{
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1579_);
v___y_1593_ = v___x_1601_;
goto v___jp_1592_;
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec(v_n_1591_);
lean_dec_ref(v_a_1579_);
lean_dec_ref(v_xs_1577_);
v_a_1606_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1598_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1598_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
v___jp_1592_:
{
if (lean_obj_tag(v___y_1593_) == 0)
{
lean_object* v_a_1594_; 
v_a_1594_ = lean_ctor_get(v___y_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___y_1593_, 1);
v_i_1578_ = v_n_1591_;
v_a_1579_ = v_a_1594_;
goto _start;
}
else
{
lean_dec(v_n_1591_);
lean_dec_ref(v_xs_1577_);
return v___y_1593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg___boxed(lean_object* v_xs_1614_, lean_object* v_i_1615_, lean_object* v_a_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1614_, v_i_1615_, v_a_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object* v_xs_1625_, lean_object* v_e_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_xs_1625_);
v___x_1635_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1626_, v___x_1634_, v_xs_1625_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1637_ = lean_array_get_size(v_xs_1625_);
v___x_1638_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1625_, v___x_1637_, v_a_1636_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
return v___x_1638_;
}
else
{
lean_dec_ref(v_xs_1625_);
return v___x_1635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS___boxed(lean_object* v_xs_1639_, lean_object* v_e_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_Meta_Sym_mkForallFVarsS(v_xs_1639_, v_e_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(lean_object* v_xs_1649_, lean_object* v_n_1650_, lean_object* v_i_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1649_, v_i_1651_, v_a_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___boxed(lean_object* v_xs_1662_, lean_object* v_n_1663_, lean_object* v_i_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(v_xs_1662_, v_n_1663_, v_i_1664_, v_a_1665_, v_a_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v_n_1663_);
return v_res_1674_;
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
