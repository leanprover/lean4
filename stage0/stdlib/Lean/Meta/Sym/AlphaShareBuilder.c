// Lean compiler output
// Module: Lean.Meta.Sym.AlphaShareBuilder
// Imports: public import Lean.Meta.Sym.SymM
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "__dummy__"};
static const lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 141, 137, 132, 208, 124, 31, 129)}};
static const lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Sym.AlphaShareBuilder"};
static const lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Sym.Internal.Sym.assertShared"};
static const lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "assertion violation: isSameExpr prev.expr e\n\n"};
static const lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Internal_Sym_share1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__1_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_isDebugEnabled___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__0_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__1_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__2_value)}};
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Sym.Internal.liftBuilderM"};
static const lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Meta.Sym.Internal.Builder.assertShared"};
static const lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 121, .m_capacity = 121, .m_length = 116, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Sym.AlphaShareBuilder.3401574005._hygCtx._hyg.9.0 ).set.contains ⟨e⟩\n\n"};
static const lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__2_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_map, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__3_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0_value)}};
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__4_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_pure, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__5_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_seqRight, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__4_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__5_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__2_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__6_value)}};
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__7_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_bind, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__7_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__8_value)}};
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Internal_Builder_share1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__11 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__11_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateAppS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Expr.updateAppS!"};
static const lean_object* l_Lean_Expr_updateAppS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateAppS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateAppS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "application expected"};
static const lean_object* l_Lean_Expr_updateAppS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateAppS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateAppS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateAppS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateMDataS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Expr.updateMDataS!"};
static const lean_object* l_Lean_Expr_updateMDataS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateMDataS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateMDataS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "mdata expected"};
static const lean_object* l_Lean_Expr_updateMDataS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateMDataS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateMDataS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateProjS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Expr.updateProjS!"};
static const lean_object* l_Lean_Expr_updateProjS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateProjS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateProjS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "proj expected"};
static const lean_object* l_Lean_Expr_updateProjS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateProjS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateProjS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateProjS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateForallS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Expr.updateForallS!"};
static const lean_object* l_Lean_Expr_updateForallS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateForallS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateForallS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "forall expected"};
static const lean_object* l_Lean_Expr_updateForallS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateForallS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateForallS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateForallS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateLambdaS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Expr.updateLambdaS!"};
static const lean_object* l_Lean_Expr_updateLambdaS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateLambdaS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateLambdaS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "lambda expected"};
static const lean_object* l_Lean_Expr_updateLambdaS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateLambdaS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateLambdaS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateLetS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Expr.updateLetS!"};
static const lean_object* l_Lean_Expr_updateLetS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateLetS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateLetS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "let expression expected"};
static const lean_object* l_Lean_Expr_updateLetS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateLetS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateLetS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateLetS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0(lean_object* v_share1_1_, lean_object* v_inst_2_, lean_object* v_e_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_share1_1_, v_e_3_);
v___x_5_ = lean_apply_2(v_inst_2_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1(lean_object* v_assertShared_6_, lean_object* v_inst_7_, lean_object* v_e_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_apply_1(v_assertShared_6_, v_e_8_);
v___x_10_ = lean_apply_2(v_inst_7_, lean_box(0), v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg(lean_object* v_inst_11_, lean_object* v_inst_12_){
_start:
{
lean_object* v_share1_13_; lean_object* v_assertShared_14_; lean_object* v_isDebugEnabled_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_25_; 
v_share1_13_ = lean_ctor_get(v_inst_12_, 0);
v_assertShared_14_ = lean_ctor_get(v_inst_12_, 1);
v_isDebugEnabled_15_ = lean_ctor_get(v_inst_12_, 2);
v_isSharedCheck_25_ = !lean_is_exclusive(v_inst_12_);
if (v_isSharedCheck_25_ == 0)
{
v___x_17_ = v_inst_12_;
v_isShared_18_ = v_isSharedCheck_25_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_isDebugEnabled_15_);
lean_inc(v_assertShared_14_);
lean_inc(v_share1_13_);
lean_dec(v_inst_12_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_25_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___f_19_; lean_object* v___f_20_; lean_object* v___x_21_; lean_object* v___x_23_; 
lean_inc_n(v_inst_11_, 2);
v___f_19_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_19_, 0, v_share1_13_);
lean_closure_set(v___f_19_, 1, v_inst_11_);
v___f_20_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1), 3, 2);
lean_closure_set(v___f_20_, 0, v_assertShared_14_);
lean_closure_set(v___f_20_, 1, v_inst_11_);
v___x_21_ = lean_apply_2(v_inst_11_, lean_box(0), v_isDebugEnabled_15_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 2, v___x_21_);
lean_ctor_set(v___x_17_, 1, v___f_20_);
lean_ctor_set(v___x_17_, 0, v___f_19_);
v___x_23_ = v___x_17_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___f_19_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v___f_20_);
lean_ctor_set(v_reuseFailAlloc_24_, 2, v___x_21_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift(lean_object* v_m_26_, lean_object* v_n_27_, lean_object* v_inst_28_, lean_object* v_inst_29_){
_start:
{
lean_object* v_share1_30_; lean_object* v_assertShared_31_; lean_object* v_isDebugEnabled_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_42_; 
v_share1_30_ = lean_ctor_get(v_inst_29_, 0);
v_assertShared_31_ = lean_ctor_get(v_inst_29_, 1);
v_isDebugEnabled_32_ = lean_ctor_get(v_inst_29_, 2);
v_isSharedCheck_42_ = !lean_is_exclusive(v_inst_29_);
if (v_isSharedCheck_42_ == 0)
{
v___x_34_ = v_inst_29_;
v_isShared_35_ = v_isSharedCheck_42_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_isDebugEnabled_32_);
lean_inc(v_assertShared_31_);
lean_inc(v_share1_30_);
lean_dec(v_inst_29_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_42_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___f_36_; lean_object* v___f_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc_n(v_inst_28_, 2);
v___f_36_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_36_, 0, v_share1_30_);
lean_closure_set(v___f_36_, 1, v_inst_28_);
v___f_37_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1), 3, 2);
lean_closure_set(v___f_37_, 0, v_assertShared_31_);
lean_closure_set(v___f_37_, 1, v_inst_28_);
v___x_38_ = lean_apply_2(v_inst_28_, lean_box(0), v_isDebugEnabled_32_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 2, v___x_38_);
lean_ctor_set(v___x_34_, 1, v___f_37_);
lean_ctor_set(v___x_34_, 0, v___f_36_);
v___x_40_ = v___x_34_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___f_36_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v___f_37_);
lean_ctor_set(v_reuseFailAlloc_41_, 2, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_box(0);
v___x_47_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__1));
v___x_48_ = l_Lean_mkConst(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy(void){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2, &l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2_once, _init_l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_50_, lean_object* v_x_51_, lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
lean_object* v_ks_54_; lean_object* v_vs_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_79_; 
v_ks_54_ = lean_ctor_get(v_x_50_, 0);
v_vs_55_ = lean_ctor_get(v_x_50_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v_x_50_);
if (v_isSharedCheck_79_ == 0)
{
v___x_57_ = v_x_50_;
v_isShared_58_ = v_isSharedCheck_79_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_vs_55_);
lean_inc(v_ks_54_);
lean_dec(v_x_50_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_79_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = lean_array_get_size(v_ks_54_);
v___x_60_ = lean_nat_dec_lt(v_x_51_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
lean_dec(v_x_51_);
v___x_61_ = lean_array_push(v_ks_54_, v_x_52_);
v___x_62_ = lean_array_push(v_vs_55_, v_x_53_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v___x_62_);
lean_ctor_set(v___x_57_, 0, v___x_61_);
v___x_64_ = v___x_57_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_61_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v___x_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
else
{
lean_object* v_k_x27_66_; uint8_t v___x_67_; 
v_k_x27_66_ = lean_array_fget_borrowed(v_ks_54_, v_x_51_);
v___x_67_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_52_, v_k_x27_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_69_; 
if (v_isShared_58_ == 0)
{
v___x_69_ = v___x_57_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_ks_54_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_vs_55_);
v___x_69_ = v_reuseFailAlloc_73_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_nat_add(v_x_51_, v___x_70_);
lean_dec(v_x_51_);
v_x_50_ = v___x_69_;
v_x_51_ = v___x_71_;
goto _start;
}
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_74_ = lean_array_fset(v_ks_54_, v_x_51_, v_x_52_);
v___x_75_ = lean_array_fset(v_vs_55_, v_x_51_, v_x_53_);
lean_dec(v_x_51_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v___x_75_);
lean_ctor_set(v___x_57_, 0, v___x_74_);
v___x_77_ = v___x_57_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_80_, lean_object* v_k_81_, lean_object* v_v_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_80_, v___x_83_, v_k_81_, v_v_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_85_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(lean_object* v_x_86_, size_t v_x_87_, size_t v_x_88_, lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v_es_91_; size_t v___x_92_; size_t v___x_93_; lean_object* v_j_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v_es_91_ = lean_ctor_get(v_x_86_, 0);
v___x_92_ = ((size_t)31ULL);
v___x_93_ = lean_usize_land(v_x_87_, v___x_92_);
v_j_94_ = lean_usize_to_nat(v___x_93_);
v___x_95_ = lean_array_get_size(v_es_91_);
v___x_96_ = lean_nat_dec_lt(v_j_94_, v___x_95_);
if (v___x_96_ == 0)
{
lean_dec(v_j_94_);
lean_dec(v_x_90_);
lean_dec_ref(v_x_89_);
return v_x_86_;
}
else
{
lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_135_; 
lean_inc_ref(v_es_91_);
v_isSharedCheck_135_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; 
v_unused_136_ = lean_ctor_get(v_x_86_, 0);
lean_dec(v_unused_136_);
v___x_98_ = v_x_86_;
v_isShared_99_ = v_isSharedCheck_135_;
goto v_resetjp_97_;
}
else
{
lean_dec(v_x_86_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_135_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v_v_100_; lean_object* v___x_101_; lean_object* v_xs_x27_102_; lean_object* v___y_104_; 
v_v_100_ = lean_array_fget(v_es_91_, v_j_94_);
v___x_101_ = lean_box(0);
v_xs_x27_102_ = lean_array_fset(v_es_91_, v_j_94_, v___x_101_);
switch(lean_obj_tag(v_v_100_))
{
case 0:
{
lean_object* v_key_109_; lean_object* v_val_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_120_; 
v_key_109_ = lean_ctor_get(v_v_100_, 0);
v_val_110_ = lean_ctor_get(v_v_100_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_v_100_);
if (v_isSharedCheck_120_ == 0)
{
v___x_112_ = v_v_100_;
v_isShared_113_ = v_isSharedCheck_120_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_val_110_);
lean_inc(v_key_109_);
lean_dec(v_v_100_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_120_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
uint8_t v___x_114_; 
v___x_114_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_89_, v_key_109_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; 
lean_del_object(v___x_112_);
v___x_115_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_109_, v_val_110_, v_x_89_, v_x_90_);
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
v___y_104_ = v___x_116_;
goto v___jp_103_;
}
else
{
lean_object* v___x_118_; 
lean_dec(v_val_110_);
lean_dec(v_key_109_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 1, v_x_90_);
lean_ctor_set(v___x_112_, 0, v_x_89_);
v___x_118_ = v___x_112_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_x_89_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_x_90_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
v___y_104_ = v___x_118_;
goto v___jp_103_;
}
}
}
}
case 1:
{
lean_object* v_node_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_133_; 
v_node_121_ = lean_ctor_get(v_v_100_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v_v_100_);
if (v_isSharedCheck_133_ == 0)
{
v___x_123_ = v_v_100_;
v_isShared_124_ = v_isSharedCheck_133_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_node_121_);
lean_dec(v_v_100_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_133_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
size_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_125_ = ((size_t)5ULL);
v___x_126_ = lean_usize_shift_right(v_x_87_, v___x_125_);
v___x_127_ = ((size_t)1ULL);
v___x_128_ = lean_usize_add(v_x_88_, v___x_127_);
v___x_129_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_node_121_, v___x_126_, v___x_128_, v_x_89_, v_x_90_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_129_);
v___x_131_ = v___x_123_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
v___y_104_ = v___x_131_;
goto v___jp_103_;
}
}
}
default: 
{
lean_object* v___x_134_; 
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_x_89_);
lean_ctor_set(v___x_134_, 1, v_x_90_);
v___y_104_ = v___x_134_;
goto v___jp_103_;
}
}
v___jp_103_:
{
lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_105_ = lean_array_fset(v_xs_x27_102_, v_j_94_, v___y_104_);
lean_dec(v_j_94_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_105_);
v___x_107_ = v___x_98_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
else
{
lean_object* v_ks_137_; lean_object* v_vs_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_156_; 
v_ks_137_ = lean_ctor_get(v_x_86_, 0);
v_vs_138_ = lean_ctor_get(v_x_86_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_156_ == 0)
{
v___x_140_ = v_x_86_;
v_isShared_141_ = v_isSharedCheck_156_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_vs_138_);
lean_inc(v_ks_137_);
lean_dec(v_x_86_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_156_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_ks_137_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_vs_138_);
v___x_143_ = v_reuseFailAlloc_155_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v_newNode_144_; size_t v___x_145_; uint8_t v___x_146_; 
v_newNode_144_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(v___x_143_, v_x_89_, v_x_90_);
v___x_145_ = ((size_t)7ULL);
v___x_146_ = lean_usize_dec_le(v___x_145_, v_x_88_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_147_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_144_);
v___x_148_ = lean_unsigned_to_nat(4u);
v___x_149_ = lean_nat_dec_lt(v___x_147_, v___x_148_);
lean_dec(v___x_147_);
if (v___x_149_ == 0)
{
lean_object* v_ks_150_; lean_object* v_vs_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_ks_150_ = lean_ctor_get(v_newNode_144_, 0);
lean_inc_ref(v_ks_150_);
v_vs_151_ = lean_ctor_get(v_newNode_144_, 1);
lean_inc_ref(v_vs_151_);
lean_dec_ref(v_newNode_144_);
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0);
v___x_154_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_x_88_, v_ks_150_, v_vs_151_, v___x_152_, v___x_153_);
lean_dec_ref(v_vs_151_);
lean_dec_ref(v_ks_150_);
return v___x_154_;
}
else
{
return v_newNode_144_;
}
}
else
{
return v_newNode_144_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_86_ = stack[0].m_obj;
size_t v_x_87_ = stack[1].m_num;
size_t v_x_88_ = stack[2].m_num;
lean_object* v_x_89_ = stack[3].m_obj;
lean_object* v_x_90_ = stack[4].m_obj;
lean_object* v_res_157_;
v_res_157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_86_, v_x_87_, v_x_88_, v_x_89_, v_x_90_);
stack->m_obj
 = v_res_157_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(size_t v_depth_158_, lean_object* v_keys_159_, lean_object* v_vals_160_, lean_object* v_i_161_, lean_object* v_entries_162_){
_start:
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_array_get_size(v_keys_159_);
v___x_164_ = lean_nat_dec_lt(v_i_161_, v___x_163_);
if (v___x_164_ == 0)
{
lean_dec(v_i_161_);
return v_entries_162_;
}
else
{
lean_object* v_k_165_; lean_object* v_v_166_; uint64_t v___x_167_; size_t v_h_168_; size_t v___x_169_; lean_object* v___x_170_; size_t v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v_h_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_k_165_ = lean_array_fget_borrowed(v_keys_159_, v_i_161_);
v_v_166_ = lean_array_fget_borrowed(v_vals_160_, v_i_161_);
v___x_167_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_165_);
v_h_168_ = lean_uint64_to_usize(v___x_167_);
v___x_169_ = ((size_t)5ULL);
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = ((size_t)1ULL);
v___x_172_ = lean_usize_sub(v_depth_158_, v___x_171_);
v___x_173_ = lean_usize_mul(v___x_169_, v___x_172_);
v_h_174_ = lean_usize_shift_right(v_h_168_, v___x_173_);
v___x_175_ = lean_nat_add(v_i_161_, v___x_170_);
lean_dec(v_i_161_);
lean_inc(v_v_166_);
lean_inc(v_k_165_);
v___x_176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_entries_162_, v_h_174_, v_depth_158_, v_k_165_, v_v_166_);
v_i_161_ = v___x_175_;
v_entries_162_ = v___x_176_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_158_ = stack[0].m_num;
lean_object* v_keys_159_ = stack[1].m_obj;
lean_object* v_vals_160_ = stack[2].m_obj;
lean_object* v_i_161_ = stack[3].m_obj;
lean_object* v_entries_162_ = stack[4].m_obj;
lean_object* v_res_178_;
v_res_178_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_158_, v_keys_159_, v_vals_160_, v_i_161_, v_entries_162_);
stack->m_obj
 = v_res_178_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_179_, lean_object* v_keys_180_, lean_object* v_vals_181_, lean_object* v_i_182_, lean_object* v_entries_183_){
_start:
{
size_t v_depth_boxed_184_; lean_object* v_res_185_; 
v_depth_boxed_184_ = lean_unbox_usize(v_depth_179_);
lean_dec(v_depth_179_);
v_res_185_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_184_, v_keys_180_, v_vals_181_, v_i_182_, v_entries_183_);
lean_dec_ref(v_vals_181_);
lean_dec_ref(v_keys_180_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___boxed(lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
size_t v_x_2110__boxed_191_; size_t v_x_2111__boxed_192_; lean_object* v_res_193_; 
v_x_2110__boxed_191_ = lean_unbox_usize(v_x_187_);
lean_dec(v_x_187_);
v_x_2111__boxed_192_ = lean_unbox_usize(v_x_188_);
lean_dec(v_x_188_);
v_res_193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_186_, v_x_2110__boxed_191_, v_x_2111__boxed_192_, v_x_189_, v_x_190_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
uint64_t v___x_197_; size_t v___x_198_; size_t v___x_199_; lean_object* v___x_200_; 
v___x_197_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_195_);
v___x_198_ = lean_uint64_to_usize(v___x_197_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_194_, v___x_198_, v___x_199_, v_x_195_, v_x_196_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(lean_object* v_keys_201_, lean_object* v_i_202_, lean_object* v_k_203_, lean_object* v_k_u2080_204_){
_start:
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_array_get_size(v_keys_201_);
v___x_206_ = lean_nat_dec_lt(v_i_202_, v___x_205_);
if (v___x_206_ == 0)
{
lean_dec(v_i_202_);
lean_inc_ref(v_k_u2080_204_);
return v_k_u2080_204_;
}
else
{
lean_object* v_k_x27_207_; uint8_t v___x_208_; 
v_k_x27_207_ = lean_array_fget_borrowed(v_keys_201_, v_i_202_);
v___x_208_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_203_, v_k_x27_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = lean_nat_add(v_i_202_, v___x_209_);
lean_dec(v_i_202_);
v_i_202_ = v___x_210_;
goto _start;
}
else
{
lean_dec(v_i_202_);
lean_inc(v_k_x27_207_);
return v_k_x27_207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg___boxed(lean_object* v_keys_212_, lean_object* v_i_213_, lean_object* v_k_214_, lean_object* v_k_u2080_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_212_, v_i_213_, v_k_214_, v_k_u2080_215_);
lean_dec_ref(v_k_u2080_215_);
lean_dec_ref(v_k_214_);
lean_dec_ref(v_keys_212_);
return v_res_216_;
}
}
lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(lean_object* v_x_217_, size_t v_x_218_, lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_217_) == 0)
{
lean_object* v_es_221_; lean_object* v___x_222_; size_t v___x_223_; size_t v___x_224_; lean_object* v_j_225_; lean_object* v___x_226_; 
v_es_221_ = lean_ctor_get(v_x_217_, 0);
v___x_222_ = lean_box(2);
v___x_223_ = ((size_t)31ULL);
v___x_224_ = lean_usize_land(v_x_218_, v___x_223_);
v_j_225_ = lean_usize_to_nat(v___x_224_);
v___x_226_ = lean_array_get_borrowed(v___x_222_, v_es_221_, v_j_225_);
lean_dec(v_j_225_);
switch(lean_obj_tag(v___x_226_))
{
case 0:
{
lean_object* v_key_227_; uint8_t v___x_228_; 
v_key_227_ = lean_ctor_get(v___x_226_, 0);
v___x_228_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_219_, v_key_227_);
if (v___x_228_ == 0)
{
lean_inc_ref(v_x_220_);
return v_x_220_;
}
else
{
lean_inc(v_key_227_);
return v_key_227_;
}
}
case 1:
{
lean_object* v_node_229_; size_t v___x_230_; size_t v___x_231_; 
v_node_229_ = lean_ctor_get(v___x_226_, 0);
v___x_230_ = ((size_t)5ULL);
v___x_231_ = lean_usize_shift_right(v_x_218_, v___x_230_);
v_x_217_ = v_node_229_;
v_x_218_ = v___x_231_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_220_);
return v_x_220_;
}
}
}
else
{
lean_object* v_ks_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_ks_233_ = lean_ctor_get(v_x_217_, 0);
v___x_234_ = lean_unsigned_to_nat(0u);
v___x_235_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_ks_233_, v___x_234_, v_x_219_, v_x_220_);
return v___x_235_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_217_ = stack[0].m_obj;
size_t v_x_218_ = stack[1].m_num;
lean_object* v_x_219_ = stack[2].m_obj;
lean_object* v_x_220_ = stack[3].m_obj;
lean_object* v_res_236_;
v_res_236_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_217_, v_x_218_, v_x_219_, v_x_220_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg___boxed(lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_x_239_, lean_object* v_x_240_){
_start:
{
size_t v_x_2385__boxed_241_; lean_object* v_res_242_; 
v_x_2385__boxed_241_ = lean_unbox_usize(v_x_238_);
lean_dec(v_x_238_);
v_res_242_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_237_, v_x_2385__boxed_241_, v_x_239_, v_x_240_);
lean_dec_ref(v_x_240_);
lean_dec_ref(v_x_239_);
lean_dec_ref(v_x_237_);
return v_res_242_;
}
}
static size_t _init_l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0(void){
_start:
{
lean_object* v___x_243_; size_t v___x_244_; 
v___x_243_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_244_ = lean_ptr_addr(v___x_243_);
return v___x_244_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object* v_e_245_, lean_object* v_a_246_){
_start:
{
lean_object* v___x_248_; lean_object* v_share_249_; lean_object* v___x_250_; uint64_t v___x_251_; size_t v___x_252_; lean_object* v___x_253_; size_t v___x_254_; size_t v___x_255_; uint8_t v___x_256_; 
v___x_248_ = lean_st_ref_get(v_a_246_);
v_share_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc_ref(v_share_249_);
lean_dec(v___x_248_);
v___x_250_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_251_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_245_);
v___x_252_ = lean_uint64_to_usize(v___x_251_);
v___x_253_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_249_, v___x_252_, v_e_245_, v___x_250_);
lean_dec_ref(v_share_249_);
v___x_254_ = lean_ptr_addr(v___x_253_);
v___x_255_ = lean_usize_once(&l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0, &l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0);
v___x_256_ = lean_usize_dec_eq(v___x_254_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
lean_dec_ref(v_e_245_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_253_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; lean_object* v_share_259_; lean_object* v_maxFVar_260_; lean_object* v_proofInstInfo_261_; lean_object* v_proofInstInfoFVar_262_; lean_object* v_inferType_263_; lean_object* v_getLevel_264_; lean_object* v_congrInfo_265_; lean_object* v_defEqI_266_; lean_object* v_extensions_267_; lean_object* v_issues_268_; lean_object* v_canon_269_; lean_object* v_instanceOverrides_270_; uint8_t v_debug_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_282_; 
lean_dec_ref(v___x_253_);
v___x_258_ = lean_st_ref_take(v_a_246_);
v_share_259_ = lean_ctor_get(v___x_258_, 0);
v_maxFVar_260_ = lean_ctor_get(v___x_258_, 1);
v_proofInstInfo_261_ = lean_ctor_get(v___x_258_, 2);
v_proofInstInfoFVar_262_ = lean_ctor_get(v___x_258_, 3);
v_inferType_263_ = lean_ctor_get(v___x_258_, 4);
v_getLevel_264_ = lean_ctor_get(v___x_258_, 5);
v_congrInfo_265_ = lean_ctor_get(v___x_258_, 6);
v_defEqI_266_ = lean_ctor_get(v___x_258_, 7);
v_extensions_267_ = lean_ctor_get(v___x_258_, 8);
v_issues_268_ = lean_ctor_get(v___x_258_, 9);
v_canon_269_ = lean_ctor_get(v___x_258_, 10);
v_instanceOverrides_270_ = lean_ctor_get(v___x_258_, 11);
v_debug_271_ = lean_ctor_get_uint8(v___x_258_, sizeof(void*)*12);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_282_ == 0)
{
v___x_273_ = v___x_258_;
v_isShared_274_ = v_isSharedCheck_282_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_instanceOverrides_270_);
lean_inc(v_canon_269_);
lean_inc(v_issues_268_);
lean_inc(v_extensions_267_);
lean_inc(v_defEqI_266_);
lean_inc(v_congrInfo_265_);
lean_inc(v_getLevel_264_);
lean_inc(v_inferType_263_);
lean_inc(v_proofInstInfoFVar_262_);
lean_inc(v_proofInstInfo_261_);
lean_inc(v_maxFVar_260_);
lean_inc(v_share_259_);
lean_dec(v___x_258_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_282_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_275_ = lean_box(0);
lean_inc_ref(v_e_245_);
v___x_276_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_share_259_, v_e_245_, v___x_275_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_276_);
v___x_278_ = v___x_273_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_maxFVar_260_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_proofInstInfo_261_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_proofInstInfoFVar_262_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_inferType_263_);
lean_ctor_set(v_reuseFailAlloc_281_, 5, v_getLevel_264_);
lean_ctor_set(v_reuseFailAlloc_281_, 6, v_congrInfo_265_);
lean_ctor_set(v_reuseFailAlloc_281_, 7, v_defEqI_266_);
lean_ctor_set(v_reuseFailAlloc_281_, 8, v_extensions_267_);
lean_ctor_set(v_reuseFailAlloc_281_, 9, v_issues_268_);
lean_ctor_set(v_reuseFailAlloc_281_, 10, v_canon_269_);
lean_ctor_set(v_reuseFailAlloc_281_, 11, v_instanceOverrides_270_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, sizeof(void*)*12, v_debug_271_);
v___x_278_ = v_reuseFailAlloc_281_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_st_ref_put(v_a_246_, v___x_278_);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v_e_245_);
return v___x_280_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_Sym_share1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_245_ = stack[0].m_obj;
lean_object* v_a_246_ = stack[1].m_obj;
lean_object* v_res_283_;
v_res_283_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_245_, v_a_246_);
stack->m_obj
 = v_res_283_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg___boxed(lean_object* v_e_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_284_, v_a_285_);
lean_dec(v_a_285_);
return v_res_287_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1(lean_object* v_e_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_288_, v_a_290_);
return v___x_296_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_Sym_share1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_288_ = stack[0].m_obj;
lean_object* v_a_289_ = stack[1].m_obj;
lean_object* v_a_290_ = stack[2].m_obj;
lean_object* v_a_291_ = stack[3].m_obj;
lean_object* v_a_292_ = stack[4].m_obj;
lean_object* v_a_293_ = stack[5].m_obj;
lean_object* v_a_294_ = stack[6].m_obj;
lean_object* v_res_297_;
v_res_297_ = l_Lean_Meta_Sym_Internal_Sym_share1(v_e_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___boxed(lean_object* v_e_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Meta_Sym_Internal_Sym_share1(v_e_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
return v_res_306_;
}
}
lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(lean_object* v_00_u03b2_307_, lean_object* v_x_308_, size_t v_x_309_, lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_308_, v_x_309_, v_x_310_, v_x_311_);
return v___x_312_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_308_ = stack[1].m_obj;
size_t v_x_309_ = stack[2].m_num;
lean_object* v_x_310_ = stack[3].m_obj;
lean_object* v_x_311_ = stack[4].m_obj;
lean_object* v_res_313_;
v_res_313_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(lean_box(0), v_x_308_, v_x_309_, v_x_310_, v_x_311_);
stack->m_obj
 = v_res_313_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___boxed(lean_object* v_00_u03b2_314_, lean_object* v_x_315_, lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
size_t v_x_2533__boxed_319_; lean_object* v_res_320_; 
v_x_2533__boxed_319_ = lean_unbox_usize(v_x_316_);
lean_dec(v_x_316_);
v_res_320_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(v_00_u03b2_314_, v_x_315_, v_x_2533__boxed_319_, v_x_317_, v_x_318_);
lean_dec_ref(v_x_318_);
lean_dec_ref(v_x_317_);
lean_dec_ref(v_x_315_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1(lean_object* v_00_u03b2_321_, lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_x_322_, v_x_323_, v_x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(lean_object* v_00_u03b2_326_, lean_object* v_keys_327_, lean_object* v_vals_328_, lean_object* v_heq_329_, lean_object* v_i_330_, lean_object* v_k_331_, lean_object* v_k_u2080_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_327_, v_i_330_, v_k_331_, v_k_u2080_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___boxed(lean_object* v_00_u03b2_334_, lean_object* v_keys_335_, lean_object* v_vals_336_, lean_object* v_heq_337_, lean_object* v_i_338_, lean_object* v_k_339_, lean_object* v_k_u2080_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(v_00_u03b2_334_, v_keys_335_, v_vals_336_, v_heq_337_, v_i_338_, v_k_339_, v_k_u2080_340_);
lean_dec_ref(v_k_u2080_340_);
lean_dec_ref(v_k_339_);
lean_dec_ref(v_vals_336_);
lean_dec_ref(v_keys_335_);
return v_res_341_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(lean_object* v_00_u03b2_342_, lean_object* v_x_343_, size_t v_x_344_, size_t v_x_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_343_, v_x_344_, v_x_345_, v_x_346_, v_x_347_);
return v___x_348_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_343_ = stack[1].m_obj;
size_t v_x_344_ = stack[2].m_num;
size_t v_x_345_ = stack[3].m_num;
lean_object* v_x_346_ = stack[4].m_obj;
lean_object* v_x_347_ = stack[5].m_obj;
lean_object* v_res_349_;
v_res_349_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(lean_box(0), v_x_343_, v_x_344_, v_x_345_, v_x_346_, v_x_347_);
stack->m_obj
 = v_res_349_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_350_, lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
size_t v_x_2571__boxed_356_; size_t v_x_2572__boxed_357_; lean_object* v_res_358_; 
v_x_2571__boxed_356_ = lean_unbox_usize(v_x_352_);
lean_dec(v_x_352_);
v_x_2572__boxed_357_ = lean_unbox_usize(v_x_353_);
lean_dec(v_x_353_);
v_res_358_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(v_00_u03b2_350_, v_x_351_, v_x_2571__boxed_356_, v_x_2572__boxed_357_, v_x_354_, v_x_355_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_359_, lean_object* v_n_360_, lean_object* v_k_361_, lean_object* v_v_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(v_n_360_, v_k_361_, v_v_362_);
return v___x_363_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_364_, size_t v_depth_365_, lean_object* v_keys_366_, lean_object* v_vals_367_, lean_object* v_heq_368_, lean_object* v_i_369_, lean_object* v_entries_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_365_, v_keys_366_, v_vals_367_, v_i_369_, v_entries_370_);
return v___x_371_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_depth_365_ = stack[1].m_num;
lean_object* v_keys_366_ = stack[2].m_obj;
lean_object* v_vals_367_ = stack[3].m_obj;
lean_object* v_i_369_ = stack[5].m_obj;
lean_object* v_entries_370_ = stack[6].m_obj;
lean_object* v_res_372_;
v_res_372_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(lean_box(0), v_depth_365_, v_keys_366_, v_vals_367_, lean_box(0), v_i_369_, v_entries_370_);
stack->m_obj
 = v_res_372_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_373_, lean_object* v_depth_374_, lean_object* v_keys_375_, lean_object* v_vals_376_, lean_object* v_heq_377_, lean_object* v_i_378_, lean_object* v_entries_379_){
_start:
{
size_t v_depth_boxed_380_; lean_object* v_res_381_; 
v_depth_boxed_380_ = lean_unbox_usize(v_depth_374_);
lean_dec(v_depth_374_);
v_res_381_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(v_00_u03b2_373_, v_depth_boxed_380_, v_keys_375_, v_vals_376_, v_heq_377_, v_i_378_, v_entries_379_);
lean_dec_ref(v_vals_376_);
lean_dec_ref(v_keys_375_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_382_, lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_383_, v_x_384_, v_x_385_, v_x_386_);
return v___x_387_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0(void){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_388_;
}
}
lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(lean_object* v_msg_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_698__overap_398_; lean_object* v___x_399_; 
v___x_397_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_698__overap_398_ = lean_panic_fn_borrowed(v___x_397_, v_msg_389_);
lean_inc(v___y_395_);
lean_inc_ref(v___y_394_);
lean_inc(v___y_393_);
lean_inc_ref(v___y_392_);
lean_inc(v___y_391_);
lean_inc_ref(v___y_390_);
v___x_399_ = lean_apply_7(v___x_698__overap_398_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, lean_box(0));
return v___x_399_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_389_ = stack[0].m_obj;
lean_object* v___y_390_ = stack[1].m_obj;
lean_object* v___y_391_ = stack[2].m_obj;
lean_object* v___y_392_ = stack[3].m_obj;
lean_object* v___y_393_ = stack[4].m_obj;
lean_object* v___y_394_ = stack[5].m_obj;
lean_object* v___y_395_ = stack[6].m_obj;
lean_object* v_res_400_;
v_res_400_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v_msg_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
stack->m_obj
 = v_res_400_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___boxed(lean_object* v_msg_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v_msg_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_409_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_413_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2));
v___x_414_ = lean_unsigned_to_nat(2u);
v___x_415_ = lean_unsigned_to_nat(42u);
v___x_416_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1));
v___x_417_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_418_ = l_mkPanicMessageWithDecl(v___x_417_, v___x_416_, v___x_415_, v___x_414_, v___x_413_);
return v___x_418_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object* v_e_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v___x_427_; lean_object* v_share_428_; lean_object* v___x_429_; uint64_t v___x_430_; size_t v___x_431_; lean_object* v___x_432_; size_t v___x_433_; size_t v___x_434_; uint8_t v___x_435_; 
v___x_427_ = lean_st_ref_get(v_a_421_);
v_share_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc_ref(v_share_428_);
lean_dec(v___x_427_);
v___x_429_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_430_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_419_);
v___x_431_ = lean_uint64_to_usize(v___x_430_);
v___x_432_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_428_, v___x_431_, v_e_419_, v___x_429_);
lean_dec_ref(v_share_428_);
v___x_433_ = lean_ptr_addr(v___x_432_);
lean_dec_ref(v___x_432_);
v___x_434_ = lean_ptr_addr(v_e_419_);
v___x_435_ = lean_usize_dec_eq(v___x_433_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3, &l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3_once, _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3);
v___x_437_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v___x_436_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
return v___x_437_;
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_box(0);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_Sym_assertShared_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_419_ = stack[0].m_obj;
lean_object* v_a_420_ = stack[1].m_obj;
lean_object* v_a_421_ = stack[2].m_obj;
lean_object* v_a_422_ = stack[3].m_obj;
lean_object* v_a_423_ = stack[4].m_obj;
lean_object* v_a_424_ = stack[5].m_obj;
lean_object* v_a_425_ = stack[6].m_obj;
lean_object* v_res_440_;
v_res_440_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
stack->m_obj
 = v_res_440_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed(lean_object* v_e_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec_ref(v_e_441_);
return v_res_449_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_460_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1));
v___x_461_ = lean_unsigned_to_nat(16u);
v___x_462_ = lean_unsigned_to_nat(62u);
v___x_463_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0));
v___x_464_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_465_ = l_mkPanicMessageWithDecl(v___x_464_, v___x_463_, v___x_462_, v___x_461_, v___x_460_);
return v___x_465_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object* v_k_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v_debug_476_; lean_object* v___x_477_; lean_object* v_env_478_; lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_474_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_475_ = lean_st_ref_get(v_a_468_);
v_debug_476_ = lean_ctor_get_uint8(v___x_475_, sizeof(void*)*12);
lean_dec(v___x_475_);
v___x_477_ = lean_st_ref_get(v_a_472_);
v_env_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc_ref(v_env_478_);
lean_dec(v___x_477_);
v___x_479_ = lean_box(v_debug_476_);
v___x_480_ = lean_apply_1(v_k_466_, v___x_479_);
v___x_481_ = 0;
v___x_482_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_482_, 0, v_env_478_);
lean_ctor_set_uint8(v___x_482_, sizeof(void*)*1, v___x_481_);
lean_ctor_set_uint8(v___x_482_, sizeof(void*)*1 + 1, v___x_481_);
v___x_483_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_480_, v___x_482_, v_a_468_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_495_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_495_ == 0)
{
v___x_486_ = v___x_483_;
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
if (lean_obj_tag(v_a_484_) == 0)
{
lean_object* v___x_488_; lean_object* v___x_1316__overap_489_; lean_object* v___x_490_; 
lean_dec_ref_known(v_a_484_, 1);
lean_del_object(v___x_486_);
v___x_488_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
v___x_1316__overap_489_ = l_panic___redArg(v___x_474_, v___x_488_);
lean_inc(v_a_472_);
lean_inc_ref(v_a_471_);
lean_inc(v_a_470_);
lean_inc_ref(v_a_469_);
lean_inc(v_a_468_);
lean_inc_ref(v_a_467_);
v___x_490_ = lean_apply_7(v___x_1316__overap_489_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, lean_box(0));
return v___x_490_;
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; 
v_a_491_ = lean_ctor_get(v_a_484_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v_a_484_, 1);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v_a_491_);
v___x_493_ = v___x_486_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
v_a_496_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_483_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_483_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_liftBuilderM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_466_ = stack[0].m_obj;
lean_object* v_a_467_ = stack[1].m_obj;
lean_object* v_a_468_ = stack[2].m_obj;
lean_object* v_a_469_ = stack[3].m_obj;
lean_object* v_a_470_ = stack[4].m_obj;
lean_object* v_a_471_ = stack[5].m_obj;
lean_object* v_a_472_ = stack[6].m_obj;
lean_object* v_res_504_;
v_res_504_ = l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(v_k_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
stack->m_obj
 = v_res_504_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(lean_object* v_k_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(v_k_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
return v_res_513_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM(lean_object* v_00_u03b1_514_, lean_object* v_k_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v_debug_525_; lean_object* v___x_526_; lean_object* v_env_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_523_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_524_ = lean_st_ref_get(v_a_517_);
v_debug_525_ = lean_ctor_get_uint8(v___x_524_, sizeof(void*)*12);
lean_dec(v___x_524_);
v___x_526_ = lean_st_ref_get(v_a_521_);
v_env_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc_ref(v_env_527_);
lean_dec(v___x_526_);
v___x_528_ = lean_box(v_debug_525_);
v___x_529_ = lean_apply_1(v_k_515_, v___x_528_);
v___x_530_ = 0;
v___x_531_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_531_, 0, v_env_527_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*1, v___x_530_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*1 + 1, v___x_530_);
v___x_532_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_529_, v___x_531_, v_a_517_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_544_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_544_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_544_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_544_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
if (lean_obj_tag(v_a_533_) == 0)
{
lean_object* v___x_537_; lean_object* v___x_1339__overap_538_; lean_object* v___x_539_; 
lean_dec_ref_known(v_a_533_, 1);
lean_del_object(v___x_535_);
v___x_537_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
v___x_1339__overap_538_ = l_panic___redArg(v___x_523_, v___x_537_);
lean_inc(v_a_521_);
lean_inc_ref(v_a_520_);
lean_inc(v_a_519_);
lean_inc_ref(v_a_518_);
lean_inc(v_a_517_);
lean_inc_ref(v_a_516_);
v___x_539_ = lean_apply_7(v___x_1339__overap_538_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, lean_box(0));
return v___x_539_;
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; 
v_a_540_ = lean_ctor_get(v_a_533_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v_a_533_, 1);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v_a_540_);
v___x_542_ = v___x_535_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
v_a_545_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_532_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_532_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_liftBuilderM_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_515_ = stack[1].m_obj;
lean_object* v_a_516_ = stack[2].m_obj;
lean_object* v_a_517_ = stack[3].m_obj;
lean_object* v_a_518_ = stack[4].m_obj;
lean_object* v_a_519_ = stack[5].m_obj;
lean_object* v_a_520_ = stack[6].m_obj;
lean_object* v_a_521_ = stack[7].m_obj;
lean_object* v_res_553_;
v_res_553_ = l_Lean_Meta_Sym_Internal_liftBuilderM(lean_box(0), v_k_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
stack->m_obj
 = v_res_553_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object* v_00_u03b1_554_, lean_object* v_k_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Meta_Sym_Internal_liftBuilderM(v_00_u03b1_554_, v_k_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object* v_e_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_566_; uint64_t v___x_567_; size_t v___x_568_; lean_object* v___x_569_; size_t v___x_570_; size_t v___x_571_; uint8_t v___x_572_; 
v___x_566_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_567_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_564_);
v___x_568_ = lean_uint64_to_usize(v___x_567_);
v___x_569_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_a_565_, v___x_568_, v_e_564_, v___x_566_);
v___x_570_ = lean_ptr_addr(v___x_569_);
v___x_571_ = lean_usize_once(&l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0, &l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0);
v___x_572_ = lean_usize_dec_eq(v___x_570_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
lean_dec_ref(v_e_564_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_569_);
lean_ctor_set(v___x_573_, 1, v_a_565_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec_ref(v___x_569_);
v___x_574_ = lean_box(0);
lean_inc_ref(v_e_564_);
v___x_575_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_a_565_, v_e_564_, v___x_574_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v_e_564_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
return v___x_576_;
}
}
}
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object* v_e_577_, uint8_t v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v_e_577_, v_a_580_);
return v___x_581_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_Builder_share1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_577_ = stack[0].m_obj;
uint8_t v_a_578_ = stack[1].m_num;
lean_object* v_a_579_ = stack[2].m_obj;
lean_object* v_a_580_ = stack[3].m_obj;
lean_object* v_res_582_;
v_res_582_ = l_Lean_Meta_Sym_Internal_Builder_share1(v_e_577_, v_a_578_, v_a_579_, v_a_580_);
stack->m_obj
 = v_res_582_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object* v_e_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
uint8_t v_a_boxed_587_; lean_object* v_res_588_; 
v_a_boxed_587_ = lean_unbox(v_a_584_);
v_res_588_ = l_Lean_Meta_Sym_Internal_Builder_share1(v_e_583_, v_a_boxed_587_, v_a_585_, v_a_586_);
lean_dec_ref(v_a_585_);
return v_res_588_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0(void){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Std_HashMap_instInhabited___redArg();
return v___x_589_;
}
}
lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object* v_msg_590_, uint8_t v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___x_534__overap_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_594_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0);
v___f_595_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_595_, 0, v___x_594_);
v___f_596_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_596_, 0, v___f_595_);
v___f_597_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_597_, 0, v___f_596_);
v___x_534__overap_598_ = lean_panic_fn_borrowed(v___f_597_, v_msg_590_);
lean_dec_ref(v___f_597_);
v___x_599_ = lean_box(v___y_591_);
lean_inc_ref(v___y_592_);
v___x_600_ = lean_apply_3(v___x_534__overap_598_, v___x_599_, v___y_592_, v___y_593_);
return v___x_600_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_590_ = stack[0].m_obj;
uint8_t v___y_591_ = stack[1].m_num;
lean_object* v___y_592_ = stack[2].m_obj;
lean_object* v___y_593_ = stack[3].m_obj;
lean_object* v_res_601_;
v_res_601_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v_msg_590_, v___y_591_, v___y_592_, v___y_593_);
stack->m_obj
 = v_res_601_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object* v_msg_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
uint8_t v___y_635__boxed_606_; lean_object* v_res_607_; 
v___y_635__boxed_606_ = lean_unbox(v___y_603_);
v_res_607_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v_msg_602_, v___y_635__boxed_606_, v___y_604_, v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_607_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_608_, lean_object* v_i_609_, lean_object* v_k_610_){
_start:
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_array_get_size(v_keys_608_);
v___x_612_ = lean_nat_dec_lt(v_i_609_, v___x_611_);
if (v___x_612_ == 0)
{
lean_dec(v_i_609_);
return v___x_612_;
}
else
{
lean_object* v_k_x27_613_; uint8_t v___x_614_; 
v_k_x27_613_ = lean_array_fget_borrowed(v_keys_608_, v_i_609_);
v___x_614_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_610_, v_k_x27_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_nat_add(v_i_609_, v___x_615_);
lean_dec(v_i_609_);
v_i_609_ = v___x_616_;
goto _start;
}
else
{
lean_dec(v_i_609_);
return v___x_612_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_608_ = stack[0].m_obj;
lean_object* v_i_609_ = stack[1].m_obj;
lean_object* v_k_610_ = stack[2].m_obj;
uint8_t v_res_618_;
v_res_618_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_608_, v_i_609_, v_k_610_);
stack->m_num = v_res_618_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_619_, lean_object* v_i_620_, lean_object* v_k_621_){
_start:
{
uint8_t v_res_622_; lean_object* v_r_623_; 
v_res_622_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_619_, v_i_620_, v_k_621_);
lean_dec_ref(v_k_621_);
lean_dec_ref(v_keys_619_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(lean_object* v_x_624_, size_t v_x_625_, lean_object* v_x_626_){
_start:
{
if (lean_obj_tag(v_x_624_) == 0)
{
lean_object* v_es_627_; lean_object* v___x_628_; size_t v___x_629_; size_t v___x_630_; lean_object* v_j_631_; lean_object* v___x_632_; 
v_es_627_ = lean_ctor_get(v_x_624_, 0);
v___x_628_ = lean_box(2);
v___x_629_ = ((size_t)31ULL);
v___x_630_ = lean_usize_land(v_x_625_, v___x_629_);
v_j_631_ = lean_usize_to_nat(v___x_630_);
v___x_632_ = lean_array_get_borrowed(v___x_628_, v_es_627_, v_j_631_);
lean_dec(v_j_631_);
switch(lean_obj_tag(v___x_632_))
{
case 0:
{
lean_object* v_key_633_; uint8_t v___x_634_; 
v_key_633_ = lean_ctor_get(v___x_632_, 0);
v___x_634_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_626_, v_key_633_);
return v___x_634_;
}
case 1:
{
lean_object* v_node_635_; size_t v___x_636_; size_t v___x_637_; 
v_node_635_ = lean_ctor_get(v___x_632_, 0);
v___x_636_ = ((size_t)5ULL);
v___x_637_ = lean_usize_shift_right(v_x_625_, v___x_636_);
v_x_624_ = v_node_635_;
v_x_625_ = v___x_637_;
goto _start;
}
default: 
{
uint8_t v___x_639_; 
v___x_639_ = 0;
return v___x_639_;
}
}
}
else
{
lean_object* v_ks_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_ks_640_ = lean_ctor_get(v_x_624_, 0);
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_ks_640_, v___x_641_, v_x_626_);
return v___x_642_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_624_ = stack[0].m_obj;
size_t v_x_625_ = stack[1].m_num;
lean_object* v_x_626_ = stack[2].m_obj;
uint8_t v_res_643_;
v_res_643_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_624_, v_x_625_, v_x_626_);
stack->m_num = v_res_643_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_644_, lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
size_t v_x_689__boxed_647_; uint8_t v_res_648_; lean_object* v_r_649_; 
v_x_689__boxed_647_ = lean_unbox_usize(v_x_645_);
lean_dec(v_x_645_);
v_res_648_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_644_, v_x_689__boxed_647_, v_x_646_);
lean_dec_ref(v_x_646_);
lean_dec_ref(v_x_644_);
v_r_649_ = lean_box(v_res_648_);
return v_r_649_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(lean_object* v_x_650_, lean_object* v_x_651_){
_start:
{
uint64_t v___x_652_; size_t v___x_653_; uint8_t v___x_654_; 
v___x_652_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_651_);
v___x_653_ = lean_uint64_to_usize(v___x_652_);
v___x_654_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_650_, v___x_653_, v_x_651_);
return v___x_654_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_650_ = stack[0].m_obj;
lean_object* v_x_651_ = stack[1].m_obj;
uint8_t v_res_655_;
v_res_655_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_650_, v_x_651_);
stack->m_num = v_res_655_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
uint8_t v_res_658_; lean_object* v_r_659_; 
v_res_658_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_656_, v_x_657_);
lean_dec_ref(v_x_657_);
lean_dec_ref(v_x_656_);
v_r_659_ = lean_box(v_res_658_);
return v_r_659_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_662_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1));
v___x_663_ = lean_unsigned_to_nat(2u);
v___x_664_ = lean_unsigned_to_nat(74u);
v___x_665_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0));
v___x_666_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_667_ = l_mkPanicMessageWithDecl(v___x_666_, v___x_665_, v___x_664_, v___x_663_, v___x_662_);
return v___x_667_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object* v_e_668_, uint8_t v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
uint8_t v___x_672_; 
v___x_672_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_a_671_, v_e_668_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2, &l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once, _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2);
v___x_674_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v___x_673_, v_a_669_, v_a_670_, v_a_671_);
return v___x_674_;
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_box(0);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v_a_671_);
return v___x_676_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_Builder_assertShared_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_668_ = stack[0].m_obj;
uint8_t v_a_669_ = stack[1].m_num;
lean_object* v_a_670_ = stack[2].m_obj;
lean_object* v_a_671_ = stack[3].m_obj;
lean_object* v_res_677_;
v_res_677_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_668_, v_a_669_, v_a_670_, v_a_671_);
stack->m_obj
 = v_res_677_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object* v_e_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
uint8_t v_a_boxed_682_; lean_object* v_res_683_; 
v_a_boxed_682_ = lean_unbox(v_a_679_);
v_res_683_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_678_, v_a_boxed_682_, v_a_680_, v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec_ref(v_e_678_);
return v_res_683_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object* v_00_u03b2_684_, lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
uint8_t v___x_687_; 
v___x_687_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_685_, v_x_686_);
return v___x_687_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_685_ = stack[1].m_obj;
lean_object* v_x_686_ = stack[2].m_obj;
uint8_t v_res_688_;
v_res_688_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_box(0), v_x_685_, v_x_686_);
stack->m_num = v_res_688_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object* v_00_u03b2_689_, lean_object* v_x_690_, lean_object* v_x_691_){
_start:
{
uint8_t v_res_692_; lean_object* v_r_693_; 
v_res_692_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(v_00_u03b2_689_, v_x_690_, v_x_691_);
lean_dec_ref(v_x_691_);
lean_dec_ref(v_x_690_);
v_r_693_ = lean_box(v_res_692_);
return v_r_693_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object* v_00_u03b2_694_, lean_object* v_x_695_, size_t v_x_696_, lean_object* v_x_697_){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_695_, v_x_696_, v_x_697_);
return v___x_698_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_695_ = stack[1].m_obj;
size_t v_x_696_ = stack[2].m_num;
lean_object* v_x_697_ = stack[3].m_obj;
uint8_t v_res_699_;
v_res_699_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_box(0), v_x_695_, v_x_696_, v_x_697_);
stack->m_num = v_res_699_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_700_, lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_x_703_){
_start:
{
size_t v_x_836__boxed_704_; uint8_t v_res_705_; lean_object* v_r_706_; 
v_x_836__boxed_704_ = lean_unbox_usize(v_x_702_);
lean_dec(v_x_702_);
v_res_705_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(v_00_u03b2_700_, v_x_701_, v_x_836__boxed_704_, v_x_703_);
lean_dec_ref(v_x_703_);
lean_dec_ref(v_x_701_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_707_, lean_object* v_keys_708_, lean_object* v_vals_709_, lean_object* v_heq_710_, lean_object* v_i_711_, lean_object* v_k_712_){
_start:
{
uint8_t v___x_713_; 
v___x_713_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_708_, v_i_711_, v_k_712_);
return v___x_713_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_708_ = stack[1].m_obj;
lean_object* v_vals_709_ = stack[2].m_obj;
lean_object* v_i_711_ = stack[4].m_obj;
lean_object* v_k_712_ = stack[5].m_obj;
uint8_t v_res_714_;
v_res_714_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_box(0), v_keys_708_, v_vals_709_, lean_box(0), v_i_711_, v_k_712_);
stack->m_num = v_res_714_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_715_, lean_object* v_keys_716_, lean_object* v_vals_717_, lean_object* v_heq_718_, lean_object* v_i_719_, lean_object* v_k_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(v_00_u03b2_715_, v_keys_716_, v_vals_717_, v_heq_718_, v_i_719_, v_k_720_);
lean_dec_ref(v_k_720_);
lean_dec_ref(v_vals_717_);
lean_dec_ref(v_keys_716_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__9));
v___x_743_ = l_ReaderT_instMonad___redArg(v___x_742_);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10);
v___x_747_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_747_, 0, lean_box(0));
lean_closure_set(v___x_747_, 1, lean_box(0));
lean_closure_set(v___x_747_, 2, v___x_746_);
return v___x_747_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_748_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13);
v___x_749_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__12));
v___x_750_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__11));
v___x_751_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v___x_749_);
lean_ctor_set(v___x_751_, 2, v___x_748_);
return v___x_751_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM(void){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS___redArg(lean_object* v_inst_753_, lean_object* v_l_754_){
_start:
{
lean_object* v_share1_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_share1_755_ = lean_ctor_get(v_inst_753_, 0);
lean_inc(v_share1_755_);
lean_dec_ref(v_inst_753_);
v___x_756_ = l_Lean_Expr_lit___override(v_l_754_);
v___x_757_ = lean_apply_1(v_share1_755_, v___x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS(lean_object* v_m_758_, lean_object* v_inst_759_, lean_object* v_l_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_Meta_Sym_Internal_mkLitS___redArg(v_inst_759_, v_l_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___redArg(lean_object* v_inst_762_, lean_object* v_declName_763_, lean_object* v_us_764_){
_start:
{
lean_object* v_share1_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_share1_765_ = lean_ctor_get(v_inst_762_, 0);
lean_inc(v_share1_765_);
lean_dec_ref(v_inst_762_);
v___x_766_ = l_Lean_Expr_const___override(v_declName_763_, v_us_764_);
v___x_767_ = lean_apply_1(v_share1_765_, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS(lean_object* v_m_768_, lean_object* v_inst_769_, lean_object* v_declName_770_, lean_object* v_us_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Meta_Sym_Internal_mkConstS___redArg(v_inst_769_, v_declName_770_, v_us_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object* v_inst_773_, lean_object* v_idx_774_){
_start:
{
lean_object* v_share1_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_share1_775_ = lean_ctor_get(v_inst_773_, 0);
lean_inc(v_share1_775_);
lean_dec_ref(v_inst_773_);
v___x_776_ = l_Lean_Expr_bvar___override(v_idx_774_);
v___x_777_ = lean_apply_1(v_share1_775_, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS(lean_object* v_m_778_, lean_object* v_inst_779_, lean_object* v_idx_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v_inst_779_, v_idx_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___redArg(lean_object* v_inst_782_, lean_object* v_u_783_){
_start:
{
lean_object* v_share1_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_share1_784_ = lean_ctor_get(v_inst_782_, 0);
lean_inc(v_share1_784_);
lean_dec_ref(v_inst_782_);
v___x_785_ = l_Lean_Expr_sort___override(v_u_783_);
v___x_786_ = lean_apply_1(v_share1_784_, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS(lean_object* v_m_787_, lean_object* v_inst_788_, lean_object* v_u_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_Meta_Sym_Internal_mkSortS___redArg(v_inst_788_, v_u_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object* v_inst_791_, lean_object* v_fvarId_792_){
_start:
{
lean_object* v_share1_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_share1_793_ = lean_ctor_get(v_inst_791_, 0);
lean_inc(v_share1_793_);
lean_dec_ref(v_inst_791_);
v___x_794_ = l_Lean_Expr_fvar___override(v_fvarId_792_);
v___x_795_ = lean_apply_1(v_share1_793_, v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS(lean_object* v_m_796_, lean_object* v_inst_797_, lean_object* v_fvarId_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Meta_Sym_Internal_mkFVarS___redArg(v_inst_797_, v_fvarId_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___redArg(lean_object* v_inst_800_, lean_object* v_mvarId_801_){
_start:
{
lean_object* v_share1_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_share1_802_ = lean_ctor_get(v_inst_800_, 0);
lean_inc(v_share1_802_);
lean_dec_ref(v_inst_800_);
v___x_803_ = l_Lean_Expr_mvar___override(v_mvarId_801_);
v___x_804_ = lean_apply_1(v_share1_802_, v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS(lean_object* v_m_805_, lean_object* v_inst_806_, lean_object* v_mvarId_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_Meta_Sym_Internal_mkMVarS___redArg(v_inst_806_, v_mvarId_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(lean_object* v_d_809_, lean_object* v_e_810_, lean_object* v_share1_811_, lean_object* v_____r_812_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = l_Lean_Expr_mdata___override(v_d_809_, v_e_810_);
v___x_814_ = lean_apply_1(v_share1_811_, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(lean_object* v___f_815_, lean_object* v_____r_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = lean_apply_1(v___f_815_, v_____r_816_);
return v___x_817_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(lean_object* v___f_818_, lean_object* v_assertShared_819_, lean_object* v_e_820_, lean_object* v_toBind_821_, lean_object* v___f_822_, uint8_t v_____do__lift_823_){
_start:
{
if (v_____do__lift_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec(v___f_822_);
lean_dec(v_toBind_821_);
lean_dec_ref(v_e_820_);
lean_dec(v_assertShared_819_);
v___x_824_ = lean_box(0);
v___x_825_ = lean_apply_1(v___f_818_, v___x_824_);
return v___x_825_;
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; 
lean_dec(v___f_818_);
v___x_826_ = lean_apply_1(v_assertShared_819_, v_e_820_);
v___x_827_ = lean_apply_4(v_toBind_821_, lean_box(0), lean_box(0), v___x_826_, v___f_822_);
return v___x_827_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_818_ = stack[0].m_obj;
lean_object* v_assertShared_819_ = stack[1].m_obj;
lean_object* v_e_820_ = stack[2].m_obj;
lean_object* v_toBind_821_ = stack[3].m_obj;
lean_object* v___f_822_ = stack[4].m_obj;
uint8_t v_____do__lift_823_ = stack[5].m_num;
lean_object* v_res_828_;
v_res_828_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(v___f_818_, v_assertShared_819_, v_e_820_, v_toBind_821_, v___f_822_, v_____do__lift_823_);
stack->m_obj
 = v_res_828_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(lean_object* v___f_829_, lean_object* v_assertShared_830_, lean_object* v_e_831_, lean_object* v_toBind_832_, lean_object* v___f_833_, lean_object* v_____do__lift_834_){
_start:
{
uint8_t v_____do__lift_69__boxed_835_; lean_object* v_res_836_; 
v_____do__lift_69__boxed_835_ = lean_unbox(v_____do__lift_834_);
v_res_836_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(v___f_829_, v_assertShared_830_, v_e_831_, v_toBind_832_, v___f_833_, v_____do__lift_69__boxed_835_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object* v_inst_837_, lean_object* v_inst_838_, lean_object* v_d_839_, lean_object* v_e_840_){
_start:
{
lean_object* v_toBind_841_; lean_object* v_share1_842_; lean_object* v_assertShared_843_; lean_object* v_isDebugEnabled_844_; lean_object* v___f_845_; lean_object* v___f_846_; lean_object* v___f_847_; lean_object* v___x_848_; 
v_toBind_841_ = lean_ctor_get(v_inst_838_, 1);
lean_inc_n(v_toBind_841_, 2);
lean_dec_ref(v_inst_838_);
v_share1_842_ = lean_ctor_get(v_inst_837_, 0);
lean_inc(v_share1_842_);
v_assertShared_843_ = lean_ctor_get(v_inst_837_, 1);
lean_inc(v_assertShared_843_);
v_isDebugEnabled_844_ = lean_ctor_get(v_inst_837_, 2);
lean_inc(v_isDebugEnabled_844_);
lean_dec_ref(v_inst_837_);
lean_inc_ref(v_e_840_);
v___f_845_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_845_, 0, v_d_839_);
lean_closure_set(v___f_845_, 1, v_e_840_);
lean_closure_set(v___f_845_, 2, v_share1_842_);
lean_inc_ref(v___f_845_);
v___f_846_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_846_, 0, v___f_845_);
v___f_847_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_847_, 0, v___f_845_);
lean_closure_set(v___f_847_, 1, v_assertShared_843_);
lean_closure_set(v___f_847_, 2, v_e_840_);
lean_closure_set(v___f_847_, 3, v_toBind_841_);
lean_closure_set(v___f_847_, 4, v___f_846_);
v___x_848_ = lean_apply_4(v_toBind_841_, lean_box(0), lean_box(0), v_isDebugEnabled_844_, v___f_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS(lean_object* v_m_849_, lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_d_852_, lean_object* v_e_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_850_, v_inst_851_, v_d_852_, v_e_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(lean_object* v_structName_855_, lean_object* v_idx_856_, lean_object* v_struct_857_, lean_object* v_share1_858_, lean_object* v_____r_859_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = l_Lean_Expr_proj___override(v_structName_855_, v_idx_856_, v_struct_857_);
v___x_861_ = lean_apply_1(v_share1_858_, v___x_860_);
return v___x_861_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(lean_object* v___f_862_, lean_object* v_assertShared_863_, lean_object* v_struct_864_, lean_object* v_toBind_865_, lean_object* v___f_866_, uint8_t v_____do__lift_867_){
_start:
{
if (v_____do__lift_867_ == 0)
{
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_dec(v___f_866_);
lean_dec(v_toBind_865_);
lean_dec_ref(v_struct_864_);
lean_dec(v_assertShared_863_);
v___x_868_ = lean_box(0);
v___x_869_ = lean_apply_1(v___f_862_, v___x_868_);
return v___x_869_;
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec(v___f_862_);
v___x_870_ = lean_apply_1(v_assertShared_863_, v_struct_864_);
v___x_871_ = lean_apply_4(v_toBind_865_, lean_box(0), lean_box(0), v___x_870_, v___f_866_);
return v___x_871_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_862_ = stack[0].m_obj;
lean_object* v_assertShared_863_ = stack[1].m_obj;
lean_object* v_struct_864_ = stack[2].m_obj;
lean_object* v_toBind_865_ = stack[3].m_obj;
lean_object* v___f_866_ = stack[4].m_obj;
uint8_t v_____do__lift_867_ = stack[5].m_num;
lean_object* v_res_872_;
v_res_872_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(v___f_862_, v_assertShared_863_, v_struct_864_, v_toBind_865_, v___f_866_, v_____do__lift_867_);
stack->m_obj
 = v_res_872_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(lean_object* v___f_873_, lean_object* v_assertShared_874_, lean_object* v_struct_875_, lean_object* v_toBind_876_, lean_object* v___f_877_, lean_object* v_____do__lift_878_){
_start:
{
uint8_t v_____do__lift_60__boxed_879_; lean_object* v_res_880_; 
v_____do__lift_60__boxed_879_ = lean_unbox(v_____do__lift_878_);
v_res_880_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(v___f_873_, v_assertShared_874_, v_struct_875_, v_toBind_876_, v___f_877_, v_____do__lift_60__boxed_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_structName_883_, lean_object* v_idx_884_, lean_object* v_struct_885_){
_start:
{
lean_object* v_toBind_886_; lean_object* v_share1_887_; lean_object* v_assertShared_888_; lean_object* v_isDebugEnabled_889_; lean_object* v___f_890_; lean_object* v___f_891_; lean_object* v___f_892_; lean_object* v___x_893_; 
v_toBind_886_ = lean_ctor_get(v_inst_882_, 1);
lean_inc_n(v_toBind_886_, 2);
lean_dec_ref(v_inst_882_);
v_share1_887_ = lean_ctor_get(v_inst_881_, 0);
lean_inc(v_share1_887_);
v_assertShared_888_ = lean_ctor_get(v_inst_881_, 1);
lean_inc(v_assertShared_888_);
v_isDebugEnabled_889_ = lean_ctor_get(v_inst_881_, 2);
lean_inc(v_isDebugEnabled_889_);
lean_dec_ref(v_inst_881_);
lean_inc_ref(v_struct_885_);
v___f_890_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0), 5, 4);
lean_closure_set(v___f_890_, 0, v_structName_883_);
lean_closure_set(v___f_890_, 1, v_idx_884_);
lean_closure_set(v___f_890_, 2, v_struct_885_);
lean_closure_set(v___f_890_, 3, v_share1_887_);
lean_inc_ref(v___f_890_);
v___f_891_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_891_, 0, v___f_890_);
v___f_892_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_892_, 0, v___f_890_);
lean_closure_set(v___f_892_, 1, v_assertShared_888_);
lean_closure_set(v___f_892_, 2, v_struct_885_);
lean_closure_set(v___f_892_, 3, v_toBind_886_);
lean_closure_set(v___f_892_, 4, v___f_891_);
v___x_893_ = lean_apply_4(v_toBind_886_, lean_box(0), lean_box(0), v_isDebugEnabled_889_, v___f_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS(lean_object* v_m_894_, lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_structName_897_, lean_object* v_idx_898_, lean_object* v_struct_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_895_, v_inst_896_, v_structName_897_, v_idx_898_, v_struct_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(lean_object* v_f_901_, lean_object* v_a_902_, lean_object* v_share1_903_, lean_object* v_____r_904_){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = l_Lean_Expr_app___override(v_f_901_, v_a_902_);
v___x_906_ = lean_apply_1(v_share1_903_, v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(lean_object* v_assertShared_907_, lean_object* v_a_908_, lean_object* v_toBind_909_, lean_object* v___f_910_, lean_object* v_____r_911_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_apply_1(v_assertShared_907_, v_a_908_);
v___x_913_ = lean_apply_4(v_toBind_909_, lean_box(0), lean_box(0), v___x_912_, v___f_910_);
return v___x_913_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(lean_object* v___f_914_, lean_object* v_assertShared_915_, lean_object* v_a_916_, lean_object* v_toBind_917_, lean_object* v___f_918_, lean_object* v_f_919_, uint8_t v_____do__lift_920_){
_start:
{
if (v_____do__lift_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; 
lean_dec_ref(v_f_919_);
lean_dec(v___f_918_);
lean_dec(v_toBind_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_assertShared_915_);
v___x_921_ = lean_box(0);
v___x_922_ = lean_apply_1(v___f_914_, v___x_921_);
return v___x_922_;
}
else
{
lean_object* v___f_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec(v___f_914_);
lean_inc(v_toBind_917_);
lean_inc(v_assertShared_915_);
v___f_923_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_923_, 0, v_assertShared_915_);
lean_closure_set(v___f_923_, 1, v_a_916_);
lean_closure_set(v___f_923_, 2, v_toBind_917_);
lean_closure_set(v___f_923_, 3, v___f_918_);
v___x_924_ = lean_apply_1(v_assertShared_915_, v_f_919_);
v___x_925_ = lean_apply_4(v_toBind_917_, lean_box(0), lean_box(0), v___x_924_, v___f_923_);
return v___x_925_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_914_ = stack[0].m_obj;
lean_object* v_assertShared_915_ = stack[1].m_obj;
lean_object* v_a_916_ = stack[2].m_obj;
lean_object* v_toBind_917_ = stack[3].m_obj;
lean_object* v___f_918_ = stack[4].m_obj;
lean_object* v_f_919_ = stack[5].m_obj;
uint8_t v_____do__lift_920_ = stack[6].m_num;
lean_object* v_res_926_;
v_res_926_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(v___f_914_, v_assertShared_915_, v_a_916_, v_toBind_917_, v___f_918_, v_f_919_, v_____do__lift_920_);
stack->m_obj
 = v_res_926_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(lean_object* v___f_927_, lean_object* v_assertShared_928_, lean_object* v_a_929_, lean_object* v_toBind_930_, lean_object* v___f_931_, lean_object* v_f_932_, lean_object* v_____do__lift_933_){
_start:
{
uint8_t v_____do__lift_81__boxed_934_; lean_object* v_res_935_; 
v_____do__lift_81__boxed_934_ = lean_unbox(v_____do__lift_933_);
v_res_935_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(v___f_927_, v_assertShared_928_, v_a_929_, v_toBind_930_, v___f_931_, v_f_932_, v_____do__lift_81__boxed_934_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_f_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_toBind_940_; lean_object* v_share1_941_; lean_object* v_assertShared_942_; lean_object* v_isDebugEnabled_943_; lean_object* v___f_944_; lean_object* v___f_945_; lean_object* v___f_946_; lean_object* v___x_947_; 
v_toBind_940_ = lean_ctor_get(v_inst_937_, 1);
lean_inc_n(v_toBind_940_, 2);
lean_dec_ref(v_inst_937_);
v_share1_941_ = lean_ctor_get(v_inst_936_, 0);
lean_inc(v_share1_941_);
v_assertShared_942_ = lean_ctor_get(v_inst_936_, 1);
lean_inc(v_assertShared_942_);
v_isDebugEnabled_943_ = lean_ctor_get(v_inst_936_, 2);
lean_inc(v_isDebugEnabled_943_);
lean_dec_ref(v_inst_936_);
lean_inc_ref(v_a_939_);
lean_inc_ref(v_f_938_);
v___f_944_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_944_, 0, v_f_938_);
lean_closure_set(v___f_944_, 1, v_a_939_);
lean_closure_set(v___f_944_, 2, v_share1_941_);
lean_inc_ref(v___f_944_);
v___f_945_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_945_, 0, v___f_944_);
v___f_946_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_946_, 0, v___f_944_);
lean_closure_set(v___f_946_, 1, v_assertShared_942_);
lean_closure_set(v___f_946_, 2, v_a_939_);
lean_closure_set(v___f_946_, 3, v_toBind_940_);
lean_closure_set(v___f_946_, 4, v___f_945_);
lean_closure_set(v___f_946_, 5, v_f_938_);
v___x_947_ = lean_apply_4(v_toBind_940_, lean_box(0), lean_box(0), v_isDebugEnabled_943_, v___f_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS(lean_object* v_m_948_, lean_object* v_inst_949_, lean_object* v_inst_950_, lean_object* v_f_951_, lean_object* v_a_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_949_, v_inst_950_, v_f_951_, v_a_952_);
return v___x_953_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(lean_object* v_x_954_, lean_object* v_t_955_, lean_object* v_b_956_, uint8_t v_bi_957_, lean_object* v_share1_958_, lean_object* v_____r_959_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = l_Lean_Expr_lam___override(v_x_954_, v_t_955_, v_b_956_, v_bi_957_);
v___x_961_ = lean_apply_1(v_share1_958_, v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_954_ = stack[0].m_obj;
lean_object* v_t_955_ = stack[1].m_obj;
lean_object* v_b_956_ = stack[2].m_obj;
uint8_t v_bi_957_ = stack[3].m_num;
lean_object* v_share1_958_ = stack[4].m_obj;
lean_object* v_____r_959_ = stack[5].m_obj;
lean_object* v_res_962_;
v_res_962_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(v_x_954_, v_t_955_, v_b_956_, v_bi_957_, v_share1_958_, v_____r_959_);
stack->m_obj
 = v_res_962_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(lean_object* v_x_963_, lean_object* v_t_964_, lean_object* v_b_965_, lean_object* v_bi_966_, lean_object* v_share1_967_, lean_object* v_____r_968_){
_start:
{
uint8_t v_bi_boxed_969_; lean_object* v_res_970_; 
v_bi_boxed_969_ = lean_unbox(v_bi_966_);
v_res_970_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(v_x_963_, v_t_964_, v_b_965_, v_bi_boxed_969_, v_share1_967_, v_____r_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(lean_object* v_assertShared_971_, lean_object* v_b_972_, lean_object* v_toBind_973_, lean_object* v___f_974_, lean_object* v_____r_975_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_apply_1(v_assertShared_971_, v_b_972_);
v___x_977_ = lean_apply_4(v_toBind_973_, lean_box(0), lean_box(0), v___x_976_, v___f_974_);
return v___x_977_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(lean_object* v___f_978_, lean_object* v_assertShared_979_, lean_object* v_b_980_, lean_object* v_toBind_981_, lean_object* v___f_982_, lean_object* v_t_983_, uint8_t v_____do__lift_984_){
_start:
{
if (v_____do__lift_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; 
lean_dec_ref(v_t_983_);
lean_dec(v___f_982_);
lean_dec(v_toBind_981_);
lean_dec_ref(v_b_980_);
lean_dec(v_assertShared_979_);
v___x_985_ = lean_box(0);
v___x_986_ = lean_apply_1(v___f_978_, v___x_985_);
return v___x_986_;
}
else
{
lean_object* v___f_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec(v___f_978_);
lean_inc(v_toBind_981_);
lean_inc(v_assertShared_979_);
v___f_987_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_987_, 0, v_assertShared_979_);
lean_closure_set(v___f_987_, 1, v_b_980_);
lean_closure_set(v___f_987_, 2, v_toBind_981_);
lean_closure_set(v___f_987_, 3, v___f_982_);
v___x_988_ = lean_apply_1(v_assertShared_979_, v_t_983_);
v___x_989_ = lean_apply_4(v_toBind_981_, lean_box(0), lean_box(0), v___x_988_, v___f_987_);
return v___x_989_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_978_ = stack[0].m_obj;
lean_object* v_assertShared_979_ = stack[1].m_obj;
lean_object* v_b_980_ = stack[2].m_obj;
lean_object* v_toBind_981_ = stack[3].m_obj;
lean_object* v___f_982_ = stack[4].m_obj;
lean_object* v_t_983_ = stack[5].m_obj;
uint8_t v_____do__lift_984_ = stack[6].m_num;
lean_object* v_res_990_;
v_res_990_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(v___f_978_, v_assertShared_979_, v_b_980_, v_toBind_981_, v___f_982_, v_t_983_, v_____do__lift_984_);
stack->m_obj
 = v_res_990_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(lean_object* v___f_991_, lean_object* v_assertShared_992_, lean_object* v_b_993_, lean_object* v_toBind_994_, lean_object* v___f_995_, lean_object* v_t_996_, lean_object* v_____do__lift_997_){
_start:
{
uint8_t v_____do__lift_83__boxed_998_; lean_object* v_res_999_; 
v_____do__lift_83__boxed_998_ = lean_unbox(v_____do__lift_997_);
v_res_999_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(v___f_991_, v_assertShared_992_, v_b_993_, v_toBind_994_, v___f_995_, v_t_996_, v_____do__lift_83__boxed_998_);
return v_res_999_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object* v_inst_1000_, lean_object* v_inst_1001_, lean_object* v_x_1002_, uint8_t v_bi_1003_, lean_object* v_t_1004_, lean_object* v_b_1005_){
_start:
{
lean_object* v_toBind_1006_; lean_object* v_share1_1007_; lean_object* v_assertShared_1008_; lean_object* v_isDebugEnabled_1009_; lean_object* v___x_1010_; lean_object* v___f_1011_; lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___x_1014_; 
v_toBind_1006_ = lean_ctor_get(v_inst_1001_, 1);
lean_inc_n(v_toBind_1006_, 2);
lean_dec_ref(v_inst_1001_);
v_share1_1007_ = lean_ctor_get(v_inst_1000_, 0);
lean_inc(v_share1_1007_);
v_assertShared_1008_ = lean_ctor_get(v_inst_1000_, 1);
lean_inc(v_assertShared_1008_);
v_isDebugEnabled_1009_ = lean_ctor_get(v_inst_1000_, 2);
lean_inc(v_isDebugEnabled_1009_);
lean_dec_ref(v_inst_1000_);
v___x_1010_ = lean_box(v_bi_1003_);
lean_inc_ref(v_b_1005_);
lean_inc_ref(v_t_1004_);
v___f_1011_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1011_, 0, v_x_1002_);
lean_closure_set(v___f_1011_, 1, v_t_1004_);
lean_closure_set(v___f_1011_, 2, v_b_1005_);
lean_closure_set(v___f_1011_, 3, v___x_1010_);
lean_closure_set(v___f_1011_, 4, v_share1_1007_);
lean_inc_ref(v___f_1011_);
v___f_1012_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1012_, 0, v___f_1011_);
v___f_1013_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1013_, 0, v___f_1011_);
lean_closure_set(v___f_1013_, 1, v_assertShared_1008_);
lean_closure_set(v___f_1013_, 2, v_b_1005_);
lean_closure_set(v___f_1013_, 3, v_toBind_1006_);
lean_closure_set(v___f_1013_, 4, v___f_1012_);
lean_closure_set(v___f_1013_, 5, v_t_1004_);
v___x_1014_ = lean_apply_4(v_toBind_1006_, lean_box(0), lean_box(0), v_isDebugEnabled_1009_, v___f_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLambdaS___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1000_ = stack[0].m_obj;
lean_object* v_inst_1001_ = stack[1].m_obj;
lean_object* v_x_1002_ = stack[2].m_obj;
uint8_t v_bi_1003_ = stack[3].m_num;
lean_object* v_t_1004_ = stack[4].m_obj;
lean_object* v_b_1005_ = stack[5].m_obj;
lean_object* v_res_1015_;
v_res_1015_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1000_, v_inst_1001_, v_x_1002_, v_bi_1003_, v_t_1004_, v_b_1005_);
stack->m_obj
 = v_res_1015_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(lean_object* v_inst_1016_, lean_object* v_inst_1017_, lean_object* v_x_1018_, lean_object* v_bi_1019_, lean_object* v_t_1020_, lean_object* v_b_1021_){
_start:
{
uint8_t v_bi_boxed_1022_; lean_object* v_res_1023_; 
v_bi_boxed_1022_ = lean_unbox(v_bi_1019_);
v_res_1023_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1016_, v_inst_1017_, v_x_1018_, v_bi_boxed_1022_, v_t_1020_, v_b_1021_);
return v_res_1023_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS(lean_object* v_m_1024_, lean_object* v_inst_1025_, lean_object* v_inst_1026_, lean_object* v_x_1027_, uint8_t v_bi_1028_, lean_object* v_t_1029_, lean_object* v_b_1030_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1025_, v_inst_1026_, v_x_1027_, v_bi_1028_, v_t_1029_, v_b_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLambdaS_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1025_ = stack[1].m_obj;
lean_object* v_inst_1026_ = stack[2].m_obj;
lean_object* v_x_1027_ = stack[3].m_obj;
uint8_t v_bi_1028_ = stack[4].m_num;
lean_object* v_t_1029_ = stack[5].m_obj;
lean_object* v_b_1030_ = stack[6].m_obj;
lean_object* v_res_1032_;
v_res_1032_ = l_Lean_Meta_Sym_Internal_mkLambdaS(lean_box(0), v_inst_1025_, v_inst_1026_, v_x_1027_, v_bi_1028_, v_t_1029_, v_b_1030_);
stack->m_obj
 = v_res_1032_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(lean_object* v_m_1033_, lean_object* v_inst_1034_, lean_object* v_inst_1035_, lean_object* v_x_1036_, lean_object* v_bi_1037_, lean_object* v_t_1038_, lean_object* v_b_1039_){
_start:
{
uint8_t v_bi_boxed_1040_; lean_object* v_res_1041_; 
v_bi_boxed_1040_ = lean_unbox(v_bi_1037_);
v_res_1041_ = l_Lean_Meta_Sym_Internal_mkLambdaS(v_m_1033_, v_inst_1034_, v_inst_1035_, v_x_1036_, v_bi_boxed_1040_, v_t_1038_, v_b_1039_);
return v_res_1041_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(lean_object* v_x_1042_, lean_object* v_t_1043_, lean_object* v_b_1044_, uint8_t v_bi_1045_, lean_object* v_share1_1046_, lean_object* v_____r_1047_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = l_Lean_Expr_forallE___override(v_x_1042_, v_t_1043_, v_b_1044_, v_bi_1045_);
v___x_1049_ = lean_apply_1(v_share1_1046_, v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1042_ = stack[0].m_obj;
lean_object* v_t_1043_ = stack[1].m_obj;
lean_object* v_b_1044_ = stack[2].m_obj;
uint8_t v_bi_1045_ = stack[3].m_num;
lean_object* v_share1_1046_ = stack[4].m_obj;
lean_object* v_____r_1047_ = stack[5].m_obj;
lean_object* v_res_1050_;
v_res_1050_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(v_x_1042_, v_t_1043_, v_b_1044_, v_bi_1045_, v_share1_1046_, v_____r_1047_);
stack->m_obj
 = v_res_1050_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(lean_object* v_x_1051_, lean_object* v_t_1052_, lean_object* v_b_1053_, lean_object* v_bi_1054_, lean_object* v_share1_1055_, lean_object* v_____r_1056_){
_start:
{
uint8_t v_bi_boxed_1057_; lean_object* v_res_1058_; 
v_bi_boxed_1057_ = lean_unbox(v_bi_1054_);
v_res_1058_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(v_x_1051_, v_t_1052_, v_b_1053_, v_bi_boxed_1057_, v_share1_1055_, v_____r_1056_);
return v_res_1058_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_x_1061_, uint8_t v_bi_1062_, lean_object* v_t_1063_, lean_object* v_b_1064_){
_start:
{
lean_object* v_toBind_1065_; lean_object* v_share1_1066_; lean_object* v_assertShared_1067_; lean_object* v_isDebugEnabled_1068_; lean_object* v___x_1069_; lean_object* v___f_1070_; lean_object* v___f_1071_; lean_object* v___f_1072_; lean_object* v___x_1073_; 
v_toBind_1065_ = lean_ctor_get(v_inst_1060_, 1);
lean_inc_n(v_toBind_1065_, 2);
lean_dec_ref(v_inst_1060_);
v_share1_1066_ = lean_ctor_get(v_inst_1059_, 0);
lean_inc(v_share1_1066_);
v_assertShared_1067_ = lean_ctor_get(v_inst_1059_, 1);
lean_inc(v_assertShared_1067_);
v_isDebugEnabled_1068_ = lean_ctor_get(v_inst_1059_, 2);
lean_inc(v_isDebugEnabled_1068_);
lean_dec_ref(v_inst_1059_);
v___x_1069_ = lean_box(v_bi_1062_);
lean_inc_ref(v_b_1064_);
lean_inc_ref(v_t_1063_);
v___f_1070_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1070_, 0, v_x_1061_);
lean_closure_set(v___f_1070_, 1, v_t_1063_);
lean_closure_set(v___f_1070_, 2, v_b_1064_);
lean_closure_set(v___f_1070_, 3, v___x_1069_);
lean_closure_set(v___f_1070_, 4, v_share1_1066_);
lean_inc_ref(v___f_1070_);
v___f_1071_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1071_, 0, v___f_1070_);
v___f_1072_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1072_, 0, v___f_1070_);
lean_closure_set(v___f_1072_, 1, v_assertShared_1067_);
lean_closure_set(v___f_1072_, 2, v_b_1064_);
lean_closure_set(v___f_1072_, 3, v_toBind_1065_);
lean_closure_set(v___f_1072_, 4, v___f_1071_);
lean_closure_set(v___f_1072_, 5, v_t_1063_);
v___x_1073_ = lean_apply_4(v_toBind_1065_, lean_box(0), lean_box(0), v_isDebugEnabled_1068_, v___f_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1059_ = stack[0].m_obj;
lean_object* v_inst_1060_ = stack[1].m_obj;
lean_object* v_x_1061_ = stack[2].m_obj;
uint8_t v_bi_1062_ = stack[3].m_num;
lean_object* v_t_1063_ = stack[4].m_obj;
lean_object* v_b_1064_ = stack[5].m_obj;
lean_object* v_res_1074_;
v_res_1074_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1059_, v_inst_1060_, v_x_1061_, v_bi_1062_, v_t_1063_, v_b_1064_);
stack->m_obj
 = v_res_1074_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_x_1077_, lean_object* v_bi_1078_, lean_object* v_t_1079_, lean_object* v_b_1080_){
_start:
{
uint8_t v_bi_boxed_1081_; lean_object* v_res_1082_; 
v_bi_boxed_1081_ = lean_unbox(v_bi_1078_);
v_res_1082_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1075_, v_inst_1076_, v_x_1077_, v_bi_boxed_1081_, v_t_1079_, v_b_1080_);
return v_res_1082_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS(lean_object* v_m_1083_, lean_object* v_inst_1084_, lean_object* v_inst_1085_, lean_object* v_x_1086_, uint8_t v_bi_1087_, lean_object* v_t_1088_, lean_object* v_b_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1084_, v_inst_1085_, v_x_1086_, v_bi_1087_, v_t_1088_, v_b_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1084_ = stack[1].m_obj;
lean_object* v_inst_1085_ = stack[2].m_obj;
lean_object* v_x_1086_ = stack[3].m_obj;
uint8_t v_bi_1087_ = stack[4].m_num;
lean_object* v_t_1088_ = stack[5].m_obj;
lean_object* v_b_1089_ = stack[6].m_obj;
lean_object* v_res_1091_;
v_res_1091_ = l_Lean_Meta_Sym_Internal_mkForallS(lean_box(0), v_inst_1084_, v_inst_1085_, v_x_1086_, v_bi_1087_, v_t_1088_, v_b_1089_);
stack->m_obj
 = v_res_1091_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___boxed(lean_object* v_m_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_x_1095_, lean_object* v_bi_1096_, lean_object* v_t_1097_, lean_object* v_b_1098_){
_start:
{
uint8_t v_bi_boxed_1099_; lean_object* v_res_1100_; 
v_bi_boxed_1099_ = lean_unbox(v_bi_1096_);
v_res_1100_ = l_Lean_Meta_Sym_Internal_mkForallS(v_m_1092_, v_inst_1093_, v_inst_1094_, v_x_1095_, v_bi_boxed_1099_, v_t_1097_, v_b_1098_);
return v_res_1100_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(lean_object* v_x_1101_, lean_object* v_t_1102_, lean_object* v_v_1103_, lean_object* v_b_1104_, uint8_t v_nondep_1105_, lean_object* v_share1_1106_, lean_object* v_____r_1107_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = l_Lean_Expr_letE___override(v_x_1101_, v_t_1102_, v_v_1103_, v_b_1104_, v_nondep_1105_);
v___x_1109_ = lean_apply_1(v_share1_1106_, v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1101_ = stack[0].m_obj;
lean_object* v_t_1102_ = stack[1].m_obj;
lean_object* v_v_1103_ = stack[2].m_obj;
lean_object* v_b_1104_ = stack[3].m_obj;
uint8_t v_nondep_1105_ = stack[4].m_num;
lean_object* v_share1_1106_ = stack[5].m_obj;
lean_object* v_____r_1107_ = stack[6].m_obj;
lean_object* v_res_1110_;
v_res_1110_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(v_x_1101_, v_t_1102_, v_v_1103_, v_b_1104_, v_nondep_1105_, v_share1_1106_, v_____r_1107_);
stack->m_obj
 = v_res_1110_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(lean_object* v_x_1111_, lean_object* v_t_1112_, lean_object* v_v_1113_, lean_object* v_b_1114_, lean_object* v_nondep_1115_, lean_object* v_share1_1116_, lean_object* v_____r_1117_){
_start:
{
uint8_t v_nondep_boxed_1118_; lean_object* v_res_1119_; 
v_nondep_boxed_1118_ = lean_unbox(v_nondep_1115_);
v_res_1119_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(v_x_1111_, v_t_1112_, v_v_1113_, v_b_1114_, v_nondep_boxed_1118_, v_share1_1116_, v_____r_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(lean_object* v_assertShared_1120_, lean_object* v_v_1121_, lean_object* v_toBind_1122_, lean_object* v___f_1123_, lean_object* v_____r_1124_){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_apply_1(v_assertShared_1120_, v_v_1121_);
v___x_1126_ = lean_apply_4(v_toBind_1122_, lean_box(0), lean_box(0), v___x_1125_, v___f_1123_);
return v___x_1126_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(lean_object* v___f_1127_, lean_object* v_assertShared_1128_, lean_object* v_b_1129_, lean_object* v_toBind_1130_, lean_object* v___f_1131_, lean_object* v_v_1132_, lean_object* v_t_1133_, uint8_t v_____do__lift_1134_){
_start:
{
if (v_____do__lift_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec_ref(v_t_1133_);
lean_dec_ref(v_v_1132_);
lean_dec(v___f_1131_);
lean_dec(v_toBind_1130_);
lean_dec_ref(v_b_1129_);
lean_dec(v_assertShared_1128_);
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_apply_1(v___f_1127_, v___x_1135_);
return v___x_1136_;
}
else
{
lean_object* v___f_1137_; lean_object* v___f_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec(v___f_1127_);
lean_inc_n(v_toBind_1130_, 2);
lean_inc_n(v_assertShared_1128_, 2);
v___f_1137_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1137_, 0, v_assertShared_1128_);
lean_closure_set(v___f_1137_, 1, v_b_1129_);
lean_closure_set(v___f_1137_, 2, v_toBind_1130_);
lean_closure_set(v___f_1137_, 3, v___f_1131_);
v___f_1138_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1138_, 0, v_assertShared_1128_);
lean_closure_set(v___f_1138_, 1, v_v_1132_);
lean_closure_set(v___f_1138_, 2, v_toBind_1130_);
lean_closure_set(v___f_1138_, 3, v___f_1137_);
v___x_1139_ = lean_apply_1(v_assertShared_1128_, v_t_1133_);
v___x_1140_ = lean_apply_4(v_toBind_1130_, lean_box(0), lean_box(0), v___x_1139_, v___f_1138_);
return v___x_1140_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1127_ = stack[0].m_obj;
lean_object* v_assertShared_1128_ = stack[1].m_obj;
lean_object* v_b_1129_ = stack[2].m_obj;
lean_object* v_toBind_1130_ = stack[3].m_obj;
lean_object* v___f_1131_ = stack[4].m_obj;
lean_object* v_v_1132_ = stack[5].m_obj;
lean_object* v_t_1133_ = stack[6].m_obj;
uint8_t v_____do__lift_1134_ = stack[7].m_num;
lean_object* v_res_1141_;
v_res_1141_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(v___f_1127_, v_assertShared_1128_, v_b_1129_, v_toBind_1130_, v___f_1131_, v_v_1132_, v_t_1133_, v_____do__lift_1134_);
stack->m_obj
 = v_res_1141_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(lean_object* v___f_1142_, lean_object* v_assertShared_1143_, lean_object* v_b_1144_, lean_object* v_toBind_1145_, lean_object* v___f_1146_, lean_object* v_v_1147_, lean_object* v_t_1148_, lean_object* v_____do__lift_1149_){
_start:
{
uint8_t v_____do__lift_92__boxed_1150_; lean_object* v_res_1151_; 
v_____do__lift_92__boxed_1150_ = lean_unbox(v_____do__lift_1149_);
v_res_1151_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(v___f_1142_, v_assertShared_1143_, v_b_1144_, v_toBind_1145_, v___f_1146_, v_v_1147_, v_t_1148_, v_____do__lift_92__boxed_1150_);
return v_res_1151_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_x_1154_, lean_object* v_t_1155_, lean_object* v_v_1156_, lean_object* v_b_1157_, uint8_t v_nondep_1158_){
_start:
{
lean_object* v_toBind_1159_; lean_object* v_share1_1160_; lean_object* v_assertShared_1161_; lean_object* v_isDebugEnabled_1162_; lean_object* v___x_1163_; lean_object* v___f_1164_; lean_object* v___f_1165_; lean_object* v___f_1166_; lean_object* v___x_1167_; 
v_toBind_1159_ = lean_ctor_get(v_inst_1153_, 1);
lean_inc_n(v_toBind_1159_, 2);
lean_dec_ref(v_inst_1153_);
v_share1_1160_ = lean_ctor_get(v_inst_1152_, 0);
lean_inc(v_share1_1160_);
v_assertShared_1161_ = lean_ctor_get(v_inst_1152_, 1);
lean_inc(v_assertShared_1161_);
v_isDebugEnabled_1162_ = lean_ctor_get(v_inst_1152_, 2);
lean_inc(v_isDebugEnabled_1162_);
lean_dec_ref(v_inst_1152_);
v___x_1163_ = lean_box(v_nondep_1158_);
lean_inc_ref(v_b_1157_);
lean_inc_ref(v_v_1156_);
lean_inc_ref(v_t_1155_);
v___f_1164_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1164_, 0, v_x_1154_);
lean_closure_set(v___f_1164_, 1, v_t_1155_);
lean_closure_set(v___f_1164_, 2, v_v_1156_);
lean_closure_set(v___f_1164_, 3, v_b_1157_);
lean_closure_set(v___f_1164_, 4, v___x_1163_);
lean_closure_set(v___f_1164_, 5, v_share1_1160_);
lean_inc_ref(v___f_1164_);
v___f_1165_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1165_, 0, v___f_1164_);
v___f_1166_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1166_, 0, v___f_1164_);
lean_closure_set(v___f_1166_, 1, v_assertShared_1161_);
lean_closure_set(v___f_1166_, 2, v_b_1157_);
lean_closure_set(v___f_1166_, 3, v_toBind_1159_);
lean_closure_set(v___f_1166_, 4, v___f_1165_);
lean_closure_set(v___f_1166_, 5, v_v_1156_);
lean_closure_set(v___f_1166_, 6, v_t_1155_);
v___x_1167_ = lean_apply_4(v_toBind_1159_, lean_box(0), lean_box(0), v_isDebugEnabled_1162_, v___f_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLetS___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1152_ = stack[0].m_obj;
lean_object* v_inst_1153_ = stack[1].m_obj;
lean_object* v_x_1154_ = stack[2].m_obj;
lean_object* v_t_1155_ = stack[3].m_obj;
lean_object* v_v_1156_ = stack[4].m_obj;
lean_object* v_b_1157_ = stack[5].m_obj;
uint8_t v_nondep_1158_ = stack[6].m_num;
lean_object* v_res_1168_;
v_res_1168_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1152_, v_inst_1153_, v_x_1154_, v_t_1155_, v_v_1156_, v_b_1157_, v_nondep_1158_);
stack->m_obj
 = v_res_1168_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_x_1171_, lean_object* v_t_1172_, lean_object* v_v_1173_, lean_object* v_b_1174_, lean_object* v_nondep_1175_){
_start:
{
uint8_t v_nondep_boxed_1176_; lean_object* v_res_1177_; 
v_nondep_boxed_1176_ = lean_unbox(v_nondep_1175_);
v_res_1177_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1169_, v_inst_1170_, v_x_1171_, v_t_1172_, v_v_1173_, v_b_1174_, v_nondep_boxed_1176_);
return v_res_1177_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLetS(lean_object* v_m_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_x_1181_, lean_object* v_t_1182_, lean_object* v_v_1183_, lean_object* v_b_1184_, uint8_t v_nondep_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1179_, v_inst_1180_, v_x_1181_, v_t_1182_, v_v_1183_, v_b_1184_, v_nondep_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLetS_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1179_ = stack[1].m_obj;
lean_object* v_inst_1180_ = stack[2].m_obj;
lean_object* v_x_1181_ = stack[3].m_obj;
lean_object* v_t_1182_ = stack[4].m_obj;
lean_object* v_v_1183_ = stack[5].m_obj;
lean_object* v_b_1184_ = stack[6].m_obj;
uint8_t v_nondep_1185_ = stack[7].m_num;
lean_object* v_res_1187_;
v_res_1187_ = l_Lean_Meta_Sym_Internal_mkLetS(lean_box(0), v_inst_1179_, v_inst_1180_, v_x_1181_, v_t_1182_, v_v_1183_, v_b_1184_, v_nondep_1185_);
stack->m_obj
 = v_res_1187_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___boxed(lean_object* v_m_1188_, lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_x_1191_, lean_object* v_t_1192_, lean_object* v_v_1193_, lean_object* v_b_1194_, lean_object* v_nondep_1195_){
_start:
{
uint8_t v_nondep_boxed_1196_; lean_object* v_res_1197_; 
v_nondep_boxed_1196_ = lean_unbox(v_nondep_1195_);
v_res_1197_ = l_Lean_Meta_Sym_Internal_mkLetS(v_m_1188_, v_inst_1189_, v_inst_1190_, v_x_1191_, v_t_1192_, v_v_1193_, v_b_1194_, v_nondep_boxed_1196_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(lean_object* v_x_1198_, lean_object* v_t_1199_, lean_object* v_v_1200_, lean_object* v_b_1201_, lean_object* v_share1_1202_, lean_object* v_____r_1203_){
_start:
{
uint8_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = 1;
v___x_1205_ = l_Lean_Expr_letE___override(v_x_1198_, v_t_1199_, v_v_1200_, v_b_1201_, v___x_1204_);
v___x_1206_ = lean_apply_1(v_share1_1202_, v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg(lean_object* v_inst_1207_, lean_object* v_inst_1208_, lean_object* v_x_1209_, lean_object* v_t_1210_, lean_object* v_v_1211_, lean_object* v_b_1212_){
_start:
{
lean_object* v_toBind_1213_; lean_object* v_share1_1214_; lean_object* v_assertShared_1215_; lean_object* v_isDebugEnabled_1216_; lean_object* v___f_1217_; lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___x_1220_; 
v_toBind_1213_ = lean_ctor_get(v_inst_1208_, 1);
lean_inc_n(v_toBind_1213_, 2);
lean_dec_ref(v_inst_1208_);
v_share1_1214_ = lean_ctor_get(v_inst_1207_, 0);
lean_inc(v_share1_1214_);
v_assertShared_1215_ = lean_ctor_get(v_inst_1207_, 1);
lean_inc(v_assertShared_1215_);
v_isDebugEnabled_1216_ = lean_ctor_get(v_inst_1207_, 2);
lean_inc(v_isDebugEnabled_1216_);
lean_dec_ref(v_inst_1207_);
lean_inc_ref(v_b_1212_);
lean_inc_ref(v_v_1211_);
lean_inc_ref(v_t_1210_);
v___f_1217_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1217_, 0, v_x_1209_);
lean_closure_set(v___f_1217_, 1, v_t_1210_);
lean_closure_set(v___f_1217_, 2, v_v_1211_);
lean_closure_set(v___f_1217_, 3, v_b_1212_);
lean_closure_set(v___f_1217_, 4, v_share1_1214_);
lean_inc_ref(v___f_1217_);
v___f_1218_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1218_, 0, v___f_1217_);
v___f_1219_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1219_, 0, v___f_1217_);
lean_closure_set(v___f_1219_, 1, v_assertShared_1215_);
lean_closure_set(v___f_1219_, 2, v_b_1212_);
lean_closure_set(v___f_1219_, 3, v_toBind_1213_);
lean_closure_set(v___f_1219_, 4, v___f_1218_);
lean_closure_set(v___f_1219_, 5, v_v_1211_);
lean_closure_set(v___f_1219_, 6, v_t_1210_);
v___x_1220_ = lean_apply_4(v_toBind_1213_, lean_box(0), lean_box(0), v_isDebugEnabled_1216_, v___f_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS(lean_object* v_m_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_x_1224_, lean_object* v_t_1225_, lean_object* v_v_1226_, lean_object* v_b_1227_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Meta_Sym_Internal_mkHaveS___redArg(v_inst_1222_, v_inst_1223_, v_x_1224_, v_t_1225_, v_v_1226_, v_b_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1231_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__1));
v___x_1232_ = lean_unsigned_to_nat(25u);
v___x_1233_ = lean_unsigned_to_nat(148u);
v___x_1234_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__0));
v___x_1235_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1236_ = l_mkPanicMessageWithDecl(v___x_1235_, v___x_1234_, v___x_1233_, v___x_1232_, v___x_1231_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21___redArg(lean_object* v_inst_1237_, lean_object* v_inst_1238_, lean_object* v_e_1239_, lean_object* v_newFn_1240_, lean_object* v_newArg_1241_){
_start:
{
if (lean_obj_tag(v_e_1239_) == 5)
{
lean_object* v_toApplicative_1242_; lean_object* v_toPure_1243_; lean_object* v_fn_1244_; lean_object* v_arg_1245_; size_t v___x_1246_; size_t v___x_1247_; uint8_t v___x_1248_; 
v_toApplicative_1242_ = lean_ctor_get(v_inst_1238_, 0);
v_toPure_1243_ = lean_ctor_get(v_toApplicative_1242_, 1);
v_fn_1244_ = lean_ctor_get(v_e_1239_, 0);
v_arg_1245_ = lean_ctor_get(v_e_1239_, 1);
v___x_1246_ = lean_ptr_addr(v_fn_1244_);
v___x_1247_ = lean_ptr_addr(v_newFn_1240_);
v___x_1248_ = lean_usize_dec_eq(v___x_1246_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; 
lean_dec_ref_known(v_e_1239_, 2);
v___x_1249_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1237_, v_inst_1238_, v_newFn_1240_, v_newArg_1241_);
return v___x_1249_;
}
else
{
size_t v___x_1250_; size_t v___x_1251_; uint8_t v___x_1252_; 
v___x_1250_ = lean_ptr_addr(v_arg_1245_);
v___x_1251_ = lean_ptr_addr(v_newArg_1241_);
v___x_1252_ = lean_usize_dec_eq(v___x_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_dec_ref_known(v_e_1239_, 2);
v___x_1253_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1237_, v_inst_1238_, v_newFn_1240_, v_newArg_1241_);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; 
lean_inc(v_toPure_1243_);
lean_dec_ref(v_newArg_1241_);
lean_dec_ref(v_newFn_1240_);
lean_dec_ref(v_inst_1238_);
lean_dec_ref(v_inst_1237_);
v___x_1254_ = lean_apply_2(v_toPure_1243_, lean_box(0), v_e_1239_);
return v___x_1254_;
}
}
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_dec_ref(v_newArg_1241_);
lean_dec_ref(v_newFn_1240_);
lean_dec_ref(v_e_1239_);
lean_dec_ref(v_inst_1237_);
v___x_1255_ = l_Lean_instInhabitedExpr;
v___x_1256_ = l_instInhabitedOfMonad___redArg(v_inst_1238_, v___x_1255_);
v___x_1257_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1258_ = l_panic___redArg(v___x_1256_, v___x_1257_);
lean_dec(v___x_1256_);
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21(lean_object* v_m_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_e_1262_, lean_object* v_newFn_1263_, lean_object* v_newArg_1264_){
_start:
{
if (lean_obj_tag(v_e_1262_) == 5)
{
lean_object* v_toApplicative_1265_; lean_object* v_toPure_1266_; lean_object* v_fn_1267_; lean_object* v_arg_1268_; size_t v___x_1269_; size_t v___x_1270_; uint8_t v___x_1271_; 
v_toApplicative_1265_ = lean_ctor_get(v_inst_1261_, 0);
v_toPure_1266_ = lean_ctor_get(v_toApplicative_1265_, 1);
v_fn_1267_ = lean_ctor_get(v_e_1262_, 0);
v_arg_1268_ = lean_ctor_get(v_e_1262_, 1);
v___x_1269_ = lean_ptr_addr(v_fn_1267_);
v___x_1270_ = lean_ptr_addr(v_newFn_1263_);
v___x_1271_ = lean_usize_dec_eq(v___x_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; 
lean_dec_ref_known(v_e_1262_, 2);
v___x_1272_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1260_, v_inst_1261_, v_newFn_1263_, v_newArg_1264_);
return v___x_1272_;
}
else
{
size_t v___x_1273_; size_t v___x_1274_; uint8_t v___x_1275_; 
v___x_1273_ = lean_ptr_addr(v_arg_1268_);
v___x_1274_ = lean_ptr_addr(v_newArg_1264_);
v___x_1275_ = lean_usize_dec_eq(v___x_1273_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; 
lean_dec_ref_known(v_e_1262_, 2);
v___x_1276_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1260_, v_inst_1261_, v_newFn_1263_, v_newArg_1264_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; 
lean_inc(v_toPure_1266_);
lean_dec_ref(v_newArg_1264_);
lean_dec_ref(v_newFn_1263_);
lean_dec_ref(v_inst_1261_);
lean_dec_ref(v_inst_1260_);
v___x_1277_ = lean_apply_2(v_toPure_1266_, lean_box(0), v_e_1262_);
return v___x_1277_;
}
}
}
else
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec_ref(v_newArg_1264_);
lean_dec_ref(v_newFn_1263_);
lean_dec_ref(v_e_1262_);
lean_dec_ref(v_inst_1260_);
v___x_1278_ = l_Lean_instInhabitedExpr;
v___x_1279_ = l_instInhabitedOfMonad___redArg(v_inst_1261_, v___x_1278_);
v___x_1280_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1281_ = l_panic___redArg(v___x_1279_, v___x_1280_);
lean_dec(v___x_1279_);
return v___x_1281_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1284_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__1));
v___x_1285_ = lean_unsigned_to_nat(24u);
v___x_1286_ = lean_unsigned_to_nat(152u);
v___x_1287_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__0));
v___x_1288_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1289_ = l_mkPanicMessageWithDecl(v___x_1288_, v___x_1287_, v___x_1286_, v___x_1285_, v___x_1284_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21___redArg(lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_e_1292_, lean_object* v_newExpr_1293_){
_start:
{
if (lean_obj_tag(v_e_1292_) == 10)
{
lean_object* v_toApplicative_1294_; lean_object* v_toPure_1295_; lean_object* v_data_1296_; lean_object* v_expr_1297_; size_t v___x_1298_; size_t v___x_1299_; uint8_t v___x_1300_; 
v_toApplicative_1294_ = lean_ctor_get(v_inst_1291_, 0);
v_toPure_1295_ = lean_ctor_get(v_toApplicative_1294_, 1);
v_data_1296_ = lean_ctor_get(v_e_1292_, 0);
v_expr_1297_ = lean_ctor_get(v_e_1292_, 1);
v___x_1298_ = lean_ptr_addr(v_expr_1297_);
v___x_1299_ = lean_ptr_addr(v_newExpr_1293_);
v___x_1300_ = lean_usize_dec_eq(v___x_1298_, v___x_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; 
lean_inc(v_data_1296_);
lean_dec_ref_known(v_e_1292_, 2);
v___x_1301_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1290_, v_inst_1291_, v_data_1296_, v_newExpr_1293_);
return v___x_1301_;
}
else
{
lean_object* v___x_1302_; 
lean_inc(v_toPure_1295_);
lean_dec_ref(v_newExpr_1293_);
lean_dec_ref(v_inst_1291_);
lean_dec_ref(v_inst_1290_);
v___x_1302_ = lean_apply_2(v_toPure_1295_, lean_box(0), v_e_1292_);
return v___x_1302_;
}
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_dec_ref(v_newExpr_1293_);
lean_dec_ref(v_e_1292_);
lean_dec_ref(v_inst_1290_);
v___x_1303_ = l_Lean_instInhabitedExpr;
v___x_1304_ = l_instInhabitedOfMonad___redArg(v_inst_1291_, v___x_1303_);
v___x_1305_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1306_ = l_panic___redArg(v___x_1304_, v___x_1305_);
lean_dec(v___x_1304_);
return v___x_1306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21(lean_object* v_m_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_e_1310_, lean_object* v_newExpr_1311_){
_start:
{
if (lean_obj_tag(v_e_1310_) == 10)
{
lean_object* v_toApplicative_1312_; lean_object* v_toPure_1313_; lean_object* v_data_1314_; lean_object* v_expr_1315_; size_t v___x_1316_; size_t v___x_1317_; uint8_t v___x_1318_; 
v_toApplicative_1312_ = lean_ctor_get(v_inst_1309_, 0);
v_toPure_1313_ = lean_ctor_get(v_toApplicative_1312_, 1);
v_data_1314_ = lean_ctor_get(v_e_1310_, 0);
v_expr_1315_ = lean_ctor_get(v_e_1310_, 1);
v___x_1316_ = lean_ptr_addr(v_expr_1315_);
v___x_1317_ = lean_ptr_addr(v_newExpr_1311_);
v___x_1318_ = lean_usize_dec_eq(v___x_1316_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
lean_inc(v_data_1314_);
lean_dec_ref_known(v_e_1310_, 2);
v___x_1319_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1308_, v_inst_1309_, v_data_1314_, v_newExpr_1311_);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; 
lean_inc(v_toPure_1313_);
lean_dec_ref(v_newExpr_1311_);
lean_dec_ref(v_inst_1309_);
lean_dec_ref(v_inst_1308_);
v___x_1320_ = lean_apply_2(v_toPure_1313_, lean_box(0), v_e_1310_);
return v___x_1320_;
}
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec_ref(v_newExpr_1311_);
lean_dec_ref(v_e_1310_);
lean_dec_ref(v_inst_1308_);
v___x_1321_ = l_Lean_instInhabitedExpr;
v___x_1322_ = l_instInhabitedOfMonad___redArg(v_inst_1309_, v___x_1321_);
v___x_1323_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1324_ = l_panic___redArg(v___x_1322_, v___x_1323_);
lean_dec(v___x_1322_);
return v___x_1324_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1327_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__1));
v___x_1328_ = lean_unsigned_to_nat(25u);
v___x_1329_ = lean_unsigned_to_nat(156u);
v___x_1330_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__0));
v___x_1331_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1332_ = l_mkPanicMessageWithDecl(v___x_1331_, v___x_1330_, v___x_1329_, v___x_1328_, v___x_1327_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21___redArg(lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_e_1335_, lean_object* v_newExpr_1336_){
_start:
{
if (lean_obj_tag(v_e_1335_) == 11)
{
lean_object* v_toApplicative_1337_; lean_object* v_toPure_1338_; lean_object* v_typeName_1339_; lean_object* v_idx_1340_; lean_object* v_struct_1341_; size_t v___x_1342_; size_t v___x_1343_; uint8_t v___x_1344_; 
v_toApplicative_1337_ = lean_ctor_get(v_inst_1334_, 0);
v_toPure_1338_ = lean_ctor_get(v_toApplicative_1337_, 1);
v_typeName_1339_ = lean_ctor_get(v_e_1335_, 0);
v_idx_1340_ = lean_ctor_get(v_e_1335_, 1);
v_struct_1341_ = lean_ctor_get(v_e_1335_, 2);
v___x_1342_ = lean_ptr_addr(v_struct_1341_);
v___x_1343_ = lean_ptr_addr(v_newExpr_1336_);
v___x_1344_ = lean_usize_dec_eq(v___x_1342_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; 
lean_inc(v_idx_1340_);
lean_inc(v_typeName_1339_);
lean_dec_ref_known(v_e_1335_, 3);
v___x_1345_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1333_, v_inst_1334_, v_typeName_1339_, v_idx_1340_, v_newExpr_1336_);
return v___x_1345_;
}
else
{
lean_object* v___x_1346_; 
lean_inc(v_toPure_1338_);
lean_dec_ref(v_newExpr_1336_);
lean_dec_ref(v_inst_1334_);
lean_dec_ref(v_inst_1333_);
v___x_1346_ = lean_apply_2(v_toPure_1338_, lean_box(0), v_e_1335_);
return v___x_1346_;
}
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec_ref(v_newExpr_1336_);
lean_dec_ref(v_e_1335_);
lean_dec_ref(v_inst_1333_);
v___x_1347_ = l_Lean_instInhabitedExpr;
v___x_1348_ = l_instInhabitedOfMonad___redArg(v_inst_1334_, v___x_1347_);
v___x_1349_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1350_ = l_panic___redArg(v___x_1348_, v___x_1349_);
lean_dec(v___x_1348_);
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21(lean_object* v_m_1351_, lean_object* v_inst_1352_, lean_object* v_inst_1353_, lean_object* v_e_1354_, lean_object* v_newExpr_1355_){
_start:
{
if (lean_obj_tag(v_e_1354_) == 11)
{
lean_object* v_toApplicative_1356_; lean_object* v_toPure_1357_; lean_object* v_typeName_1358_; lean_object* v_idx_1359_; lean_object* v_struct_1360_; size_t v___x_1361_; size_t v___x_1362_; uint8_t v___x_1363_; 
v_toApplicative_1356_ = lean_ctor_get(v_inst_1353_, 0);
v_toPure_1357_ = lean_ctor_get(v_toApplicative_1356_, 1);
v_typeName_1358_ = lean_ctor_get(v_e_1354_, 0);
v_idx_1359_ = lean_ctor_get(v_e_1354_, 1);
v_struct_1360_ = lean_ctor_get(v_e_1354_, 2);
v___x_1361_ = lean_ptr_addr(v_struct_1360_);
v___x_1362_ = lean_ptr_addr(v_newExpr_1355_);
v___x_1363_ = lean_usize_dec_eq(v___x_1361_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
lean_inc(v_idx_1359_);
lean_inc(v_typeName_1358_);
lean_dec_ref_known(v_e_1354_, 3);
v___x_1364_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1352_, v_inst_1353_, v_typeName_1358_, v_idx_1359_, v_newExpr_1355_);
return v___x_1364_;
}
else
{
lean_object* v___x_1365_; 
lean_inc(v_toPure_1357_);
lean_dec_ref(v_newExpr_1355_);
lean_dec_ref(v_inst_1353_);
lean_dec_ref(v_inst_1352_);
v___x_1365_ = lean_apply_2(v_toPure_1357_, lean_box(0), v_e_1354_);
return v___x_1365_;
}
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec_ref(v_newExpr_1355_);
lean_dec_ref(v_e_1354_);
lean_dec_ref(v_inst_1352_);
v___x_1366_ = l_Lean_instInhabitedExpr;
v___x_1367_ = l_instInhabitedOfMonad___redArg(v_inst_1353_, v___x_1366_);
v___x_1368_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1369_ = l_panic___redArg(v___x_1367_, v___x_1368_);
lean_dec(v___x_1367_);
return v___x_1369_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1372_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__1));
v___x_1373_ = lean_unsigned_to_nat(31u);
v___x_1374_ = lean_unsigned_to_nat(160u);
v___x_1375_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__0));
v___x_1376_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1377_ = l_mkPanicMessageWithDecl(v___x_1376_, v___x_1375_, v___x_1374_, v___x_1373_, v___x_1372_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21___redArg(lean_object* v_inst_1378_, lean_object* v_inst_1379_, lean_object* v_e_1380_, lean_object* v_newDomain_1381_, lean_object* v_newBody_1382_){
_start:
{
if (lean_obj_tag(v_e_1380_) == 7)
{
lean_object* v_toApplicative_1383_; lean_object* v_toPure_1384_; lean_object* v_binderName_1385_; lean_object* v_binderType_1386_; lean_object* v_body_1387_; uint8_t v_binderInfo_1388_; size_t v___x_1389_; size_t v___x_1390_; uint8_t v___x_1391_; 
v_toApplicative_1383_ = lean_ctor_get(v_inst_1379_, 0);
v_toPure_1384_ = lean_ctor_get(v_toApplicative_1383_, 1);
v_binderName_1385_ = lean_ctor_get(v_e_1380_, 0);
v_binderType_1386_ = lean_ctor_get(v_e_1380_, 1);
v_body_1387_ = lean_ctor_get(v_e_1380_, 2);
v_binderInfo_1388_ = lean_ctor_get_uint8(v_e_1380_, sizeof(void*)*3 + 8);
v___x_1389_ = lean_ptr_addr(v_binderType_1386_);
v___x_1390_ = lean_ptr_addr(v_newDomain_1381_);
v___x_1391_ = lean_usize_dec_eq(v___x_1389_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; 
lean_inc(v_binderName_1385_);
lean_dec_ref_known(v_e_1380_, 3);
v___x_1392_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1378_, v_inst_1379_, v_binderName_1385_, v_binderInfo_1388_, v_newDomain_1381_, v_newBody_1382_);
return v___x_1392_;
}
else
{
size_t v___x_1393_; size_t v___x_1394_; uint8_t v___x_1395_; 
v___x_1393_ = lean_ptr_addr(v_body_1387_);
v___x_1394_ = lean_ptr_addr(v_newBody_1382_);
v___x_1395_ = lean_usize_dec_eq(v___x_1393_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
lean_inc(v_binderName_1385_);
lean_dec_ref_known(v_e_1380_, 3);
v___x_1396_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1378_, v_inst_1379_, v_binderName_1385_, v_binderInfo_1388_, v_newDomain_1381_, v_newBody_1382_);
return v___x_1396_;
}
else
{
lean_object* v___x_1397_; 
lean_inc(v_toPure_1384_);
lean_dec_ref(v_newBody_1382_);
lean_dec_ref(v_newDomain_1381_);
lean_dec_ref(v_inst_1379_);
lean_dec_ref(v_inst_1378_);
v___x_1397_ = lean_apply_2(v_toPure_1384_, lean_box(0), v_e_1380_);
return v___x_1397_;
}
}
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_dec_ref(v_newBody_1382_);
lean_dec_ref(v_newDomain_1381_);
lean_dec_ref(v_e_1380_);
lean_dec_ref(v_inst_1378_);
v___x_1398_ = l_Lean_instInhabitedExpr;
v___x_1399_ = l_instInhabitedOfMonad___redArg(v_inst_1379_, v___x_1398_);
v___x_1400_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1401_ = l_panic___redArg(v___x_1399_, v___x_1400_);
lean_dec(v___x_1399_);
return v___x_1401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21(lean_object* v_m_1402_, lean_object* v_inst_1403_, lean_object* v_inst_1404_, lean_object* v_e_1405_, lean_object* v_newDomain_1406_, lean_object* v_newBody_1407_){
_start:
{
if (lean_obj_tag(v_e_1405_) == 7)
{
lean_object* v_toApplicative_1408_; lean_object* v_toPure_1409_; lean_object* v_binderName_1410_; lean_object* v_binderType_1411_; lean_object* v_body_1412_; uint8_t v_binderInfo_1413_; size_t v___x_1414_; size_t v___x_1415_; uint8_t v___x_1416_; 
v_toApplicative_1408_ = lean_ctor_get(v_inst_1404_, 0);
v_toPure_1409_ = lean_ctor_get(v_toApplicative_1408_, 1);
v_binderName_1410_ = lean_ctor_get(v_e_1405_, 0);
v_binderType_1411_ = lean_ctor_get(v_e_1405_, 1);
v_body_1412_ = lean_ctor_get(v_e_1405_, 2);
v_binderInfo_1413_ = lean_ctor_get_uint8(v_e_1405_, sizeof(void*)*3 + 8);
v___x_1414_ = lean_ptr_addr(v_binderType_1411_);
v___x_1415_ = lean_ptr_addr(v_newDomain_1406_);
v___x_1416_ = lean_usize_dec_eq(v___x_1414_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
lean_inc(v_binderName_1410_);
lean_dec_ref_known(v_e_1405_, 3);
v___x_1417_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1403_, v_inst_1404_, v_binderName_1410_, v_binderInfo_1413_, v_newDomain_1406_, v_newBody_1407_);
return v___x_1417_;
}
else
{
size_t v___x_1418_; size_t v___x_1419_; uint8_t v___x_1420_; 
v___x_1418_ = lean_ptr_addr(v_body_1412_);
v___x_1419_ = lean_ptr_addr(v_newBody_1407_);
v___x_1420_ = lean_usize_dec_eq(v___x_1418_, v___x_1419_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; 
lean_inc(v_binderName_1410_);
lean_dec_ref_known(v_e_1405_, 3);
v___x_1421_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1403_, v_inst_1404_, v_binderName_1410_, v_binderInfo_1413_, v_newDomain_1406_, v_newBody_1407_);
return v___x_1421_;
}
else
{
lean_object* v___x_1422_; 
lean_inc(v_toPure_1409_);
lean_dec_ref(v_newBody_1407_);
lean_dec_ref(v_newDomain_1406_);
lean_dec_ref(v_inst_1404_);
lean_dec_ref(v_inst_1403_);
v___x_1422_ = lean_apply_2(v_toPure_1409_, lean_box(0), v_e_1405_);
return v___x_1422_;
}
}
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec_ref(v_newBody_1407_);
lean_dec_ref(v_newDomain_1406_);
lean_dec_ref(v_e_1405_);
lean_dec_ref(v_inst_1403_);
v___x_1423_ = l_Lean_instInhabitedExpr;
v___x_1424_ = l_instInhabitedOfMonad___redArg(v_inst_1404_, v___x_1423_);
v___x_1425_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1426_ = l_panic___redArg(v___x_1424_, v___x_1425_);
lean_dec(v___x_1424_);
return v___x_1426_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1429_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__1));
v___x_1430_ = lean_unsigned_to_nat(27u);
v___x_1431_ = lean_unsigned_to_nat(167u);
v___x_1432_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__0));
v___x_1433_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1434_ = l_mkPanicMessageWithDecl(v___x_1433_, v___x_1432_, v___x_1431_, v___x_1430_, v___x_1429_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21___redArg(lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_e_1437_, lean_object* v_newDomain_1438_, lean_object* v_newBody_1439_){
_start:
{
if (lean_obj_tag(v_e_1437_) == 6)
{
lean_object* v_toApplicative_1440_; lean_object* v_toPure_1441_; lean_object* v_binderName_1442_; lean_object* v_binderType_1443_; lean_object* v_body_1444_; uint8_t v_binderInfo_1445_; size_t v___x_1446_; size_t v___x_1447_; uint8_t v___x_1448_; 
v_toApplicative_1440_ = lean_ctor_get(v_inst_1436_, 0);
v_toPure_1441_ = lean_ctor_get(v_toApplicative_1440_, 1);
v_binderName_1442_ = lean_ctor_get(v_e_1437_, 0);
v_binderType_1443_ = lean_ctor_get(v_e_1437_, 1);
v_body_1444_ = lean_ctor_get(v_e_1437_, 2);
v_binderInfo_1445_ = lean_ctor_get_uint8(v_e_1437_, sizeof(void*)*3 + 8);
v___x_1446_ = lean_ptr_addr(v_binderType_1443_);
v___x_1447_ = lean_ptr_addr(v_newDomain_1438_);
v___x_1448_ = lean_usize_dec_eq(v___x_1446_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_inc(v_binderName_1442_);
lean_dec_ref_known(v_e_1437_, 3);
v___x_1449_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1435_, v_inst_1436_, v_binderName_1442_, v_binderInfo_1445_, v_newDomain_1438_, v_newBody_1439_);
return v___x_1449_;
}
else
{
size_t v___x_1450_; size_t v___x_1451_; uint8_t v___x_1452_; 
v___x_1450_ = lean_ptr_addr(v_body_1444_);
v___x_1451_ = lean_ptr_addr(v_newBody_1439_);
v___x_1452_ = lean_usize_dec_eq(v___x_1450_, v___x_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; 
lean_inc(v_binderName_1442_);
lean_dec_ref_known(v_e_1437_, 3);
v___x_1453_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1435_, v_inst_1436_, v_binderName_1442_, v_binderInfo_1445_, v_newDomain_1438_, v_newBody_1439_);
return v___x_1453_;
}
else
{
lean_object* v___x_1454_; 
lean_inc(v_toPure_1441_);
lean_dec_ref(v_newBody_1439_);
lean_dec_ref(v_newDomain_1438_);
lean_dec_ref(v_inst_1436_);
lean_dec_ref(v_inst_1435_);
v___x_1454_ = lean_apply_2(v_toPure_1441_, lean_box(0), v_e_1437_);
return v___x_1454_;
}
}
}
else
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec_ref(v_newBody_1439_);
lean_dec_ref(v_newDomain_1438_);
lean_dec_ref(v_e_1437_);
lean_dec_ref(v_inst_1435_);
v___x_1455_ = l_Lean_instInhabitedExpr;
v___x_1456_ = l_instInhabitedOfMonad___redArg(v_inst_1436_, v___x_1455_);
v___x_1457_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1458_ = l_panic___redArg(v___x_1456_, v___x_1457_);
lean_dec(v___x_1456_);
return v___x_1458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21(lean_object* v_m_1459_, lean_object* v_inst_1460_, lean_object* v_inst_1461_, lean_object* v_e_1462_, lean_object* v_newDomain_1463_, lean_object* v_newBody_1464_){
_start:
{
if (lean_obj_tag(v_e_1462_) == 6)
{
lean_object* v_toApplicative_1465_; lean_object* v_toPure_1466_; lean_object* v_binderName_1467_; lean_object* v_binderType_1468_; lean_object* v_body_1469_; uint8_t v_binderInfo_1470_; size_t v___x_1471_; size_t v___x_1472_; uint8_t v___x_1473_; 
v_toApplicative_1465_ = lean_ctor_get(v_inst_1461_, 0);
v_toPure_1466_ = lean_ctor_get(v_toApplicative_1465_, 1);
v_binderName_1467_ = lean_ctor_get(v_e_1462_, 0);
v_binderType_1468_ = lean_ctor_get(v_e_1462_, 1);
v_body_1469_ = lean_ctor_get(v_e_1462_, 2);
v_binderInfo_1470_ = lean_ctor_get_uint8(v_e_1462_, sizeof(void*)*3 + 8);
v___x_1471_ = lean_ptr_addr(v_binderType_1468_);
v___x_1472_ = lean_ptr_addr(v_newDomain_1463_);
v___x_1473_ = lean_usize_dec_eq(v___x_1471_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
lean_inc(v_binderName_1467_);
lean_dec_ref_known(v_e_1462_, 3);
v___x_1474_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1460_, v_inst_1461_, v_binderName_1467_, v_binderInfo_1470_, v_newDomain_1463_, v_newBody_1464_);
return v___x_1474_;
}
else
{
size_t v___x_1475_; size_t v___x_1476_; uint8_t v___x_1477_; 
v___x_1475_ = lean_ptr_addr(v_body_1469_);
v___x_1476_ = lean_ptr_addr(v_newBody_1464_);
v___x_1477_ = lean_usize_dec_eq(v___x_1475_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; 
lean_inc(v_binderName_1467_);
lean_dec_ref_known(v_e_1462_, 3);
v___x_1478_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1460_, v_inst_1461_, v_binderName_1467_, v_binderInfo_1470_, v_newDomain_1463_, v_newBody_1464_);
return v___x_1478_;
}
else
{
lean_object* v___x_1479_; 
lean_inc(v_toPure_1466_);
lean_dec_ref(v_newBody_1464_);
lean_dec_ref(v_newDomain_1463_);
lean_dec_ref(v_inst_1461_);
lean_dec_ref(v_inst_1460_);
v___x_1479_ = lean_apply_2(v_toPure_1466_, lean_box(0), v_e_1462_);
return v___x_1479_;
}
}
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec_ref(v_newBody_1464_);
lean_dec_ref(v_newDomain_1463_);
lean_dec_ref(v_e_1462_);
lean_dec_ref(v_inst_1460_);
v___x_1480_ = l_Lean_instInhabitedExpr;
v___x_1481_ = l_instInhabitedOfMonad___redArg(v_inst_1461_, v___x_1480_);
v___x_1482_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1483_ = l_panic___redArg(v___x_1481_, v___x_1482_);
lean_dec(v___x_1481_);
return v___x_1483_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1486_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__1));
v___x_1487_ = lean_unsigned_to_nat(34u);
v___x_1488_ = lean_unsigned_to_nat(174u);
v___x_1489_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__0));
v___x_1490_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1491_ = l_mkPanicMessageWithDecl(v___x_1490_, v___x_1489_, v___x_1488_, v___x_1487_, v___x_1486_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21___redArg(lean_object* v_inst_1492_, lean_object* v_inst_1493_, lean_object* v_e_1494_, lean_object* v_newType_1495_, lean_object* v_newVal_1496_, lean_object* v_newBody_1497_){
_start:
{
if (lean_obj_tag(v_e_1494_) == 8)
{
lean_object* v_toApplicative_1498_; lean_object* v_toPure_1499_; lean_object* v_declName_1500_; lean_object* v_type_1501_; lean_object* v_value_1502_; lean_object* v_body_1503_; uint8_t v_nondep_1504_; size_t v___x_1505_; size_t v___x_1506_; uint8_t v___x_1507_; 
v_toApplicative_1498_ = lean_ctor_get(v_inst_1493_, 0);
v_toPure_1499_ = lean_ctor_get(v_toApplicative_1498_, 1);
v_declName_1500_ = lean_ctor_get(v_e_1494_, 0);
v_type_1501_ = lean_ctor_get(v_e_1494_, 1);
v_value_1502_ = lean_ctor_get(v_e_1494_, 2);
v_body_1503_ = lean_ctor_get(v_e_1494_, 3);
v_nondep_1504_ = lean_ctor_get_uint8(v_e_1494_, sizeof(void*)*4 + 8);
v___x_1505_ = lean_ptr_addr(v_type_1501_);
v___x_1506_ = lean_ptr_addr(v_newType_1495_);
v___x_1507_ = lean_usize_dec_eq(v___x_1505_, v___x_1506_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; 
lean_inc(v_declName_1500_);
lean_dec_ref_known(v_e_1494_, 4);
v___x_1508_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1492_, v_inst_1493_, v_declName_1500_, v_newType_1495_, v_newVal_1496_, v_newBody_1497_, v_nondep_1504_);
return v___x_1508_;
}
else
{
size_t v___x_1509_; size_t v___x_1510_; uint8_t v___x_1511_; 
v___x_1509_ = lean_ptr_addr(v_value_1502_);
v___x_1510_ = lean_ptr_addr(v_newVal_1496_);
v___x_1511_ = lean_usize_dec_eq(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; 
lean_inc(v_declName_1500_);
lean_dec_ref_known(v_e_1494_, 4);
v___x_1512_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1492_, v_inst_1493_, v_declName_1500_, v_newType_1495_, v_newVal_1496_, v_newBody_1497_, v_nondep_1504_);
return v___x_1512_;
}
else
{
size_t v___x_1513_; size_t v___x_1514_; uint8_t v___x_1515_; 
v___x_1513_ = lean_ptr_addr(v_body_1503_);
v___x_1514_ = lean_ptr_addr(v_newBody_1497_);
v___x_1515_ = lean_usize_dec_eq(v___x_1513_, v___x_1514_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; 
lean_inc(v_declName_1500_);
lean_dec_ref_known(v_e_1494_, 4);
v___x_1516_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1492_, v_inst_1493_, v_declName_1500_, v_newType_1495_, v_newVal_1496_, v_newBody_1497_, v_nondep_1504_);
return v___x_1516_;
}
else
{
lean_object* v___x_1517_; 
lean_inc(v_toPure_1499_);
lean_dec_ref(v_newBody_1497_);
lean_dec_ref(v_newVal_1496_);
lean_dec_ref(v_newType_1495_);
lean_dec_ref(v_inst_1493_);
lean_dec_ref(v_inst_1492_);
v___x_1517_ = lean_apply_2(v_toPure_1499_, lean_box(0), v_e_1494_);
return v___x_1517_;
}
}
}
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_dec_ref(v_newBody_1497_);
lean_dec_ref(v_newVal_1496_);
lean_dec_ref(v_newType_1495_);
lean_dec_ref(v_e_1494_);
lean_dec_ref(v_inst_1492_);
v___x_1518_ = l_Lean_instInhabitedExpr;
v___x_1519_ = l_instInhabitedOfMonad___redArg(v_inst_1493_, v___x_1518_);
v___x_1520_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1521_ = l_panic___redArg(v___x_1519_, v___x_1520_);
lean_dec(v___x_1519_);
return v___x_1521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21(lean_object* v_m_1522_, lean_object* v_inst_1523_, lean_object* v_inst_1524_, lean_object* v_e_1525_, lean_object* v_newType_1526_, lean_object* v_newVal_1527_, lean_object* v_newBody_1528_){
_start:
{
if (lean_obj_tag(v_e_1525_) == 8)
{
lean_object* v_toApplicative_1529_; lean_object* v_toPure_1530_; lean_object* v_declName_1531_; lean_object* v_type_1532_; lean_object* v_value_1533_; lean_object* v_body_1534_; uint8_t v_nondep_1535_; size_t v___x_1536_; size_t v___x_1537_; uint8_t v___x_1538_; 
v_toApplicative_1529_ = lean_ctor_get(v_inst_1524_, 0);
v_toPure_1530_ = lean_ctor_get(v_toApplicative_1529_, 1);
v_declName_1531_ = lean_ctor_get(v_e_1525_, 0);
v_type_1532_ = lean_ctor_get(v_e_1525_, 1);
v_value_1533_ = lean_ctor_get(v_e_1525_, 2);
v_body_1534_ = lean_ctor_get(v_e_1525_, 3);
v_nondep_1535_ = lean_ctor_get_uint8(v_e_1525_, sizeof(void*)*4 + 8);
v___x_1536_ = lean_ptr_addr(v_type_1532_);
v___x_1537_ = lean_ptr_addr(v_newType_1526_);
v___x_1538_ = lean_usize_dec_eq(v___x_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; 
lean_inc(v_declName_1531_);
lean_dec_ref_known(v_e_1525_, 4);
v___x_1539_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1523_, v_inst_1524_, v_declName_1531_, v_newType_1526_, v_newVal_1527_, v_newBody_1528_, v_nondep_1535_);
return v___x_1539_;
}
else
{
size_t v___x_1540_; size_t v___x_1541_; uint8_t v___x_1542_; 
v___x_1540_ = lean_ptr_addr(v_value_1533_);
v___x_1541_ = lean_ptr_addr(v_newVal_1527_);
v___x_1542_ = lean_usize_dec_eq(v___x_1540_, v___x_1541_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; 
lean_inc(v_declName_1531_);
lean_dec_ref_known(v_e_1525_, 4);
v___x_1543_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1523_, v_inst_1524_, v_declName_1531_, v_newType_1526_, v_newVal_1527_, v_newBody_1528_, v_nondep_1535_);
return v___x_1543_;
}
else
{
size_t v___x_1544_; size_t v___x_1545_; uint8_t v___x_1546_; 
v___x_1544_ = lean_ptr_addr(v_body_1534_);
v___x_1545_ = lean_ptr_addr(v_newBody_1528_);
v___x_1546_ = lean_usize_dec_eq(v___x_1544_, v___x_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; 
lean_inc(v_declName_1531_);
lean_dec_ref_known(v_e_1525_, 4);
v___x_1547_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1523_, v_inst_1524_, v_declName_1531_, v_newType_1526_, v_newVal_1527_, v_newBody_1528_, v_nondep_1535_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; 
lean_inc(v_toPure_1530_);
lean_dec_ref(v_newBody_1528_);
lean_dec_ref(v_newVal_1527_);
lean_dec_ref(v_newType_1526_);
lean_dec_ref(v_inst_1524_);
lean_dec_ref(v_inst_1523_);
v___x_1548_ = lean_apply_2(v_toPure_1530_, lean_box(0), v_e_1525_);
return v___x_1548_;
}
}
}
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_dec_ref(v_newBody_1528_);
lean_dec_ref(v_newVal_1527_);
lean_dec_ref(v_newType_1526_);
lean_dec_ref(v_e_1525_);
lean_dec_ref(v_inst_1523_);
v___x_1549_ = l_Lean_instInhabitedExpr;
v___x_1550_ = l_instInhabitedOfMonad___redArg(v_inst_1524_, v___x_1549_);
v___x_1551_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1552_ = l_panic___redArg(v___x_1550_, v___x_1551_);
lean_dec(v___x_1550_);
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0(lean_object* v_inst_1553_, lean_object* v_inst_1554_, lean_object* v_a_u2082_1555_, lean_object* v_____do__lift_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1553_, v_inst_1554_, v_____do__lift_1556_, v_a_u2082_1555_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v_f_1560_, lean_object* v_a_u2081_1561_, lean_object* v_a_u2082_1562_){
_start:
{
lean_object* v_toBind_1563_; lean_object* v___f_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_toBind_1563_ = lean_ctor_get(v_inst_1559_, 1);
lean_inc(v_toBind_1563_);
lean_inc_ref(v_inst_1559_);
lean_inc_ref(v_inst_1558_);
v___f_1564_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1564_, 0, v_inst_1558_);
lean_closure_set(v___f_1564_, 1, v_inst_1559_);
lean_closure_set(v___f_1564_, 2, v_a_u2082_1562_);
v___x_1565_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1558_, v_inst_1559_, v_f_1560_, v_a_u2081_1561_);
v___x_1566_ = lean_apply_4(v_toBind_1563_, lean_box(0), lean_box(0), v___x_1565_, v___f_1564_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082(lean_object* v_m_1567_, lean_object* v_inst_1568_, lean_object* v_inst_1569_, lean_object* v_f_1570_, lean_object* v_a_u2081_1571_, lean_object* v_a_u2082_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1568_, v_inst_1569_, v_f_1570_, v_a_u2081_1571_, v_a_u2082_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0(lean_object* v_inst_1574_, lean_object* v_inst_1575_, lean_object* v_a_u2083_1576_, lean_object* v_____do__lift_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1574_, v_inst_1575_, v_____do__lift_1577_, v_a_u2083_1576_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(lean_object* v_inst_1579_, lean_object* v_inst_1580_, lean_object* v_f_1581_, lean_object* v_a_u2081_1582_, lean_object* v_a_u2082_1583_, lean_object* v_a_u2083_1584_){
_start:
{
lean_object* v_toBind_1585_; lean_object* v___f_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_toBind_1585_ = lean_ctor_get(v_inst_1580_, 1);
lean_inc(v_toBind_1585_);
lean_inc_ref(v_inst_1580_);
lean_inc_ref(v_inst_1579_);
v___f_1586_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1586_, 0, v_inst_1579_);
lean_closure_set(v___f_1586_, 1, v_inst_1580_);
lean_closure_set(v___f_1586_, 2, v_a_u2083_1584_);
v___x_1587_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1579_, v_inst_1580_, v_f_1581_, v_a_u2081_1582_, v_a_u2082_1583_);
v___x_1588_ = lean_apply_4(v_toBind_1585_, lean_box(0), lean_box(0), v___x_1587_, v___f_1586_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083(lean_object* v_m_1589_, lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_f_1592_, lean_object* v_a_u2081_1593_, lean_object* v_a_u2082_1594_, lean_object* v_a_u2083_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1590_, v_inst_1591_, v_f_1592_, v_a_u2081_1593_, v_a_u2082_1594_, v_a_u2083_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0(lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_a_u2084_1599_, lean_object* v_____do__lift_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1597_, v_inst_1598_, v_____do__lift_1600_, v_a_u2084_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(lean_object* v_inst_1602_, lean_object* v_inst_1603_, lean_object* v_f_1604_, lean_object* v_a_u2081_1605_, lean_object* v_a_u2082_1606_, lean_object* v_a_u2083_1607_, lean_object* v_a_u2084_1608_){
_start:
{
lean_object* v_toBind_1609_; lean_object* v___f_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_toBind_1609_ = lean_ctor_get(v_inst_1603_, 1);
lean_inc(v_toBind_1609_);
lean_inc_ref(v_inst_1603_);
lean_inc_ref(v_inst_1602_);
v___f_1610_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1610_, 0, v_inst_1602_);
lean_closure_set(v___f_1610_, 1, v_inst_1603_);
lean_closure_set(v___f_1610_, 2, v_a_u2084_1608_);
v___x_1611_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1602_, v_inst_1603_, v_f_1604_, v_a_u2081_1605_, v_a_u2082_1606_, v_a_u2083_1607_);
v___x_1612_ = lean_apply_4(v_toBind_1609_, lean_box(0), lean_box(0), v___x_1611_, v___f_1610_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084(lean_object* v_m_1613_, lean_object* v_inst_1614_, lean_object* v_inst_1615_, lean_object* v_f_1616_, lean_object* v_a_u2081_1617_, lean_object* v_a_u2082_1618_, lean_object* v_a_u2083_1619_, lean_object* v_a_u2084_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1614_, v_inst_1615_, v_f_1616_, v_a_u2081_1617_, v_a_u2082_1618_, v_a_u2083_1619_, v_a_u2084_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0(lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_a_u2085_1624_, lean_object* v_____do__lift_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1622_, v_inst_1623_, v_____do__lift_1625_, v_a_u2085_1624_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_f_1629_, lean_object* v_a_u2081_1630_, lean_object* v_a_u2082_1631_, lean_object* v_a_u2083_1632_, lean_object* v_a_u2084_1633_, lean_object* v_a_u2085_1634_){
_start:
{
lean_object* v_toBind_1635_; lean_object* v___f_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_toBind_1635_ = lean_ctor_get(v_inst_1628_, 1);
lean_inc(v_toBind_1635_);
lean_inc_ref(v_inst_1628_);
lean_inc_ref(v_inst_1627_);
v___f_1636_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1636_, 0, v_inst_1627_);
lean_closure_set(v___f_1636_, 1, v_inst_1628_);
lean_closure_set(v___f_1636_, 2, v_a_u2085_1634_);
v___x_1637_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1627_, v_inst_1628_, v_f_1629_, v_a_u2081_1630_, v_a_u2082_1631_, v_a_u2083_1632_, v_a_u2084_1633_);
v___x_1638_ = lean_apply_4(v_toBind_1635_, lean_box(0), lean_box(0), v___x_1637_, v___f_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085(lean_object* v_m_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_f_1642_, lean_object* v_a_u2081_1643_, lean_object* v_a_u2082_1644_, lean_object* v_a_u2083_1645_, lean_object* v_a_u2084_1646_, lean_object* v_a_u2085_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1640_, v_inst_1641_, v_f_1642_, v_a_u2081_1643_, v_a_u2082_1644_, v_a_u2083_1645_, v_a_u2084_1646_, v_a_u2085_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0(lean_object* v_inst_1649_, lean_object* v_inst_1650_, lean_object* v_a_u2086_1651_, lean_object* v_____do__lift_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1649_, v_inst_1650_, v_____do__lift_1652_, v_a_u2086_1651_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v_f_1656_, lean_object* v_a_u2081_1657_, lean_object* v_a_u2082_1658_, lean_object* v_a_u2083_1659_, lean_object* v_a_u2084_1660_, lean_object* v_a_u2085_1661_, lean_object* v_a_u2086_1662_){
_start:
{
lean_object* v_toBind_1663_; lean_object* v___f_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_toBind_1663_ = lean_ctor_get(v_inst_1655_, 1);
lean_inc(v_toBind_1663_);
lean_inc_ref(v_inst_1655_);
lean_inc_ref(v_inst_1654_);
v___f_1664_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1664_, 0, v_inst_1654_);
lean_closure_set(v___f_1664_, 1, v_inst_1655_);
lean_closure_set(v___f_1664_, 2, v_a_u2086_1662_);
v___x_1665_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1654_, v_inst_1655_, v_f_1656_, v_a_u2081_1657_, v_a_u2082_1658_, v_a_u2083_1659_, v_a_u2084_1660_, v_a_u2085_1661_);
v___x_1666_ = lean_apply_4(v_toBind_1663_, lean_box(0), lean_box(0), v___x_1665_, v___f_1664_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086(lean_object* v_m_1667_, lean_object* v_inst_1668_, lean_object* v_inst_1669_, lean_object* v_f_1670_, lean_object* v_a_u2081_1671_, lean_object* v_a_u2082_1672_, lean_object* v_a_u2083_1673_, lean_object* v_a_u2084_1674_, lean_object* v_a_u2085_1675_, lean_object* v_a_u2086_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1668_, v_inst_1669_, v_f_1670_, v_a_u2081_1671_, v_a_u2082_1672_, v_a_u2083_1673_, v_a_u2084_1674_, v_a_u2085_1675_, v_a_u2086_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0(lean_object* v_inst_1678_, lean_object* v_inst_1679_, lean_object* v_a_u2087_1680_, lean_object* v_____do__lift_1681_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1678_, v_inst_1679_, v_____do__lift_1681_, v_a_u2087_1680_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(lean_object* v_inst_1683_, lean_object* v_inst_1684_, lean_object* v_f_1685_, lean_object* v_a_u2081_1686_, lean_object* v_a_u2082_1687_, lean_object* v_a_u2083_1688_, lean_object* v_a_u2084_1689_, lean_object* v_a_u2085_1690_, lean_object* v_a_u2086_1691_, lean_object* v_a_u2087_1692_){
_start:
{
lean_object* v_toBind_1693_; lean_object* v___f_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_toBind_1693_ = lean_ctor_get(v_inst_1684_, 1);
lean_inc(v_toBind_1693_);
lean_inc_ref(v_inst_1684_);
lean_inc_ref(v_inst_1683_);
v___f_1694_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1694_, 0, v_inst_1683_);
lean_closure_set(v___f_1694_, 1, v_inst_1684_);
lean_closure_set(v___f_1694_, 2, v_a_u2087_1692_);
v___x_1695_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1683_, v_inst_1684_, v_f_1685_, v_a_u2081_1686_, v_a_u2082_1687_, v_a_u2083_1688_, v_a_u2084_1689_, v_a_u2085_1690_, v_a_u2086_1691_);
v___x_1696_ = lean_apply_4(v_toBind_1693_, lean_box(0), lean_box(0), v___x_1695_, v___f_1694_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087(lean_object* v_m_1697_, lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_f_1700_, lean_object* v_a_u2081_1701_, lean_object* v_a_u2082_1702_, lean_object* v_a_u2083_1703_, lean_object* v_a_u2084_1704_, lean_object* v_a_u2085_1705_, lean_object* v_a_u2086_1706_, lean_object* v_a_u2087_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1698_, v_inst_1699_, v_f_1700_, v_a_u2081_1701_, v_a_u2082_1702_, v_a_u2083_1703_, v_a_u2084_1704_, v_a_u2085_1705_, v_a_u2086_1706_, v_a_u2087_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0(lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_a_u2088_1711_, lean_object* v_____do__lift_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1709_, v_inst_1710_, v_____do__lift_1712_, v_a_u2088_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(lean_object* v_inst_1714_, lean_object* v_inst_1715_, lean_object* v_f_1716_, lean_object* v_a_u2081_1717_, lean_object* v_a_u2082_1718_, lean_object* v_a_u2083_1719_, lean_object* v_a_u2084_1720_, lean_object* v_a_u2085_1721_, lean_object* v_a_u2086_1722_, lean_object* v_a_u2087_1723_, lean_object* v_a_u2088_1724_){
_start:
{
lean_object* v_toBind_1725_; lean_object* v___f_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v_toBind_1725_ = lean_ctor_get(v_inst_1715_, 1);
lean_inc(v_toBind_1725_);
lean_inc_ref(v_inst_1715_);
lean_inc_ref(v_inst_1714_);
v___f_1726_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1726_, 0, v_inst_1714_);
lean_closure_set(v___f_1726_, 1, v_inst_1715_);
lean_closure_set(v___f_1726_, 2, v_a_u2088_1724_);
v___x_1727_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1714_, v_inst_1715_, v_f_1716_, v_a_u2081_1717_, v_a_u2082_1718_, v_a_u2083_1719_, v_a_u2084_1720_, v_a_u2085_1721_, v_a_u2086_1722_, v_a_u2087_1723_);
v___x_1728_ = lean_apply_4(v_toBind_1725_, lean_box(0), lean_box(0), v___x_1727_, v___f_1726_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088(lean_object* v_m_1729_, lean_object* v_inst_1730_, lean_object* v_inst_1731_, lean_object* v_f_1732_, lean_object* v_a_u2081_1733_, lean_object* v_a_u2082_1734_, lean_object* v_a_u2083_1735_, lean_object* v_a_u2084_1736_, lean_object* v_a_u2085_1737_, lean_object* v_a_u2086_1738_, lean_object* v_a_u2087_1739_, lean_object* v_a_u2088_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1730_, v_inst_1731_, v_f_1732_, v_a_u2081_1733_, v_a_u2082_1734_, v_a_u2083_1735_, v_a_u2084_1736_, v_a_u2085_1737_, v_a_u2086_1738_, v_a_u2087_1739_, v_a_u2088_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0(lean_object* v_inst_1742_, lean_object* v_inst_1743_, lean_object* v_a_u2089_1744_, lean_object* v_____do__lift_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1742_, v_inst_1743_, v_____do__lift_1745_, v_a_u2089_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(lean_object* v_inst_1747_, lean_object* v_inst_1748_, lean_object* v_f_1749_, lean_object* v_a_u2081_1750_, lean_object* v_a_u2082_1751_, lean_object* v_a_u2083_1752_, lean_object* v_a_u2084_1753_, lean_object* v_a_u2085_1754_, lean_object* v_a_u2086_1755_, lean_object* v_a_u2087_1756_, lean_object* v_a_u2088_1757_, lean_object* v_a_u2089_1758_){
_start:
{
lean_object* v_toBind_1759_; lean_object* v___f_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_toBind_1759_ = lean_ctor_get(v_inst_1748_, 1);
lean_inc(v_toBind_1759_);
lean_inc_ref(v_inst_1748_);
lean_inc_ref(v_inst_1747_);
v___f_1760_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1760_, 0, v_inst_1747_);
lean_closure_set(v___f_1760_, 1, v_inst_1748_);
lean_closure_set(v___f_1760_, 2, v_a_u2089_1758_);
v___x_1761_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1747_, v_inst_1748_, v_f_1749_, v_a_u2081_1750_, v_a_u2082_1751_, v_a_u2083_1752_, v_a_u2084_1753_, v_a_u2085_1754_, v_a_u2086_1755_, v_a_u2087_1756_, v_a_u2088_1757_);
v___x_1762_ = lean_apply_4(v_toBind_1759_, lean_box(0), lean_box(0), v___x_1761_, v___f_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089(lean_object* v_m_1763_, lean_object* v_inst_1764_, lean_object* v_inst_1765_, lean_object* v_f_1766_, lean_object* v_a_u2081_1767_, lean_object* v_a_u2082_1768_, lean_object* v_a_u2083_1769_, lean_object* v_a_u2084_1770_, lean_object* v_a_u2085_1771_, lean_object* v_a_u2086_1772_, lean_object* v_a_u2087_1773_, lean_object* v_a_u2088_1774_, lean_object* v_a_u2089_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1764_, v_inst_1765_, v_f_1766_, v_a_u2081_1767_, v_a_u2082_1768_, v_a_u2083_1769_, v_a_u2084_1770_, v_a_u2085_1771_, v_a_u2086_1772_, v_a_u2087_1773_, v_a_u2088_1774_, v_a_u2089_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0(lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_a_u2081_u2080_1779_, lean_object* v_____do__lift_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1777_, v_inst_1778_, v_____do__lift_1780_, v_a_u2081_u2080_1779_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(lean_object* v_inst_1782_, lean_object* v_inst_1783_, lean_object* v_f_1784_, lean_object* v_a_u2081_1785_, lean_object* v_a_u2082_1786_, lean_object* v_a_u2083_1787_, lean_object* v_a_u2084_1788_, lean_object* v_a_u2085_1789_, lean_object* v_a_u2086_1790_, lean_object* v_a_u2087_1791_, lean_object* v_a_u2088_1792_, lean_object* v_a_u2089_1793_, lean_object* v_a_u2081_u2080_1794_){
_start:
{
lean_object* v_toBind_1795_; lean_object* v___f_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v_toBind_1795_ = lean_ctor_get(v_inst_1783_, 1);
lean_inc(v_toBind_1795_);
lean_inc_ref(v_inst_1783_);
lean_inc_ref(v_inst_1782_);
v___f_1796_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1796_, 0, v_inst_1782_);
lean_closure_set(v___f_1796_, 1, v_inst_1783_);
lean_closure_set(v___f_1796_, 2, v_a_u2081_u2080_1794_);
v___x_1797_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1782_, v_inst_1783_, v_f_1784_, v_a_u2081_1785_, v_a_u2082_1786_, v_a_u2083_1787_, v_a_u2084_1788_, v_a_u2085_1789_, v_a_u2086_1790_, v_a_u2087_1791_, v_a_u2088_1792_, v_a_u2089_1793_);
v___x_1798_ = lean_apply_4(v_toBind_1795_, lean_box(0), lean_box(0), v___x_1797_, v___f_1796_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080(lean_object* v_m_1799_, lean_object* v_inst_1800_, lean_object* v_inst_1801_, lean_object* v_f_1802_, lean_object* v_a_u2081_1803_, lean_object* v_a_u2082_1804_, lean_object* v_a_u2083_1805_, lean_object* v_a_u2084_1806_, lean_object* v_a_u2085_1807_, lean_object* v_a_u2086_1808_, lean_object* v_a_u2087_1809_, lean_object* v_a_u2088_1810_, lean_object* v_a_u2089_1811_, lean_object* v_a_u2081_u2080_1812_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1800_, v_inst_1801_, v_f_1802_, v_a_u2081_1803_, v_a_u2082_1804_, v_a_u2083_1805_, v_a_u2084_1806_, v_a_u2085_1807_, v_a_u2086_1808_, v_a_u2087_1809_, v_a_u2088_1810_, v_a_u2089_1811_, v_a_u2081_u2080_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0(lean_object* v_inst_1814_, lean_object* v_inst_1815_, lean_object* v_a_u2081_u2081_1816_, lean_object* v_____do__lift_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1814_, v_inst_1815_, v_____do__lift_1817_, v_a_u2081_u2081_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_f_1821_, lean_object* v_a_u2081_1822_, lean_object* v_a_u2082_1823_, lean_object* v_a_u2083_1824_, lean_object* v_a_u2084_1825_, lean_object* v_a_u2085_1826_, lean_object* v_a_u2086_1827_, lean_object* v_a_u2087_1828_, lean_object* v_a_u2088_1829_, lean_object* v_a_u2089_1830_, lean_object* v_a_u2081_u2080_1831_, lean_object* v_a_u2081_u2081_1832_){
_start:
{
lean_object* v_toBind_1833_; lean_object* v___f_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v_toBind_1833_ = lean_ctor_get(v_inst_1820_, 1);
lean_inc(v_toBind_1833_);
lean_inc_ref(v_inst_1820_);
lean_inc_ref(v_inst_1819_);
v___f_1834_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1834_, 0, v_inst_1819_);
lean_closure_set(v___f_1834_, 1, v_inst_1820_);
lean_closure_set(v___f_1834_, 2, v_a_u2081_u2081_1832_);
v___x_1835_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1819_, v_inst_1820_, v_f_1821_, v_a_u2081_1822_, v_a_u2082_1823_, v_a_u2083_1824_, v_a_u2084_1825_, v_a_u2085_1826_, v_a_u2086_1827_, v_a_u2087_1828_, v_a_u2088_1829_, v_a_u2089_1830_, v_a_u2081_u2080_1831_);
v___x_1836_ = lean_apply_4(v_toBind_1833_, lean_box(0), lean_box(0), v___x_1835_, v___f_1834_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081(lean_object* v_m_1837_, lean_object* v_inst_1838_, lean_object* v_inst_1839_, lean_object* v_f_1840_, lean_object* v_a_u2081_1841_, lean_object* v_a_u2082_1842_, lean_object* v_a_u2083_1843_, lean_object* v_a_u2084_1844_, lean_object* v_a_u2085_1845_, lean_object* v_a_u2086_1846_, lean_object* v_a_u2087_1847_, lean_object* v_a_u2088_1848_, lean_object* v_a_u2089_1849_, lean_object* v_a_u2081_u2080_1850_, lean_object* v_a_u2081_u2081_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(v_inst_1838_, v_inst_1839_, v_f_1840_, v_a_u2081_1841_, v_a_u2082_1842_, v_a_u2083_1843_, v_a_u2084_1844_, v_a_u2085_1845_, v_a_u2086_1846_, v_a_u2087_1847_, v_a_u2088_1848_, v_a_u2089_1849_, v_a_u2081_u2080_1850_, v_a_u2081_u2081_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed(lean_object* v_i_1853_, lean_object* v_inst_1854_, lean_object* v_inst_1855_, lean_object* v_args_1856_, lean_object* v_endIdx_1857_, lean_object* v_____do__lift_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(v_i_1853_, v_inst_1854_, v_inst_1855_, v_args_1856_, v_endIdx_1857_, v_____do__lift_1858_);
lean_dec(v_i_1853_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(lean_object* v_inst_1860_, lean_object* v_inst_1861_, lean_object* v_args_1862_, lean_object* v_endIdx_1863_, lean_object* v_b_1864_, lean_object* v_i_1865_){
_start:
{
lean_object* v_toApplicative_1866_; lean_object* v_toBind_1867_; lean_object* v_toPure_1868_; uint8_t v___x_1869_; 
v_toApplicative_1866_ = lean_ctor_get(v_inst_1861_, 0);
v_toBind_1867_ = lean_ctor_get(v_inst_1861_, 1);
lean_inc(v_toBind_1867_);
v_toPure_1868_ = lean_ctor_get(v_toApplicative_1866_, 1);
v___x_1869_ = lean_nat_dec_le(v_endIdx_1863_, v_i_1865_);
if (v___x_1869_ == 0)
{
lean_object* v___f_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
lean_inc_ref(v_args_1862_);
lean_inc_ref(v_inst_1861_);
lean_inc_ref(v_inst_1860_);
lean_inc(v_i_1865_);
v___f_1870_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1870_, 0, v_i_1865_);
lean_closure_set(v___f_1870_, 1, v_inst_1860_);
lean_closure_set(v___f_1870_, 2, v_inst_1861_);
lean_closure_set(v___f_1870_, 3, v_args_1862_);
lean_closure_set(v___f_1870_, 4, v_endIdx_1863_);
v___x_1871_ = l_Lean_instInhabitedExpr;
v___x_1872_ = lean_array_get(v___x_1871_, v_args_1862_, v_i_1865_);
lean_dec(v_i_1865_);
lean_dec_ref(v_args_1862_);
v___x_1873_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1860_, v_inst_1861_, v_b_1864_, v___x_1872_);
v___x_1874_ = lean_apply_4(v_toBind_1867_, lean_box(0), lean_box(0), v___x_1873_, v___f_1870_);
return v___x_1874_;
}
else
{
lean_object* v___x_1875_; 
lean_inc(v_toPure_1868_);
lean_dec(v_toBind_1867_);
lean_dec(v_i_1865_);
lean_dec(v_endIdx_1863_);
lean_dec_ref(v_args_1862_);
lean_dec_ref(v_inst_1861_);
lean_dec_ref(v_inst_1860_);
v___x_1875_ = lean_apply_2(v_toPure_1868_, lean_box(0), v_b_1864_);
return v___x_1875_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(lean_object* v_i_1876_, lean_object* v_inst_1877_, lean_object* v_inst_1878_, lean_object* v_args_1879_, lean_object* v_endIdx_1880_, lean_object* v_____do__lift_1881_){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = lean_unsigned_to_nat(1u);
v___x_1883_ = lean_nat_add(v_i_1876_, v___x_1882_);
v___x_1884_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1877_, v_inst_1878_, v_args_1879_, v_endIdx_1880_, v_____do__lift_1881_, v___x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go(lean_object* v_m_1885_, lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_args_1888_, lean_object* v_endIdx_1889_, lean_object* v_b_1890_, lean_object* v_i_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1886_, v_inst_1887_, v_args_1888_, v_endIdx_1889_, v_b_1890_, v_i_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS___redArg(lean_object* v_inst_1893_, lean_object* v_inst_1894_, lean_object* v_f_1895_, lean_object* v_beginIdx_1896_, lean_object* v_endIdx_1897_, lean_object* v_args_1898_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1893_, v_inst_1894_, v_args_1898_, v_endIdx_1897_, v_f_1895_, v_beginIdx_1896_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS(lean_object* v_m_1900_, lean_object* v_inst_1901_, lean_object* v_inst_1902_, lean_object* v_f_1903_, lean_object* v_beginIdx_1904_, lean_object* v_endIdx_1905_, lean_object* v_args_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1901_, v_inst_1902_, v_args_1906_, v_endIdx_1905_, v_f_1903_, v_beginIdx_1904_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___redArg(lean_object* v_inst_1908_, lean_object* v_inst_1909_, lean_object* v_f_1910_, lean_object* v_args_1911_){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = lean_unsigned_to_nat(0u);
v___x_1913_ = lean_array_get_size(v_args_1911_);
v___x_1914_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1908_, v_inst_1909_, v_args_1911_, v___x_1913_, v_f_1910_, v___x_1912_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS(lean_object* v_m_1915_, lean_object* v_inst_1916_, lean_object* v_inst_1917_, lean_object* v_f_1918_, lean_object* v_args_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_Meta_Sym_Internal_mkAppNS___redArg(v_inst_1916_, v_inst_1917_, v_f_1918_, v_args_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed(lean_object* v_inst_1921_, lean_object* v_inst_1922_, lean_object* v_revArgs_1923_, lean_object* v_start_1924_, lean_object* v_i_1925_, lean_object* v_____do__lift_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(v_inst_1921_, v_inst_1922_, v_revArgs_1923_, v_start_1924_, v_i_1925_, v_____do__lift_1926_);
lean_dec(v_i_1925_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(lean_object* v_inst_1928_, lean_object* v_inst_1929_, lean_object* v_revArgs_1930_, lean_object* v_start_1931_, lean_object* v_b_1932_, lean_object* v_i_1933_){
_start:
{
lean_object* v_toApplicative_1934_; lean_object* v_toBind_1935_; lean_object* v_toPure_1936_; uint8_t v___x_1937_; 
v_toApplicative_1934_ = lean_ctor_get(v_inst_1929_, 0);
v_toBind_1935_ = lean_ctor_get(v_inst_1929_, 1);
lean_inc(v_toBind_1935_);
v_toPure_1936_ = lean_ctor_get(v_toApplicative_1934_, 1);
v___x_1937_ = lean_nat_dec_le(v_i_1933_, v_start_1931_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v_i_1940_; lean_object* v___f_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1938_ = l_Lean_instInhabitedExpr;
v___x_1939_ = lean_unsigned_to_nat(1u);
v_i_1940_ = lean_nat_sub(v_i_1933_, v___x_1939_);
lean_inc(v_i_1940_);
lean_inc_ref(v_revArgs_1930_);
lean_inc_ref(v_inst_1929_);
lean_inc_ref(v_inst_1928_);
v___f_1941_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1941_, 0, v_inst_1928_);
lean_closure_set(v___f_1941_, 1, v_inst_1929_);
lean_closure_set(v___f_1941_, 2, v_revArgs_1930_);
lean_closure_set(v___f_1941_, 3, v_start_1931_);
lean_closure_set(v___f_1941_, 4, v_i_1940_);
v___x_1942_ = lean_array_get(v___x_1938_, v_revArgs_1930_, v_i_1940_);
lean_dec(v_i_1940_);
lean_dec_ref(v_revArgs_1930_);
v___x_1943_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1928_, v_inst_1929_, v_b_1932_, v___x_1942_);
v___x_1944_ = lean_apply_4(v_toBind_1935_, lean_box(0), lean_box(0), v___x_1943_, v___f_1941_);
return v___x_1944_;
}
else
{
lean_object* v___x_1945_; 
lean_inc(v_toPure_1936_);
lean_dec(v_toBind_1935_);
lean_dec(v_start_1931_);
lean_dec_ref(v_revArgs_1930_);
lean_dec_ref(v_inst_1929_);
lean_dec_ref(v_inst_1928_);
v___x_1945_ = lean_apply_2(v_toPure_1936_, lean_box(0), v_b_1932_);
return v___x_1945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(lean_object* v_inst_1946_, lean_object* v_inst_1947_, lean_object* v_revArgs_1948_, lean_object* v_start_1949_, lean_object* v_i_1950_, lean_object* v_____do__lift_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1946_, v_inst_1947_, v_revArgs_1948_, v_start_1949_, v_____do__lift_1951_, v_i_1950_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___boxed(lean_object* v_inst_1953_, lean_object* v_inst_1954_, lean_object* v_revArgs_1955_, lean_object* v_start_1956_, lean_object* v_b_1957_, lean_object* v_i_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1953_, v_inst_1954_, v_revArgs_1955_, v_start_1956_, v_b_1957_, v_i_1958_);
lean_dec(v_i_1958_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(lean_object* v_m_1960_, lean_object* v_inst_1961_, lean_object* v_inst_1962_, lean_object* v_revArgs_1963_, lean_object* v_start_1964_, lean_object* v_b_1965_, lean_object* v_i_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1961_, v_inst_1962_, v_revArgs_1963_, v_start_1964_, v_b_1965_, v_i_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___boxed(lean_object* v_m_1968_, lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_revArgs_1971_, lean_object* v_start_1972_, lean_object* v_b_1973_, lean_object* v_i_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(v_m_1968_, v_inst_1969_, v_inst_1970_, v_revArgs_1971_, v_start_1972_, v_b_1973_, v_i_1974_);
lean_dec(v_i_1974_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(lean_object* v_inst_1976_, lean_object* v_inst_1977_, lean_object* v_f_1978_, lean_object* v_beginIdx_1979_, lean_object* v_endIdx_1980_, lean_object* v_revArgs_1981_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1976_, v_inst_1977_, v_revArgs_1981_, v_beginIdx_1979_, v_f_1978_, v_endIdx_1980_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg___boxed(lean_object* v_inst_1983_, lean_object* v_inst_1984_, lean_object* v_f_1985_, lean_object* v_beginIdx_1986_, lean_object* v_endIdx_1987_, lean_object* v_revArgs_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(v_inst_1983_, v_inst_1984_, v_f_1985_, v_beginIdx_1986_, v_endIdx_1987_, v_revArgs_1988_);
lean_dec(v_endIdx_1987_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS(lean_object* v_m_1990_, lean_object* v_inst_1991_, lean_object* v_inst_1992_, lean_object* v_f_1993_, lean_object* v_beginIdx_1994_, lean_object* v_endIdx_1995_, lean_object* v_revArgs_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1991_, v_inst_1992_, v_revArgs_1996_, v_beginIdx_1994_, v_f_1993_, v_endIdx_1995_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___boxed(lean_object* v_m_1998_, lean_object* v_inst_1999_, lean_object* v_inst_2000_, lean_object* v_f_2001_, lean_object* v_beginIdx_2002_, lean_object* v_endIdx_2003_, lean_object* v_revArgs_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS(v_m_1998_, v_inst_1999_, v_inst_2000_, v_f_2001_, v_beginIdx_2002_, v_endIdx_2003_, v_revArgs_2004_);
lean_dec(v_endIdx_2003_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(lean_object* v_inst_2006_, lean_object* v_inst_2007_, lean_object* v_f_2008_, lean_object* v_revArgs_2009_){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = lean_unsigned_to_nat(0u);
v___x_2011_ = lean_array_get_size(v_revArgs_2009_);
v___x_2012_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_2006_, v_inst_2007_, v_revArgs_2009_, v___x_2010_, v_f_2008_, v___x_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS(lean_object* v_m_2013_, lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_f_2016_, lean_object* v_revArgs_2017_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(v_inst_2014_, v_inst_2015_, v_f_2016_, v_revArgs_2017_);
return v___x_2018_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy = _init_l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy();
lean_mark_persistent(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy);
l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM = _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM();
lean_mark_persistent(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
}
#ifdef __cplusplus
}
#endif
