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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(lean_object* v_x_86_, size_t v_x_87_, size_t v_x_88_, lean_object* v_x_89_, lean_object* v_x_90_){
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(size_t v_depth_157_, lean_object* v_keys_158_, lean_object* v_vals_159_, lean_object* v_i_160_, lean_object* v_entries_161_){
_start:
{
lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = lean_array_get_size(v_keys_158_);
v___x_163_ = lean_nat_dec_lt(v_i_160_, v___x_162_);
if (v___x_163_ == 0)
{
lean_dec(v_i_160_);
return v_entries_161_;
}
else
{
lean_object* v_k_164_; lean_object* v_v_165_; uint64_t v___x_166_; size_t v_h_167_; size_t v___x_168_; lean_object* v___x_169_; size_t v___x_170_; size_t v___x_171_; size_t v___x_172_; size_t v_h_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_k_164_ = lean_array_fget_borrowed(v_keys_158_, v_i_160_);
v_v_165_ = lean_array_fget_borrowed(v_vals_159_, v_i_160_);
v___x_166_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_164_);
v_h_167_ = lean_uint64_to_usize(v___x_166_);
v___x_168_ = ((size_t)5ULL);
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = ((size_t)1ULL);
v___x_171_ = lean_usize_sub(v_depth_157_, v___x_170_);
v___x_172_ = lean_usize_mul(v___x_168_, v___x_171_);
v_h_173_ = lean_usize_shift_right(v_h_167_, v___x_172_);
v___x_174_ = lean_nat_add(v_i_160_, v___x_169_);
lean_dec(v_i_160_);
lean_inc(v_v_165_);
lean_inc(v_k_164_);
v___x_175_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_entries_161_, v_h_173_, v_depth_157_, v_k_164_, v_v_165_);
v_i_160_ = v___x_174_;
v_entries_161_ = v___x_175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_177_, lean_object* v_keys_178_, lean_object* v_vals_179_, lean_object* v_i_180_, lean_object* v_entries_181_){
_start:
{
size_t v_depth_boxed_182_; lean_object* v_res_183_; 
v_depth_boxed_182_ = lean_unbox_usize(v_depth_177_);
lean_dec(v_depth_177_);
v_res_183_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_182_, v_keys_178_, v_vals_179_, v_i_180_, v_entries_181_);
lean_dec_ref(v_vals_179_);
lean_dec_ref(v_keys_178_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___boxed(lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
size_t v_x_2079__boxed_189_; size_t v_x_2080__boxed_190_; lean_object* v_res_191_; 
v_x_2079__boxed_189_ = lean_unbox_usize(v_x_185_);
lean_dec(v_x_185_);
v_x_2080__boxed_190_ = lean_unbox_usize(v_x_186_);
lean_dec(v_x_186_);
v_res_191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_184_, v_x_2079__boxed_189_, v_x_2080__boxed_190_, v_x_187_, v_x_188_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(lean_object* v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_){
_start:
{
uint64_t v___x_195_; size_t v___x_196_; size_t v___x_197_; lean_object* v___x_198_; 
v___x_195_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_193_);
v___x_196_ = lean_uint64_to_usize(v___x_195_);
v___x_197_ = ((size_t)1ULL);
v___x_198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_192_, v___x_196_, v___x_197_, v_x_193_, v_x_194_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(lean_object* v_keys_199_, lean_object* v_i_200_, lean_object* v_k_201_, lean_object* v_k_u2080_202_){
_start:
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = lean_array_get_size(v_keys_199_);
v___x_204_ = lean_nat_dec_lt(v_i_200_, v___x_203_);
if (v___x_204_ == 0)
{
lean_dec(v_i_200_);
lean_inc_ref(v_k_u2080_202_);
return v_k_u2080_202_;
}
else
{
lean_object* v_k_x27_205_; uint8_t v___x_206_; 
v_k_x27_205_ = lean_array_fget_borrowed(v_keys_199_, v_i_200_);
v___x_206_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_201_, v_k_x27_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_add(v_i_200_, v___x_207_);
lean_dec(v_i_200_);
v_i_200_ = v___x_208_;
goto _start;
}
else
{
lean_dec(v_i_200_);
lean_inc(v_k_x27_205_);
return v_k_x27_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg___boxed(lean_object* v_keys_210_, lean_object* v_i_211_, lean_object* v_k_212_, lean_object* v_k_u2080_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_210_, v_i_211_, v_k_212_, v_k_u2080_213_);
lean_dec_ref(v_k_u2080_213_);
lean_dec_ref(v_k_212_);
lean_dec_ref(v_keys_210_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(lean_object* v_x_215_, size_t v_x_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
lean_object* v_es_219_; lean_object* v___x_220_; size_t v___x_221_; size_t v___x_222_; lean_object* v_j_223_; lean_object* v___x_224_; 
v_es_219_ = lean_ctor_get(v_x_215_, 0);
v___x_220_ = lean_box(2);
v___x_221_ = ((size_t)31ULL);
v___x_222_ = lean_usize_land(v_x_216_, v___x_221_);
v_j_223_ = lean_usize_to_nat(v___x_222_);
v___x_224_ = lean_array_get_borrowed(v___x_220_, v_es_219_, v_j_223_);
lean_dec(v_j_223_);
switch(lean_obj_tag(v___x_224_))
{
case 0:
{
lean_object* v_key_225_; uint8_t v___x_226_; 
v_key_225_ = lean_ctor_get(v___x_224_, 0);
v___x_226_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_217_, v_key_225_);
if (v___x_226_ == 0)
{
lean_inc_ref(v_x_218_);
return v_x_218_;
}
else
{
lean_inc(v_key_225_);
return v_key_225_;
}
}
case 1:
{
lean_object* v_node_227_; size_t v___x_228_; size_t v___x_229_; 
v_node_227_ = lean_ctor_get(v___x_224_, 0);
v___x_228_ = ((size_t)5ULL);
v___x_229_ = lean_usize_shift_right(v_x_216_, v___x_228_);
v_x_215_ = v_node_227_;
v_x_216_ = v___x_229_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_218_);
return v_x_218_;
}
}
}
else
{
lean_object* v_ks_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_ks_231_ = lean_ctor_get(v_x_215_, 0);
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_ks_231_, v___x_232_, v_x_217_, v_x_218_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg___boxed(lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
size_t v_x_2257__boxed_238_; lean_object* v_res_239_; 
v_x_2257__boxed_238_ = lean_unbox_usize(v_x_235_);
lean_dec(v_x_235_);
v_res_239_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_234_, v_x_2257__boxed_238_, v_x_236_, v_x_237_);
lean_dec_ref(v_x_237_);
lean_dec_ref(v_x_236_);
lean_dec_ref(v_x_234_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object* v_e_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_243_; lean_object* v_share_244_; lean_object* v___x_245_; uint64_t v___x_246_; size_t v___x_247_; lean_object* v___x_248_; size_t v___x_249_; size_t v___x_250_; uint8_t v___x_251_; 
v___x_243_ = lean_st_ref_get(v_a_241_);
v_share_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc_ref(v_share_244_);
lean_dec(v___x_243_);
v___x_245_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_246_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_240_);
v___x_247_ = lean_uint64_to_usize(v___x_246_);
v___x_248_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_244_, v___x_247_, v_e_240_, v___x_245_);
lean_dec_ref(v_share_244_);
v___x_249_ = lean_ptr_addr(v___x_248_);
v___x_250_ = lean_ptr_addr(v___x_245_);
v___x_251_ = lean_usize_dec_eq(v___x_249_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_dec_ref(v_e_240_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_248_);
return v___x_252_;
}
else
{
lean_object* v___x_253_; lean_object* v_share_254_; lean_object* v_maxFVar_255_; lean_object* v_proofInstInfo_256_; lean_object* v_proofInstInfoFVar_257_; lean_object* v_inferType_258_; lean_object* v_getLevel_259_; lean_object* v_congrInfo_260_; lean_object* v_defEqI_261_; lean_object* v_extensions_262_; lean_object* v_issues_263_; lean_object* v_canon_264_; lean_object* v_instanceOverrides_265_; uint8_t v_debug_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_277_; 
lean_dec_ref(v___x_248_);
v___x_253_ = lean_st_ref_take(v_a_241_);
v_share_254_ = lean_ctor_get(v___x_253_, 0);
v_maxFVar_255_ = lean_ctor_get(v___x_253_, 1);
v_proofInstInfo_256_ = lean_ctor_get(v___x_253_, 2);
v_proofInstInfoFVar_257_ = lean_ctor_get(v___x_253_, 3);
v_inferType_258_ = lean_ctor_get(v___x_253_, 4);
v_getLevel_259_ = lean_ctor_get(v___x_253_, 5);
v_congrInfo_260_ = lean_ctor_get(v___x_253_, 6);
v_defEqI_261_ = lean_ctor_get(v___x_253_, 7);
v_extensions_262_ = lean_ctor_get(v___x_253_, 8);
v_issues_263_ = lean_ctor_get(v___x_253_, 9);
v_canon_264_ = lean_ctor_get(v___x_253_, 10);
v_instanceOverrides_265_ = lean_ctor_get(v___x_253_, 11);
v_debug_266_ = lean_ctor_get_uint8(v___x_253_, sizeof(void*)*12);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_277_ == 0)
{
v___x_268_ = v___x_253_;
v_isShared_269_ = v_isSharedCheck_277_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_instanceOverrides_265_);
lean_inc(v_canon_264_);
lean_inc(v_issues_263_);
lean_inc(v_extensions_262_);
lean_inc(v_defEqI_261_);
lean_inc(v_congrInfo_260_);
lean_inc(v_getLevel_259_);
lean_inc(v_inferType_258_);
lean_inc(v_proofInstInfoFVar_257_);
lean_inc(v_proofInstInfo_256_);
lean_inc(v_maxFVar_255_);
lean_inc(v_share_254_);
lean_dec(v___x_253_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_277_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_270_ = lean_box(0);
lean_inc_ref(v_e_240_);
v___x_271_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_share_254_, v_e_240_, v___x_270_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_271_);
v___x_273_ = v___x_268_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_maxFVar_255_);
lean_ctor_set(v_reuseFailAlloc_276_, 2, v_proofInstInfo_256_);
lean_ctor_set(v_reuseFailAlloc_276_, 3, v_proofInstInfoFVar_257_);
lean_ctor_set(v_reuseFailAlloc_276_, 4, v_inferType_258_);
lean_ctor_set(v_reuseFailAlloc_276_, 5, v_getLevel_259_);
lean_ctor_set(v_reuseFailAlloc_276_, 6, v_congrInfo_260_);
lean_ctor_set(v_reuseFailAlloc_276_, 7, v_defEqI_261_);
lean_ctor_set(v_reuseFailAlloc_276_, 8, v_extensions_262_);
lean_ctor_set(v_reuseFailAlloc_276_, 9, v_issues_263_);
lean_ctor_set(v_reuseFailAlloc_276_, 10, v_canon_264_);
lean_ctor_set(v_reuseFailAlloc_276_, 11, v_instanceOverrides_265_);
lean_ctor_set_uint8(v_reuseFailAlloc_276_, sizeof(void*)*12, v_debug_266_);
v___x_273_ = v_reuseFailAlloc_276_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_st_ref_put(v_a_241_, v___x_273_);
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v_e_240_);
return v___x_275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg___boxed(lean_object* v_e_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_278_, v_a_279_);
lean_dec(v_a_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1(lean_object* v_e_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_282_, v_a_284_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___boxed(lean_object* v_e_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Meta_Sym_Internal_Sym_share1(v_e_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(lean_object* v_00_u03b2_300_, lean_object* v_x_301_, size_t v_x_302_, lean_object* v_x_303_, lean_object* v_x_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_301_, v_x_302_, v_x_303_, v_x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___boxed(lean_object* v_00_u03b2_306_, lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
size_t v_x_2349__boxed_311_; lean_object* v_res_312_; 
v_x_2349__boxed_311_ = lean_unbox_usize(v_x_308_);
lean_dec(v_x_308_);
v_res_312_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(v_00_u03b2_306_, v_x_307_, v_x_2349__boxed_311_, v_x_309_, v_x_310_);
lean_dec_ref(v_x_310_);
lean_dec_ref(v_x_309_);
lean_dec_ref(v_x_307_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1(lean_object* v_00_u03b2_313_, lean_object* v_x_314_, lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_x_314_, v_x_315_, v_x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(lean_object* v_00_u03b2_318_, lean_object* v_keys_319_, lean_object* v_vals_320_, lean_object* v_heq_321_, lean_object* v_i_322_, lean_object* v_k_323_, lean_object* v_k_u2080_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_319_, v_i_322_, v_k_323_, v_k_u2080_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___boxed(lean_object* v_00_u03b2_326_, lean_object* v_keys_327_, lean_object* v_vals_328_, lean_object* v_heq_329_, lean_object* v_i_330_, lean_object* v_k_331_, lean_object* v_k_u2080_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(v_00_u03b2_326_, v_keys_327_, v_vals_328_, v_heq_329_, v_i_330_, v_k_331_, v_k_u2080_332_);
lean_dec_ref(v_k_u2080_332_);
lean_dec_ref(v_k_331_);
lean_dec_ref(v_vals_328_);
lean_dec_ref(v_keys_327_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(lean_object* v_00_u03b2_334_, lean_object* v_x_335_, size_t v_x_336_, size_t v_x_337_, lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_335_, v_x_336_, v_x_337_, v_x_338_, v_x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_341_, lean_object* v_x_342_, lean_object* v_x_343_, lean_object* v_x_344_, lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
size_t v_x_2373__boxed_347_; size_t v_x_2374__boxed_348_; lean_object* v_res_349_; 
v_x_2373__boxed_347_ = lean_unbox_usize(v_x_343_);
lean_dec(v_x_343_);
v_x_2374__boxed_348_ = lean_unbox_usize(v_x_344_);
lean_dec(v_x_344_);
v_res_349_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(v_00_u03b2_341_, v_x_342_, v_x_2373__boxed_347_, v_x_2374__boxed_348_, v_x_345_, v_x_346_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_350_, lean_object* v_n_351_, lean_object* v_k_352_, lean_object* v_v_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(v_n_351_, v_k_352_, v_v_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_355_, size_t v_depth_356_, lean_object* v_keys_357_, lean_object* v_vals_358_, lean_object* v_heq_359_, lean_object* v_i_360_, lean_object* v_entries_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_356_, v_keys_357_, v_vals_358_, v_i_360_, v_entries_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_363_, lean_object* v_depth_364_, lean_object* v_keys_365_, lean_object* v_vals_366_, lean_object* v_heq_367_, lean_object* v_i_368_, lean_object* v_entries_369_){
_start:
{
size_t v_depth_boxed_370_; lean_object* v_res_371_; 
v_depth_boxed_370_ = lean_unbox_usize(v_depth_364_);
lean_dec(v_depth_364_);
v_res_371_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(v_00_u03b2_363_, v_depth_boxed_370_, v_keys_365_, v_vals_366_, v_heq_367_, v_i_368_, v_entries_369_);
lean_dec_ref(v_vals_366_);
lean_dec_ref(v_keys_365_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_373_, v_x_374_, v_x_375_, v_x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0(void){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(lean_object* v_msg_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_698__overap_388_; lean_object* v___x_389_; 
v___x_387_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_698__overap_388_ = lean_panic_fn_borrowed(v___x_387_, v_msg_379_);
lean_inc(v___y_385_);
lean_inc_ref(v___y_384_);
lean_inc(v___y_383_);
lean_inc_ref(v___y_382_);
lean_inc(v___y_381_);
lean_inc_ref(v___y_380_);
v___x_389_ = lean_apply_7(v___x_698__overap_388_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, lean_box(0));
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___boxed(lean_object* v_msg_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v_msg_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
return v_res_398_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_402_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2));
v___x_403_ = lean_unsigned_to_nat(2u);
v___x_404_ = lean_unsigned_to_nat(42u);
v___x_405_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1));
v___x_406_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_407_ = l_mkPanicMessageWithDecl(v___x_406_, v___x_405_, v___x_404_, v___x_403_, v___x_402_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object* v_e_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; lean_object* v_share_417_; lean_object* v___x_418_; uint64_t v___x_419_; size_t v___x_420_; lean_object* v___x_421_; size_t v___x_422_; size_t v___x_423_; uint8_t v___x_424_; 
v___x_416_ = lean_st_ref_get(v_a_410_);
v_share_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc_ref(v_share_417_);
lean_dec(v___x_416_);
v___x_418_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_419_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_408_);
v___x_420_ = lean_uint64_to_usize(v___x_419_);
v___x_421_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_417_, v___x_420_, v_e_408_, v___x_418_);
lean_dec_ref(v_share_417_);
v___x_422_ = lean_ptr_addr(v___x_421_);
lean_dec_ref(v___x_421_);
v___x_423_ = lean_ptr_addr(v_e_408_);
v___x_424_ = lean_usize_dec_eq(v___x_422_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3, &l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3_once, _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3);
v___x_426_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v___x_425_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_box(0);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed(lean_object* v_e_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec_ref(v_e_429_);
return v_res_437_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_448_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1));
v___x_449_ = lean_unsigned_to_nat(16u);
v___x_450_ = lean_unsigned_to_nat(62u);
v___x_451_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0));
v___x_452_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_453_ = l_mkPanicMessageWithDecl(v___x_452_, v___x_451_, v___x_450_, v___x_449_, v___x_448_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object* v_k_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v_debug_464_; lean_object* v___x_465_; lean_object* v_env_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_462_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_463_ = lean_st_ref_get(v_a_456_);
v_debug_464_ = lean_ctor_get_uint8(v___x_463_, sizeof(void*)*12);
lean_dec(v___x_463_);
v___x_465_ = lean_st_ref_get(v_a_460_);
v_env_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc_ref(v_env_466_);
lean_dec(v___x_465_);
v___x_467_ = lean_box(v_debug_464_);
v___x_468_ = lean_apply_1(v_k_454_, v___x_467_);
v___x_469_ = 0;
v___x_470_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_470_, 0, v_env_466_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*1, v___x_469_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*1 + 1, v___x_469_);
v___x_471_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_468_, v___x_470_, v_a_456_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_483_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_483_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_483_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_483_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
if (lean_obj_tag(v_a_472_) == 0)
{
lean_object* v___x_476_; lean_object* v___x_1322__overap_477_; lean_object* v___x_478_; 
lean_dec_ref_known(v_a_472_, 1);
lean_del_object(v___x_474_);
v___x_476_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
v___x_1322__overap_477_ = l_panic___redArg(v___x_462_, v___x_476_);
lean_inc(v_a_460_);
lean_inc_ref(v_a_459_);
lean_inc(v_a_458_);
lean_inc_ref(v_a_457_);
lean_inc(v_a_456_);
lean_inc_ref(v_a_455_);
v___x_478_ = lean_apply_7(v___x_1322__overap_477_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, lean_box(0));
return v___x_478_;
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; 
v_a_479_ = lean_ctor_get(v_a_472_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v_a_472_, 1);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v_a_479_);
v___x_481_ = v___x_474_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
v_a_484_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_471_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_471_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(lean_object* v_k_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(v_k_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM(lean_object* v_00_u03b1_501_, lean_object* v_k_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v_debug_512_; lean_object* v___x_513_; lean_object* v_env_514_; lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_510_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_511_ = lean_st_ref_get(v_a_504_);
v_debug_512_ = lean_ctor_get_uint8(v___x_511_, sizeof(void*)*12);
lean_dec(v___x_511_);
v___x_513_ = lean_st_ref_get(v_a_508_);
v_env_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc_ref(v_env_514_);
lean_dec(v___x_513_);
v___x_515_ = lean_box(v_debug_512_);
v___x_516_ = lean_apply_1(v_k_502_, v___x_515_);
v___x_517_ = 0;
v___x_518_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_518_, 0, v_env_514_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*1, v___x_517_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*1 + 1, v___x_517_);
v___x_519_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_516_, v___x_518_, v_a_504_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_531_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_531_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_531_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_531_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
if (lean_obj_tag(v_a_520_) == 0)
{
lean_object* v___x_524_; lean_object* v___x_1345__overap_525_; lean_object* v___x_526_; 
lean_dec_ref_known(v_a_520_, 1);
lean_del_object(v___x_522_);
v___x_524_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
v___x_1345__overap_525_ = l_panic___redArg(v___x_510_, v___x_524_);
lean_inc(v_a_508_);
lean_inc_ref(v_a_507_);
lean_inc(v_a_506_);
lean_inc_ref(v_a_505_);
lean_inc(v_a_504_);
lean_inc_ref(v_a_503_);
v___x_526_ = lean_apply_7(v___x_1345__overap_525_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, lean_box(0));
return v___x_526_;
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; 
v_a_527_ = lean_ctor_get(v_a_520_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v_a_520_, 1);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v_a_527_);
v___x_529_ = v___x_522_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_527_);
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
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
v_a_532_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_519_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_519_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object* v_00_u03b1_540_, lean_object* v_k_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Meta_Sym_Internal_liftBuilderM(v_00_u03b1_540_, v_k_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object* v_e_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_552_; uint64_t v___x_553_; size_t v___x_554_; lean_object* v___x_555_; size_t v___x_556_; size_t v___x_557_; uint8_t v___x_558_; 
v___x_552_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_553_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_550_);
v___x_554_ = lean_uint64_to_usize(v___x_553_);
v___x_555_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_a_551_, v___x_554_, v_e_550_, v___x_552_);
v___x_556_ = lean_ptr_addr(v___x_555_);
v___x_557_ = lean_ptr_addr(v___x_552_);
v___x_558_ = lean_usize_dec_eq(v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
lean_dec_ref(v_e_550_);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_555_);
lean_ctor_set(v___x_559_, 1, v_a_551_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec_ref(v___x_555_);
v___x_560_ = lean_box(0);
lean_inc_ref(v_e_550_);
v___x_561_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_a_551_, v_e_550_, v___x_560_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v_e_550_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object* v_e_563_, uint8_t v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v_e_563_, v_a_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object* v_e_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
uint8_t v_a_boxed_572_; lean_object* v_res_573_; 
v_a_boxed_572_ = lean_unbox(v_a_569_);
v_res_573_ = l_Lean_Meta_Sym_Internal_Builder_share1(v_e_568_, v_a_boxed_572_, v_a_570_, v_a_571_);
lean_dec_ref(v_a_570_);
return v_res_573_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0(void){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_HashMap_instInhabited___redArg();
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object* v_msg_575_, uint8_t v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___f_580_; lean_object* v___f_581_; lean_object* v___f_582_; lean_object* v___x_534__overap_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_579_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0);
v___f_580_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_580_, 0, v___x_579_);
v___f_581_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_581_, 0, v___f_580_);
v___f_582_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_582_, 0, v___f_581_);
v___x_534__overap_583_ = lean_panic_fn_borrowed(v___f_582_, v_msg_575_);
lean_dec_ref(v___f_582_);
v___x_584_ = lean_box(v___y_576_);
lean_inc_ref(v___y_577_);
v___x_585_ = lean_apply_3(v___x_534__overap_583_, v___x_584_, v___y_577_, v___y_578_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object* v_msg_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
uint8_t v___y_635__boxed_590_; lean_object* v_res_591_; 
v___y_635__boxed_590_ = lean_unbox(v___y_587_);
v_res_591_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v_msg_586_, v___y_635__boxed_590_, v___y_588_, v___y_589_);
lean_dec_ref(v___y_588_);
return v_res_591_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_592_, lean_object* v_i_593_, lean_object* v_k_594_){
_start:
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_array_get_size(v_keys_592_);
v___x_596_ = lean_nat_dec_lt(v_i_593_, v___x_595_);
if (v___x_596_ == 0)
{
lean_dec(v_i_593_);
return v___x_596_;
}
else
{
lean_object* v_k_x27_597_; uint8_t v___x_598_; 
v_k_x27_597_ = lean_array_fget_borrowed(v_keys_592_, v_i_593_);
v___x_598_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_594_, v_k_x27_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = lean_nat_add(v_i_593_, v___x_599_);
lean_dec(v_i_593_);
v_i_593_ = v___x_600_;
goto _start;
}
else
{
lean_dec(v_i_593_);
return v___x_596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_602_, lean_object* v_i_603_, lean_object* v_k_604_){
_start:
{
uint8_t v_res_605_; lean_object* v_r_606_; 
v_res_605_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_602_, v_i_603_, v_k_604_);
lean_dec_ref(v_k_604_);
lean_dec_ref(v_keys_602_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(lean_object* v_x_607_, size_t v_x_608_, lean_object* v_x_609_){
_start:
{
if (lean_obj_tag(v_x_607_) == 0)
{
lean_object* v_es_610_; lean_object* v___x_611_; size_t v___x_612_; size_t v___x_613_; lean_object* v_j_614_; lean_object* v___x_615_; 
v_es_610_ = lean_ctor_get(v_x_607_, 0);
v___x_611_ = lean_box(2);
v___x_612_ = ((size_t)31ULL);
v___x_613_ = lean_usize_land(v_x_608_, v___x_612_);
v_j_614_ = lean_usize_to_nat(v___x_613_);
v___x_615_ = lean_array_get_borrowed(v___x_611_, v_es_610_, v_j_614_);
lean_dec(v_j_614_);
switch(lean_obj_tag(v___x_615_))
{
case 0:
{
lean_object* v_key_616_; uint8_t v___x_617_; 
v_key_616_ = lean_ctor_get(v___x_615_, 0);
v___x_617_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_609_, v_key_616_);
return v___x_617_;
}
case 1:
{
lean_object* v_node_618_; size_t v___x_619_; size_t v___x_620_; 
v_node_618_ = lean_ctor_get(v___x_615_, 0);
v___x_619_ = ((size_t)5ULL);
v___x_620_ = lean_usize_shift_right(v_x_608_, v___x_619_);
v_x_607_ = v_node_618_;
v_x_608_ = v___x_620_;
goto _start;
}
default: 
{
uint8_t v___x_622_; 
v___x_622_ = 0;
return v___x_622_;
}
}
}
else
{
lean_object* v_ks_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v_ks_623_ = lean_ctor_get(v_x_607_, 0);
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_ks_623_, v___x_624_, v_x_609_);
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_){
_start:
{
size_t v_x_670__boxed_629_; uint8_t v_res_630_; lean_object* v_r_631_; 
v_x_670__boxed_629_ = lean_unbox_usize(v_x_627_);
lean_dec(v_x_627_);
v_res_630_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_626_, v_x_670__boxed_629_, v_x_628_);
lean_dec_ref(v_x_628_);
lean_dec_ref(v_x_626_);
v_r_631_ = lean_box(v_res_630_);
return v_r_631_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
uint64_t v___x_634_; size_t v___x_635_; uint8_t v___x_636_; 
v___x_634_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_633_);
v___x_635_ = lean_uint64_to_usize(v___x_634_);
v___x_636_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_632_, v___x_635_, v_x_633_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
uint8_t v_res_639_; lean_object* v_r_640_; 
v_res_639_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_637_, v_x_638_);
lean_dec_ref(v_x_638_);
lean_dec_ref(v_x_637_);
v_r_640_ = lean_box(v_res_639_);
return v_r_640_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_643_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1));
v___x_644_ = lean_unsigned_to_nat(2u);
v___x_645_ = lean_unsigned_to_nat(74u);
v___x_646_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0));
v___x_647_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_648_ = l_mkPanicMessageWithDecl(v___x_647_, v___x_646_, v___x_645_, v___x_644_, v___x_643_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object* v_e_649_, uint8_t v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
uint8_t v___x_653_; 
v___x_653_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_a_652_, v_e_649_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2, &l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once, _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2);
v___x_655_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v___x_654_, v_a_650_, v_a_651_, v_a_652_);
return v___x_655_;
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_box(0);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v_a_652_);
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object* v_e_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
uint8_t v_a_boxed_662_; lean_object* v_res_663_; 
v_a_boxed_662_ = lean_unbox(v_a_659_);
v_res_663_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_658_, v_a_boxed_662_, v_a_660_, v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec_ref(v_e_658_);
return v_res_663_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object* v_00_u03b2_664_, lean_object* v_x_665_, lean_object* v_x_666_){
_start:
{
uint8_t v___x_667_; 
v___x_667_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_665_, v_x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object* v_00_u03b2_668_, lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
uint8_t v_res_671_; lean_object* v_r_672_; 
v_res_671_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(v_00_u03b2_668_, v_x_669_, v_x_670_);
lean_dec_ref(v_x_670_);
lean_dec_ref(v_x_669_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object* v_00_u03b2_673_, lean_object* v_x_674_, size_t v_x_675_, lean_object* v_x_676_){
_start:
{
uint8_t v___x_677_; 
v___x_677_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_674_, v_x_675_, v_x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_678_, lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_){
_start:
{
size_t v_x_769__boxed_682_; uint8_t v_res_683_; lean_object* v_r_684_; 
v_x_769__boxed_682_ = lean_unbox_usize(v_x_680_);
lean_dec(v_x_680_);
v_res_683_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(v_00_u03b2_678_, v_x_679_, v_x_769__boxed_682_, v_x_681_);
lean_dec_ref(v_x_681_);
lean_dec_ref(v_x_679_);
v_r_684_ = lean_box(v_res_683_);
return v_r_684_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_685_, lean_object* v_keys_686_, lean_object* v_vals_687_, lean_object* v_heq_688_, lean_object* v_i_689_, lean_object* v_k_690_){
_start:
{
uint8_t v___x_691_; 
v___x_691_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_686_, v_i_689_, v_k_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_692_, lean_object* v_keys_693_, lean_object* v_vals_694_, lean_object* v_heq_695_, lean_object* v_i_696_, lean_object* v_k_697_){
_start:
{
uint8_t v_res_698_; lean_object* v_r_699_; 
v_res_698_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(v_00_u03b2_692_, v_keys_693_, v_vals_694_, v_heq_695_, v_i_696_, v_k_697_);
lean_dec_ref(v_k_697_);
lean_dec_ref(v_vals_694_);
lean_dec_ref(v_keys_693_);
v_r_699_ = lean_box(v_res_698_);
return v_r_699_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__9));
v___x_720_ = l_ReaderT_instMonad___redArg(v___x_719_);
return v___x_720_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10);
v___x_724_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_724_, 0, lean_box(0));
lean_closure_set(v___x_724_, 1, lean_box(0));
lean_closure_set(v___x_724_, 2, v___x_723_);
return v___x_724_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_725_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13);
v___x_726_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__12));
v___x_727_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__11));
v___x_728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v___x_726_);
lean_ctor_set(v___x_728_, 2, v___x_725_);
return v___x_728_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM(void){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS___redArg(lean_object* v_inst_730_, lean_object* v_l_731_){
_start:
{
lean_object* v_share1_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_share1_732_ = lean_ctor_get(v_inst_730_, 0);
lean_inc(v_share1_732_);
lean_dec_ref(v_inst_730_);
v___x_733_ = l_Lean_Expr_lit___override(v_l_731_);
v___x_734_ = lean_apply_1(v_share1_732_, v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS(lean_object* v_m_735_, lean_object* v_inst_736_, lean_object* v_l_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Meta_Sym_Internal_mkLitS___redArg(v_inst_736_, v_l_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___redArg(lean_object* v_inst_739_, lean_object* v_declName_740_, lean_object* v_us_741_){
_start:
{
lean_object* v_share1_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_share1_742_ = lean_ctor_get(v_inst_739_, 0);
lean_inc(v_share1_742_);
lean_dec_ref(v_inst_739_);
v___x_743_ = l_Lean_Expr_const___override(v_declName_740_, v_us_741_);
v___x_744_ = lean_apply_1(v_share1_742_, v___x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS(lean_object* v_m_745_, lean_object* v_inst_746_, lean_object* v_declName_747_, lean_object* v_us_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Meta_Sym_Internal_mkConstS___redArg(v_inst_746_, v_declName_747_, v_us_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object* v_inst_750_, lean_object* v_idx_751_){
_start:
{
lean_object* v_share1_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_share1_752_ = lean_ctor_get(v_inst_750_, 0);
lean_inc(v_share1_752_);
lean_dec_ref(v_inst_750_);
v___x_753_ = l_Lean_Expr_bvar___override(v_idx_751_);
v___x_754_ = lean_apply_1(v_share1_752_, v___x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS(lean_object* v_m_755_, lean_object* v_inst_756_, lean_object* v_idx_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v_inst_756_, v_idx_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___redArg(lean_object* v_inst_759_, lean_object* v_u_760_){
_start:
{
lean_object* v_share1_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_share1_761_ = lean_ctor_get(v_inst_759_, 0);
lean_inc(v_share1_761_);
lean_dec_ref(v_inst_759_);
v___x_762_ = l_Lean_Expr_sort___override(v_u_760_);
v___x_763_ = lean_apply_1(v_share1_761_, v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS(lean_object* v_m_764_, lean_object* v_inst_765_, lean_object* v_u_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_Meta_Sym_Internal_mkSortS___redArg(v_inst_765_, v_u_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object* v_inst_768_, lean_object* v_fvarId_769_){
_start:
{
lean_object* v_share1_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_share1_770_ = lean_ctor_get(v_inst_768_, 0);
lean_inc(v_share1_770_);
lean_dec_ref(v_inst_768_);
v___x_771_ = l_Lean_Expr_fvar___override(v_fvarId_769_);
v___x_772_ = lean_apply_1(v_share1_770_, v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS(lean_object* v_m_773_, lean_object* v_inst_774_, lean_object* v_fvarId_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_Meta_Sym_Internal_mkFVarS___redArg(v_inst_774_, v_fvarId_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___redArg(lean_object* v_inst_777_, lean_object* v_mvarId_778_){
_start:
{
lean_object* v_share1_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_share1_779_ = lean_ctor_get(v_inst_777_, 0);
lean_inc(v_share1_779_);
lean_dec_ref(v_inst_777_);
v___x_780_ = l_Lean_Expr_mvar___override(v_mvarId_778_);
v___x_781_ = lean_apply_1(v_share1_779_, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS(lean_object* v_m_782_, lean_object* v_inst_783_, lean_object* v_mvarId_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_Meta_Sym_Internal_mkMVarS___redArg(v_inst_783_, v_mvarId_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(lean_object* v_d_786_, lean_object* v_e_787_, lean_object* v_share1_788_, lean_object* v_____r_789_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = l_Lean_Expr_mdata___override(v_d_786_, v_e_787_);
v___x_791_ = lean_apply_1(v_share1_788_, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(lean_object* v___f_792_, lean_object* v_____r_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = lean_apply_1(v___f_792_, v_____r_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(lean_object* v___f_795_, lean_object* v_assertShared_796_, lean_object* v_e_797_, lean_object* v_toBind_798_, lean_object* v___f_799_, uint8_t v_____do__lift_800_){
_start:
{
if (v_____do__lift_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec(v___f_799_);
lean_dec(v_toBind_798_);
lean_dec_ref(v_e_797_);
lean_dec(v_assertShared_796_);
v___x_801_ = lean_box(0);
v___x_802_ = lean_apply_1(v___f_795_, v___x_801_);
return v___x_802_;
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec(v___f_795_);
v___x_803_ = lean_apply_1(v_assertShared_796_, v_e_797_);
v___x_804_ = lean_apply_4(v_toBind_798_, lean_box(0), lean_box(0), v___x_803_, v___f_799_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(lean_object* v___f_805_, lean_object* v_assertShared_806_, lean_object* v_e_807_, lean_object* v_toBind_808_, lean_object* v___f_809_, lean_object* v_____do__lift_810_){
_start:
{
uint8_t v_____do__lift_63__boxed_811_; lean_object* v_res_812_; 
v_____do__lift_63__boxed_811_ = lean_unbox(v_____do__lift_810_);
v_res_812_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(v___f_805_, v_assertShared_806_, v_e_807_, v_toBind_808_, v___f_809_, v_____do__lift_63__boxed_811_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_d_815_, lean_object* v_e_816_){
_start:
{
lean_object* v_toBind_817_; lean_object* v_share1_818_; lean_object* v_assertShared_819_; lean_object* v_isDebugEnabled_820_; lean_object* v___f_821_; lean_object* v___f_822_; lean_object* v___f_823_; lean_object* v___x_824_; 
v_toBind_817_ = lean_ctor_get(v_inst_814_, 1);
lean_inc_n(v_toBind_817_, 2);
lean_dec_ref(v_inst_814_);
v_share1_818_ = lean_ctor_get(v_inst_813_, 0);
lean_inc(v_share1_818_);
v_assertShared_819_ = lean_ctor_get(v_inst_813_, 1);
lean_inc(v_assertShared_819_);
v_isDebugEnabled_820_ = lean_ctor_get(v_inst_813_, 2);
lean_inc(v_isDebugEnabled_820_);
lean_dec_ref(v_inst_813_);
lean_inc_ref(v_e_816_);
v___f_821_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_821_, 0, v_d_815_);
lean_closure_set(v___f_821_, 1, v_e_816_);
lean_closure_set(v___f_821_, 2, v_share1_818_);
lean_inc_ref(v___f_821_);
v___f_822_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_822_, 0, v___f_821_);
v___f_823_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_823_, 0, v___f_821_);
lean_closure_set(v___f_823_, 1, v_assertShared_819_);
lean_closure_set(v___f_823_, 2, v_e_816_);
lean_closure_set(v___f_823_, 3, v_toBind_817_);
lean_closure_set(v___f_823_, 4, v___f_822_);
v___x_824_ = lean_apply_4(v_toBind_817_, lean_box(0), lean_box(0), v_isDebugEnabled_820_, v___f_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS(lean_object* v_m_825_, lean_object* v_inst_826_, lean_object* v_inst_827_, lean_object* v_d_828_, lean_object* v_e_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_826_, v_inst_827_, v_d_828_, v_e_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(lean_object* v_structName_831_, lean_object* v_idx_832_, lean_object* v_struct_833_, lean_object* v_share1_834_, lean_object* v_____r_835_){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = l_Lean_Expr_proj___override(v_structName_831_, v_idx_832_, v_struct_833_);
v___x_837_ = lean_apply_1(v_share1_834_, v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(lean_object* v___f_838_, lean_object* v_assertShared_839_, lean_object* v_struct_840_, lean_object* v_toBind_841_, lean_object* v___f_842_, uint8_t v_____do__lift_843_){
_start:
{
if (v_____do__lift_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec(v___f_842_);
lean_dec(v_toBind_841_);
lean_dec_ref(v_struct_840_);
lean_dec(v_assertShared_839_);
v___x_844_ = lean_box(0);
v___x_845_ = lean_apply_1(v___f_838_, v___x_844_);
return v___x_845_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec(v___f_838_);
v___x_846_ = lean_apply_1(v_assertShared_839_, v_struct_840_);
v___x_847_ = lean_apply_4(v_toBind_841_, lean_box(0), lean_box(0), v___x_846_, v___f_842_);
return v___x_847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(lean_object* v___f_848_, lean_object* v_assertShared_849_, lean_object* v_struct_850_, lean_object* v_toBind_851_, lean_object* v___f_852_, lean_object* v_____do__lift_853_){
_start:
{
uint8_t v_____do__lift_57__boxed_854_; lean_object* v_res_855_; 
v_____do__lift_57__boxed_854_ = lean_unbox(v_____do__lift_853_);
v_res_855_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(v___f_848_, v_assertShared_849_, v_struct_850_, v_toBind_851_, v___f_852_, v_____do__lift_57__boxed_854_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_structName_858_, lean_object* v_idx_859_, lean_object* v_struct_860_){
_start:
{
lean_object* v_toBind_861_; lean_object* v_share1_862_; lean_object* v_assertShared_863_; lean_object* v_isDebugEnabled_864_; lean_object* v___f_865_; lean_object* v___f_866_; lean_object* v___f_867_; lean_object* v___x_868_; 
v_toBind_861_ = lean_ctor_get(v_inst_857_, 1);
lean_inc_n(v_toBind_861_, 2);
lean_dec_ref(v_inst_857_);
v_share1_862_ = lean_ctor_get(v_inst_856_, 0);
lean_inc(v_share1_862_);
v_assertShared_863_ = lean_ctor_get(v_inst_856_, 1);
lean_inc(v_assertShared_863_);
v_isDebugEnabled_864_ = lean_ctor_get(v_inst_856_, 2);
lean_inc(v_isDebugEnabled_864_);
lean_dec_ref(v_inst_856_);
lean_inc_ref(v_struct_860_);
v___f_865_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0), 5, 4);
lean_closure_set(v___f_865_, 0, v_structName_858_);
lean_closure_set(v___f_865_, 1, v_idx_859_);
lean_closure_set(v___f_865_, 2, v_struct_860_);
lean_closure_set(v___f_865_, 3, v_share1_862_);
lean_inc_ref(v___f_865_);
v___f_866_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_866_, 0, v___f_865_);
v___f_867_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_867_, 0, v___f_865_);
lean_closure_set(v___f_867_, 1, v_assertShared_863_);
lean_closure_set(v___f_867_, 2, v_struct_860_);
lean_closure_set(v___f_867_, 3, v_toBind_861_);
lean_closure_set(v___f_867_, 4, v___f_866_);
v___x_868_ = lean_apply_4(v_toBind_861_, lean_box(0), lean_box(0), v_isDebugEnabled_864_, v___f_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS(lean_object* v_m_869_, lean_object* v_inst_870_, lean_object* v_inst_871_, lean_object* v_structName_872_, lean_object* v_idx_873_, lean_object* v_struct_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_870_, v_inst_871_, v_structName_872_, v_idx_873_, v_struct_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(lean_object* v_f_876_, lean_object* v_a_877_, lean_object* v_share1_878_, lean_object* v_____r_879_){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = l_Lean_Expr_app___override(v_f_876_, v_a_877_);
v___x_881_ = lean_apply_1(v_share1_878_, v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(lean_object* v_assertShared_882_, lean_object* v_a_883_, lean_object* v_toBind_884_, lean_object* v___f_885_, lean_object* v_____r_886_){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_apply_1(v_assertShared_882_, v_a_883_);
v___x_888_ = lean_apply_4(v_toBind_884_, lean_box(0), lean_box(0), v___x_887_, v___f_885_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(lean_object* v___f_889_, lean_object* v_assertShared_890_, lean_object* v_a_891_, lean_object* v_toBind_892_, lean_object* v___f_893_, lean_object* v_f_894_, uint8_t v_____do__lift_895_){
_start:
{
if (v_____do__lift_895_ == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; 
lean_dec_ref(v_f_894_);
lean_dec(v___f_893_);
lean_dec(v_toBind_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_assertShared_890_);
v___x_896_ = lean_box(0);
v___x_897_ = lean_apply_1(v___f_889_, v___x_896_);
return v___x_897_;
}
else
{
lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
lean_dec(v___f_889_);
lean_inc(v_toBind_892_);
lean_inc(v_assertShared_890_);
v___f_898_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_898_, 0, v_assertShared_890_);
lean_closure_set(v___f_898_, 1, v_a_891_);
lean_closure_set(v___f_898_, 2, v_toBind_892_);
lean_closure_set(v___f_898_, 3, v___f_893_);
v___x_899_ = lean_apply_1(v_assertShared_890_, v_f_894_);
v___x_900_ = lean_apply_4(v_toBind_892_, lean_box(0), lean_box(0), v___x_899_, v___f_898_);
return v___x_900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(lean_object* v___f_901_, lean_object* v_assertShared_902_, lean_object* v_a_903_, lean_object* v_toBind_904_, lean_object* v___f_905_, lean_object* v_f_906_, lean_object* v_____do__lift_907_){
_start:
{
uint8_t v_____do__lift_74__boxed_908_; lean_object* v_res_909_; 
v_____do__lift_74__boxed_908_ = lean_unbox(v_____do__lift_907_);
v_res_909_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(v___f_901_, v_assertShared_902_, v_a_903_, v_toBind_904_, v___f_905_, v_f_906_, v_____do__lift_74__boxed_908_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object* v_inst_910_, lean_object* v_inst_911_, lean_object* v_f_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_toBind_914_; lean_object* v_share1_915_; lean_object* v_assertShared_916_; lean_object* v_isDebugEnabled_917_; lean_object* v___f_918_; lean_object* v___f_919_; lean_object* v___f_920_; lean_object* v___x_921_; 
v_toBind_914_ = lean_ctor_get(v_inst_911_, 1);
lean_inc_n(v_toBind_914_, 2);
lean_dec_ref(v_inst_911_);
v_share1_915_ = lean_ctor_get(v_inst_910_, 0);
lean_inc(v_share1_915_);
v_assertShared_916_ = lean_ctor_get(v_inst_910_, 1);
lean_inc(v_assertShared_916_);
v_isDebugEnabled_917_ = lean_ctor_get(v_inst_910_, 2);
lean_inc(v_isDebugEnabled_917_);
lean_dec_ref(v_inst_910_);
lean_inc_ref(v_a_913_);
lean_inc_ref(v_f_912_);
v___f_918_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_918_, 0, v_f_912_);
lean_closure_set(v___f_918_, 1, v_a_913_);
lean_closure_set(v___f_918_, 2, v_share1_915_);
lean_inc_ref(v___f_918_);
v___f_919_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_919_, 0, v___f_918_);
v___f_920_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_920_, 0, v___f_918_);
lean_closure_set(v___f_920_, 1, v_assertShared_916_);
lean_closure_set(v___f_920_, 2, v_a_913_);
lean_closure_set(v___f_920_, 3, v_toBind_914_);
lean_closure_set(v___f_920_, 4, v___f_919_);
lean_closure_set(v___f_920_, 5, v_f_912_);
v___x_921_ = lean_apply_4(v_toBind_914_, lean_box(0), lean_box(0), v_isDebugEnabled_917_, v___f_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS(lean_object* v_m_922_, lean_object* v_inst_923_, lean_object* v_inst_924_, lean_object* v_f_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_923_, v_inst_924_, v_f_925_, v_a_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(lean_object* v_x_928_, lean_object* v_t_929_, lean_object* v_b_930_, uint8_t v_bi_931_, lean_object* v_share1_932_, lean_object* v_____r_933_){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = l_Lean_Expr_lam___override(v_x_928_, v_t_929_, v_b_930_, v_bi_931_);
v___x_935_ = lean_apply_1(v_share1_932_, v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(lean_object* v_x_936_, lean_object* v_t_937_, lean_object* v_b_938_, lean_object* v_bi_939_, lean_object* v_share1_940_, lean_object* v_____r_941_){
_start:
{
uint8_t v_bi_boxed_942_; lean_object* v_res_943_; 
v_bi_boxed_942_ = lean_unbox(v_bi_939_);
v_res_943_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(v_x_936_, v_t_937_, v_b_938_, v_bi_boxed_942_, v_share1_940_, v_____r_941_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(lean_object* v_assertShared_944_, lean_object* v_b_945_, lean_object* v_toBind_946_, lean_object* v___f_947_, lean_object* v_____r_948_){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = lean_apply_1(v_assertShared_944_, v_b_945_);
v___x_950_ = lean_apply_4(v_toBind_946_, lean_box(0), lean_box(0), v___x_949_, v___f_947_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(lean_object* v___f_951_, lean_object* v_assertShared_952_, lean_object* v_b_953_, lean_object* v_toBind_954_, lean_object* v___f_955_, lean_object* v_t_956_, uint8_t v_____do__lift_957_){
_start:
{
if (v_____do__lift_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec_ref(v_t_956_);
lean_dec(v___f_955_);
lean_dec(v_toBind_954_);
lean_dec_ref(v_b_953_);
lean_dec(v_assertShared_952_);
v___x_958_ = lean_box(0);
v___x_959_ = lean_apply_1(v___f_951_, v___x_958_);
return v___x_959_;
}
else
{
lean_object* v___f_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
lean_dec(v___f_951_);
lean_inc(v_toBind_954_);
lean_inc(v_assertShared_952_);
v___f_960_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_960_, 0, v_assertShared_952_);
lean_closure_set(v___f_960_, 1, v_b_953_);
lean_closure_set(v___f_960_, 2, v_toBind_954_);
lean_closure_set(v___f_960_, 3, v___f_955_);
v___x_961_ = lean_apply_1(v_assertShared_952_, v_t_956_);
v___x_962_ = lean_apply_4(v_toBind_954_, lean_box(0), lean_box(0), v___x_961_, v___f_960_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(lean_object* v___f_963_, lean_object* v_assertShared_964_, lean_object* v_b_965_, lean_object* v_toBind_966_, lean_object* v___f_967_, lean_object* v_t_968_, lean_object* v_____do__lift_969_){
_start:
{
uint8_t v_____do__lift_75__boxed_970_; lean_object* v_res_971_; 
v_____do__lift_75__boxed_970_ = lean_unbox(v_____do__lift_969_);
v_res_971_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(v___f_963_, v_assertShared_964_, v_b_965_, v_toBind_966_, v___f_967_, v_t_968_, v_____do__lift_75__boxed_970_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_x_974_, uint8_t v_bi_975_, lean_object* v_t_976_, lean_object* v_b_977_){
_start:
{
lean_object* v_toBind_978_; lean_object* v_share1_979_; lean_object* v_assertShared_980_; lean_object* v_isDebugEnabled_981_; lean_object* v___x_982_; lean_object* v___f_983_; lean_object* v___f_984_; lean_object* v___f_985_; lean_object* v___x_986_; 
v_toBind_978_ = lean_ctor_get(v_inst_973_, 1);
lean_inc_n(v_toBind_978_, 2);
lean_dec_ref(v_inst_973_);
v_share1_979_ = lean_ctor_get(v_inst_972_, 0);
lean_inc(v_share1_979_);
v_assertShared_980_ = lean_ctor_get(v_inst_972_, 1);
lean_inc(v_assertShared_980_);
v_isDebugEnabled_981_ = lean_ctor_get(v_inst_972_, 2);
lean_inc(v_isDebugEnabled_981_);
lean_dec_ref(v_inst_972_);
v___x_982_ = lean_box(v_bi_975_);
lean_inc_ref(v_b_977_);
lean_inc_ref(v_t_976_);
v___f_983_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_983_, 0, v_x_974_);
lean_closure_set(v___f_983_, 1, v_t_976_);
lean_closure_set(v___f_983_, 2, v_b_977_);
lean_closure_set(v___f_983_, 3, v___x_982_);
lean_closure_set(v___f_983_, 4, v_share1_979_);
lean_inc_ref(v___f_983_);
v___f_984_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_984_, 0, v___f_983_);
v___f_985_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_985_, 0, v___f_983_);
lean_closure_set(v___f_985_, 1, v_assertShared_980_);
lean_closure_set(v___f_985_, 2, v_b_977_);
lean_closure_set(v___f_985_, 3, v_toBind_978_);
lean_closure_set(v___f_985_, 4, v___f_984_);
lean_closure_set(v___f_985_, 5, v_t_976_);
v___x_986_ = lean_apply_4(v_toBind_978_, lean_box(0), lean_box(0), v_isDebugEnabled_981_, v___f_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(lean_object* v_inst_987_, lean_object* v_inst_988_, lean_object* v_x_989_, lean_object* v_bi_990_, lean_object* v_t_991_, lean_object* v_b_992_){
_start:
{
uint8_t v_bi_boxed_993_; lean_object* v_res_994_; 
v_bi_boxed_993_ = lean_unbox(v_bi_990_);
v_res_994_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_987_, v_inst_988_, v_x_989_, v_bi_boxed_993_, v_t_991_, v_b_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS(lean_object* v_m_995_, lean_object* v_inst_996_, lean_object* v_inst_997_, lean_object* v_x_998_, uint8_t v_bi_999_, lean_object* v_t_1000_, lean_object* v_b_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_996_, v_inst_997_, v_x_998_, v_bi_999_, v_t_1000_, v_b_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(lean_object* v_m_1003_, lean_object* v_inst_1004_, lean_object* v_inst_1005_, lean_object* v_x_1006_, lean_object* v_bi_1007_, lean_object* v_t_1008_, lean_object* v_b_1009_){
_start:
{
uint8_t v_bi_boxed_1010_; lean_object* v_res_1011_; 
v_bi_boxed_1010_ = lean_unbox(v_bi_1007_);
v_res_1011_ = l_Lean_Meta_Sym_Internal_mkLambdaS(v_m_1003_, v_inst_1004_, v_inst_1005_, v_x_1006_, v_bi_boxed_1010_, v_t_1008_, v_b_1009_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(lean_object* v_x_1012_, lean_object* v_t_1013_, lean_object* v_b_1014_, uint8_t v_bi_1015_, lean_object* v_share1_1016_, lean_object* v_____r_1017_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = l_Lean_Expr_forallE___override(v_x_1012_, v_t_1013_, v_b_1014_, v_bi_1015_);
v___x_1019_ = lean_apply_1(v_share1_1016_, v___x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(lean_object* v_x_1020_, lean_object* v_t_1021_, lean_object* v_b_1022_, lean_object* v_bi_1023_, lean_object* v_share1_1024_, lean_object* v_____r_1025_){
_start:
{
uint8_t v_bi_boxed_1026_; lean_object* v_res_1027_; 
v_bi_boxed_1026_ = lean_unbox(v_bi_1023_);
v_res_1027_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(v_x_1020_, v_t_1021_, v_b_1022_, v_bi_boxed_1026_, v_share1_1024_, v_____r_1025_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_x_1030_, uint8_t v_bi_1031_, lean_object* v_t_1032_, lean_object* v_b_1033_){
_start:
{
lean_object* v_toBind_1034_; lean_object* v_share1_1035_; lean_object* v_assertShared_1036_; lean_object* v_isDebugEnabled_1037_; lean_object* v___x_1038_; lean_object* v___f_1039_; lean_object* v___f_1040_; lean_object* v___f_1041_; lean_object* v___x_1042_; 
v_toBind_1034_ = lean_ctor_get(v_inst_1029_, 1);
lean_inc_n(v_toBind_1034_, 2);
lean_dec_ref(v_inst_1029_);
v_share1_1035_ = lean_ctor_get(v_inst_1028_, 0);
lean_inc(v_share1_1035_);
v_assertShared_1036_ = lean_ctor_get(v_inst_1028_, 1);
lean_inc(v_assertShared_1036_);
v_isDebugEnabled_1037_ = lean_ctor_get(v_inst_1028_, 2);
lean_inc(v_isDebugEnabled_1037_);
lean_dec_ref(v_inst_1028_);
v___x_1038_ = lean_box(v_bi_1031_);
lean_inc_ref(v_b_1033_);
lean_inc_ref(v_t_1032_);
v___f_1039_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1039_, 0, v_x_1030_);
lean_closure_set(v___f_1039_, 1, v_t_1032_);
lean_closure_set(v___f_1039_, 2, v_b_1033_);
lean_closure_set(v___f_1039_, 3, v___x_1038_);
lean_closure_set(v___f_1039_, 4, v_share1_1035_);
lean_inc_ref(v___f_1039_);
v___f_1040_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1040_, 0, v___f_1039_);
v___f_1041_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1041_, 0, v___f_1039_);
lean_closure_set(v___f_1041_, 1, v_assertShared_1036_);
lean_closure_set(v___f_1041_, 2, v_b_1033_);
lean_closure_set(v___f_1041_, 3, v_toBind_1034_);
lean_closure_set(v___f_1041_, 4, v___f_1040_);
lean_closure_set(v___f_1041_, 5, v_t_1032_);
v___x_1042_ = lean_apply_4(v_toBind_1034_, lean_box(0), lean_box(0), v_isDebugEnabled_1037_, v___f_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_x_1045_, lean_object* v_bi_1046_, lean_object* v_t_1047_, lean_object* v_b_1048_){
_start:
{
uint8_t v_bi_boxed_1049_; lean_object* v_res_1050_; 
v_bi_boxed_1049_ = lean_unbox(v_bi_1046_);
v_res_1050_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1043_, v_inst_1044_, v_x_1045_, v_bi_boxed_1049_, v_t_1047_, v_b_1048_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS(lean_object* v_m_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_x_1054_, uint8_t v_bi_1055_, lean_object* v_t_1056_, lean_object* v_b_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1052_, v_inst_1053_, v_x_1054_, v_bi_1055_, v_t_1056_, v_b_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___boxed(lean_object* v_m_1059_, lean_object* v_inst_1060_, lean_object* v_inst_1061_, lean_object* v_x_1062_, lean_object* v_bi_1063_, lean_object* v_t_1064_, lean_object* v_b_1065_){
_start:
{
uint8_t v_bi_boxed_1066_; lean_object* v_res_1067_; 
v_bi_boxed_1066_ = lean_unbox(v_bi_1063_);
v_res_1067_ = l_Lean_Meta_Sym_Internal_mkForallS(v_m_1059_, v_inst_1060_, v_inst_1061_, v_x_1062_, v_bi_boxed_1066_, v_t_1064_, v_b_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(lean_object* v_x_1068_, lean_object* v_t_1069_, lean_object* v_v_1070_, lean_object* v_b_1071_, uint8_t v_nondep_1072_, lean_object* v_share1_1073_, lean_object* v_____r_1074_){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = l_Lean_Expr_letE___override(v_x_1068_, v_t_1069_, v_v_1070_, v_b_1071_, v_nondep_1072_);
v___x_1076_ = lean_apply_1(v_share1_1073_, v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(lean_object* v_x_1077_, lean_object* v_t_1078_, lean_object* v_v_1079_, lean_object* v_b_1080_, lean_object* v_nondep_1081_, lean_object* v_share1_1082_, lean_object* v_____r_1083_){
_start:
{
uint8_t v_nondep_boxed_1084_; lean_object* v_res_1085_; 
v_nondep_boxed_1084_ = lean_unbox(v_nondep_1081_);
v_res_1085_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(v_x_1077_, v_t_1078_, v_v_1079_, v_b_1080_, v_nondep_boxed_1084_, v_share1_1082_, v_____r_1083_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(lean_object* v_assertShared_1086_, lean_object* v_v_1087_, lean_object* v_toBind_1088_, lean_object* v___f_1089_, lean_object* v_____r_1090_){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_apply_1(v_assertShared_1086_, v_v_1087_);
v___x_1092_ = lean_apply_4(v_toBind_1088_, lean_box(0), lean_box(0), v___x_1091_, v___f_1089_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(lean_object* v___f_1093_, lean_object* v_assertShared_1094_, lean_object* v_b_1095_, lean_object* v_toBind_1096_, lean_object* v___f_1097_, lean_object* v_v_1098_, lean_object* v_t_1099_, uint8_t v_____do__lift_1100_){
_start:
{
if (v_____do__lift_1100_ == 0)
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_dec_ref(v_t_1099_);
lean_dec_ref(v_v_1098_);
lean_dec(v___f_1097_);
lean_dec(v_toBind_1096_);
lean_dec_ref(v_b_1095_);
lean_dec(v_assertShared_1094_);
v___x_1101_ = lean_box(0);
v___x_1102_ = lean_apply_1(v___f_1093_, v___x_1101_);
return v___x_1102_;
}
else
{
lean_object* v___f_1103_; lean_object* v___f_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec(v___f_1093_);
lean_inc_n(v_toBind_1096_, 2);
lean_inc_n(v_assertShared_1094_, 2);
v___f_1103_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1103_, 0, v_assertShared_1094_);
lean_closure_set(v___f_1103_, 1, v_b_1095_);
lean_closure_set(v___f_1103_, 2, v_toBind_1096_);
lean_closure_set(v___f_1103_, 3, v___f_1097_);
v___f_1104_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1104_, 0, v_assertShared_1094_);
lean_closure_set(v___f_1104_, 1, v_v_1098_);
lean_closure_set(v___f_1104_, 2, v_toBind_1096_);
lean_closure_set(v___f_1104_, 3, v___f_1103_);
v___x_1105_ = lean_apply_1(v_assertShared_1094_, v_t_1099_);
v___x_1106_ = lean_apply_4(v_toBind_1096_, lean_box(0), lean_box(0), v___x_1105_, v___f_1104_);
return v___x_1106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(lean_object* v___f_1107_, lean_object* v_assertShared_1108_, lean_object* v_b_1109_, lean_object* v_toBind_1110_, lean_object* v___f_1111_, lean_object* v_v_1112_, lean_object* v_t_1113_, lean_object* v_____do__lift_1114_){
_start:
{
uint8_t v_____do__lift_84__boxed_1115_; lean_object* v_res_1116_; 
v_____do__lift_84__boxed_1115_ = lean_unbox(v_____do__lift_1114_);
v_res_1116_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(v___f_1107_, v_assertShared_1108_, v_b_1109_, v_toBind_1110_, v___f_1111_, v_v_1112_, v_t_1113_, v_____do__lift_84__boxed_1115_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_x_1119_, lean_object* v_t_1120_, lean_object* v_v_1121_, lean_object* v_b_1122_, uint8_t v_nondep_1123_){
_start:
{
lean_object* v_toBind_1124_; lean_object* v_share1_1125_; lean_object* v_assertShared_1126_; lean_object* v_isDebugEnabled_1127_; lean_object* v___x_1128_; lean_object* v___f_1129_; lean_object* v___f_1130_; lean_object* v___f_1131_; lean_object* v___x_1132_; 
v_toBind_1124_ = lean_ctor_get(v_inst_1118_, 1);
lean_inc_n(v_toBind_1124_, 2);
lean_dec_ref(v_inst_1118_);
v_share1_1125_ = lean_ctor_get(v_inst_1117_, 0);
lean_inc(v_share1_1125_);
v_assertShared_1126_ = lean_ctor_get(v_inst_1117_, 1);
lean_inc(v_assertShared_1126_);
v_isDebugEnabled_1127_ = lean_ctor_get(v_inst_1117_, 2);
lean_inc(v_isDebugEnabled_1127_);
lean_dec_ref(v_inst_1117_);
v___x_1128_ = lean_box(v_nondep_1123_);
lean_inc_ref(v_b_1122_);
lean_inc_ref(v_v_1121_);
lean_inc_ref(v_t_1120_);
v___f_1129_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1129_, 0, v_x_1119_);
lean_closure_set(v___f_1129_, 1, v_t_1120_);
lean_closure_set(v___f_1129_, 2, v_v_1121_);
lean_closure_set(v___f_1129_, 3, v_b_1122_);
lean_closure_set(v___f_1129_, 4, v___x_1128_);
lean_closure_set(v___f_1129_, 5, v_share1_1125_);
lean_inc_ref(v___f_1129_);
v___f_1130_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1130_, 0, v___f_1129_);
v___f_1131_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1131_, 0, v___f_1129_);
lean_closure_set(v___f_1131_, 1, v_assertShared_1126_);
lean_closure_set(v___f_1131_, 2, v_b_1122_);
lean_closure_set(v___f_1131_, 3, v_toBind_1124_);
lean_closure_set(v___f_1131_, 4, v___f_1130_);
lean_closure_set(v___f_1131_, 5, v_v_1121_);
lean_closure_set(v___f_1131_, 6, v_t_1120_);
v___x_1132_ = lean_apply_4(v_toBind_1124_, lean_box(0), lean_box(0), v_isDebugEnabled_1127_, v___f_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_x_1135_, lean_object* v_t_1136_, lean_object* v_v_1137_, lean_object* v_b_1138_, lean_object* v_nondep_1139_){
_start:
{
uint8_t v_nondep_boxed_1140_; lean_object* v_res_1141_; 
v_nondep_boxed_1140_ = lean_unbox(v_nondep_1139_);
v_res_1141_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1133_, v_inst_1134_, v_x_1135_, v_t_1136_, v_v_1137_, v_b_1138_, v_nondep_boxed_1140_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS(lean_object* v_m_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_x_1145_, lean_object* v_t_1146_, lean_object* v_v_1147_, lean_object* v_b_1148_, uint8_t v_nondep_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1143_, v_inst_1144_, v_x_1145_, v_t_1146_, v_v_1147_, v_b_1148_, v_nondep_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___boxed(lean_object* v_m_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_x_1154_, lean_object* v_t_1155_, lean_object* v_v_1156_, lean_object* v_b_1157_, lean_object* v_nondep_1158_){
_start:
{
uint8_t v_nondep_boxed_1159_; lean_object* v_res_1160_; 
v_nondep_boxed_1159_ = lean_unbox(v_nondep_1158_);
v_res_1160_ = l_Lean_Meta_Sym_Internal_mkLetS(v_m_1151_, v_inst_1152_, v_inst_1153_, v_x_1154_, v_t_1155_, v_v_1156_, v_b_1157_, v_nondep_boxed_1159_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(lean_object* v_x_1161_, lean_object* v_t_1162_, lean_object* v_v_1163_, lean_object* v_b_1164_, lean_object* v_share1_1165_, lean_object* v_____r_1166_){
_start:
{
uint8_t v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = 1;
v___x_1168_ = l_Lean_Expr_letE___override(v_x_1161_, v_t_1162_, v_v_1163_, v_b_1164_, v___x_1167_);
v___x_1169_ = lean_apply_1(v_share1_1165_, v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg(lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v_x_1172_, lean_object* v_t_1173_, lean_object* v_v_1174_, lean_object* v_b_1175_){
_start:
{
lean_object* v_toBind_1176_; lean_object* v_share1_1177_; lean_object* v_assertShared_1178_; lean_object* v_isDebugEnabled_1179_; lean_object* v___f_1180_; lean_object* v___f_1181_; lean_object* v___f_1182_; lean_object* v___x_1183_; 
v_toBind_1176_ = lean_ctor_get(v_inst_1171_, 1);
lean_inc_n(v_toBind_1176_, 2);
lean_dec_ref(v_inst_1171_);
v_share1_1177_ = lean_ctor_get(v_inst_1170_, 0);
lean_inc(v_share1_1177_);
v_assertShared_1178_ = lean_ctor_get(v_inst_1170_, 1);
lean_inc(v_assertShared_1178_);
v_isDebugEnabled_1179_ = lean_ctor_get(v_inst_1170_, 2);
lean_inc(v_isDebugEnabled_1179_);
lean_dec_ref(v_inst_1170_);
lean_inc_ref(v_b_1175_);
lean_inc_ref(v_v_1174_);
lean_inc_ref(v_t_1173_);
v___f_1180_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1180_, 0, v_x_1172_);
lean_closure_set(v___f_1180_, 1, v_t_1173_);
lean_closure_set(v___f_1180_, 2, v_v_1174_);
lean_closure_set(v___f_1180_, 3, v_b_1175_);
lean_closure_set(v___f_1180_, 4, v_share1_1177_);
lean_inc_ref(v___f_1180_);
v___f_1181_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1181_, 0, v___f_1180_);
v___f_1182_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1182_, 0, v___f_1180_);
lean_closure_set(v___f_1182_, 1, v_assertShared_1178_);
lean_closure_set(v___f_1182_, 2, v_b_1175_);
lean_closure_set(v___f_1182_, 3, v_toBind_1176_);
lean_closure_set(v___f_1182_, 4, v___f_1181_);
lean_closure_set(v___f_1182_, 5, v_v_1174_);
lean_closure_set(v___f_1182_, 6, v_t_1173_);
v___x_1183_ = lean_apply_4(v_toBind_1176_, lean_box(0), lean_box(0), v_isDebugEnabled_1179_, v___f_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS(lean_object* v_m_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_x_1187_, lean_object* v_t_1188_, lean_object* v_v_1189_, lean_object* v_b_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_Meta_Sym_Internal_mkHaveS___redArg(v_inst_1185_, v_inst_1186_, v_x_1187_, v_t_1188_, v_v_1189_, v_b_1190_);
return v___x_1191_;
}
}
static lean_object* _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1194_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__1));
v___x_1195_ = lean_unsigned_to_nat(25u);
v___x_1196_ = lean_unsigned_to_nat(148u);
v___x_1197_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__0));
v___x_1198_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1199_ = l_mkPanicMessageWithDecl(v___x_1198_, v___x_1197_, v___x_1196_, v___x_1195_, v___x_1194_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21___redArg(lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_e_1202_, lean_object* v_newFn_1203_, lean_object* v_newArg_1204_){
_start:
{
if (lean_obj_tag(v_e_1202_) == 5)
{
lean_object* v_toApplicative_1205_; lean_object* v_toPure_1206_; lean_object* v_fn_1207_; lean_object* v_arg_1208_; size_t v___x_1209_; size_t v___x_1210_; uint8_t v___x_1211_; 
v_toApplicative_1205_ = lean_ctor_get(v_inst_1201_, 0);
v_toPure_1206_ = lean_ctor_get(v_toApplicative_1205_, 1);
v_fn_1207_ = lean_ctor_get(v_e_1202_, 0);
v_arg_1208_ = lean_ctor_get(v_e_1202_, 1);
v___x_1209_ = lean_ptr_addr(v_fn_1207_);
v___x_1210_ = lean_ptr_addr(v_newFn_1203_);
v___x_1211_ = lean_usize_dec_eq(v___x_1209_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; 
lean_dec_ref_known(v_e_1202_, 2);
v___x_1212_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1200_, v_inst_1201_, v_newFn_1203_, v_newArg_1204_);
return v___x_1212_;
}
else
{
size_t v___x_1213_; size_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1213_ = lean_ptr_addr(v_arg_1208_);
v___x_1214_ = lean_ptr_addr(v_newArg_1204_);
v___x_1215_ = lean_usize_dec_eq(v___x_1213_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
lean_dec_ref_known(v_e_1202_, 2);
v___x_1216_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1200_, v_inst_1201_, v_newFn_1203_, v_newArg_1204_);
return v___x_1216_;
}
else
{
lean_object* v___x_1217_; 
lean_inc(v_toPure_1206_);
lean_dec_ref(v_newArg_1204_);
lean_dec_ref(v_newFn_1203_);
lean_dec_ref(v_inst_1201_);
lean_dec_ref(v_inst_1200_);
v___x_1217_ = lean_apply_2(v_toPure_1206_, lean_box(0), v_e_1202_);
return v___x_1217_;
}
}
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec_ref(v_newArg_1204_);
lean_dec_ref(v_newFn_1203_);
lean_dec_ref(v_e_1202_);
lean_dec_ref(v_inst_1200_);
v___x_1218_ = l_Lean_instInhabitedExpr;
v___x_1219_ = l_instInhabitedOfMonad___redArg(v_inst_1201_, v___x_1218_);
v___x_1220_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1221_ = l_panic___redArg(v___x_1219_, v___x_1220_);
lean_dec(v___x_1219_);
return v___x_1221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21(lean_object* v_m_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_e_1225_, lean_object* v_newFn_1226_, lean_object* v_newArg_1227_){
_start:
{
if (lean_obj_tag(v_e_1225_) == 5)
{
lean_object* v_toApplicative_1228_; lean_object* v_toPure_1229_; lean_object* v_fn_1230_; lean_object* v_arg_1231_; size_t v___x_1232_; size_t v___x_1233_; uint8_t v___x_1234_; 
v_toApplicative_1228_ = lean_ctor_get(v_inst_1224_, 0);
v_toPure_1229_ = lean_ctor_get(v_toApplicative_1228_, 1);
v_fn_1230_ = lean_ctor_get(v_e_1225_, 0);
v_arg_1231_ = lean_ctor_get(v_e_1225_, 1);
v___x_1232_ = lean_ptr_addr(v_fn_1230_);
v___x_1233_ = lean_ptr_addr(v_newFn_1226_);
v___x_1234_ = lean_usize_dec_eq(v___x_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec_ref_known(v_e_1225_, 2);
v___x_1235_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1223_, v_inst_1224_, v_newFn_1226_, v_newArg_1227_);
return v___x_1235_;
}
else
{
size_t v___x_1236_; size_t v___x_1237_; uint8_t v___x_1238_; 
v___x_1236_ = lean_ptr_addr(v_arg_1231_);
v___x_1237_ = lean_ptr_addr(v_newArg_1227_);
v___x_1238_ = lean_usize_dec_eq(v___x_1236_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_dec_ref_known(v_e_1225_, 2);
v___x_1239_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1223_, v_inst_1224_, v_newFn_1226_, v_newArg_1227_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; 
lean_inc(v_toPure_1229_);
lean_dec_ref(v_newArg_1227_);
lean_dec_ref(v_newFn_1226_);
lean_dec_ref(v_inst_1224_);
lean_dec_ref(v_inst_1223_);
v___x_1240_ = lean_apply_2(v_toPure_1229_, lean_box(0), v_e_1225_);
return v___x_1240_;
}
}
}
else
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec_ref(v_newArg_1227_);
lean_dec_ref(v_newFn_1226_);
lean_dec_ref(v_e_1225_);
lean_dec_ref(v_inst_1223_);
v___x_1241_ = l_Lean_instInhabitedExpr;
v___x_1242_ = l_instInhabitedOfMonad___redArg(v_inst_1224_, v___x_1241_);
v___x_1243_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1244_ = l_panic___redArg(v___x_1242_, v___x_1243_);
lean_dec(v___x_1242_);
return v___x_1244_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1247_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__1));
v___x_1248_ = lean_unsigned_to_nat(24u);
v___x_1249_ = lean_unsigned_to_nat(152u);
v___x_1250_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__0));
v___x_1251_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1252_ = l_mkPanicMessageWithDecl(v___x_1251_, v___x_1250_, v___x_1249_, v___x_1248_, v___x_1247_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21___redArg(lean_object* v_inst_1253_, lean_object* v_inst_1254_, lean_object* v_e_1255_, lean_object* v_newExpr_1256_){
_start:
{
if (lean_obj_tag(v_e_1255_) == 10)
{
lean_object* v_toApplicative_1257_; lean_object* v_toPure_1258_; lean_object* v_data_1259_; lean_object* v_expr_1260_; size_t v___x_1261_; size_t v___x_1262_; uint8_t v___x_1263_; 
v_toApplicative_1257_ = lean_ctor_get(v_inst_1254_, 0);
v_toPure_1258_ = lean_ctor_get(v_toApplicative_1257_, 1);
v_data_1259_ = lean_ctor_get(v_e_1255_, 0);
v_expr_1260_ = lean_ctor_get(v_e_1255_, 1);
v___x_1261_ = lean_ptr_addr(v_expr_1260_);
v___x_1262_ = lean_ptr_addr(v_newExpr_1256_);
v___x_1263_ = lean_usize_dec_eq(v___x_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
lean_inc(v_data_1259_);
lean_dec_ref_known(v_e_1255_, 2);
v___x_1264_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1253_, v_inst_1254_, v_data_1259_, v_newExpr_1256_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; 
lean_inc(v_toPure_1258_);
lean_dec_ref(v_newExpr_1256_);
lean_dec_ref(v_inst_1254_);
lean_dec_ref(v_inst_1253_);
v___x_1265_ = lean_apply_2(v_toPure_1258_, lean_box(0), v_e_1255_);
return v___x_1265_;
}
}
else
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec_ref(v_newExpr_1256_);
lean_dec_ref(v_e_1255_);
lean_dec_ref(v_inst_1253_);
v___x_1266_ = l_Lean_instInhabitedExpr;
v___x_1267_ = l_instInhabitedOfMonad___redArg(v_inst_1254_, v___x_1266_);
v___x_1268_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1269_ = l_panic___redArg(v___x_1267_, v___x_1268_);
lean_dec(v___x_1267_);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21(lean_object* v_m_1270_, lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_e_1273_, lean_object* v_newExpr_1274_){
_start:
{
if (lean_obj_tag(v_e_1273_) == 10)
{
lean_object* v_toApplicative_1275_; lean_object* v_toPure_1276_; lean_object* v_data_1277_; lean_object* v_expr_1278_; size_t v___x_1279_; size_t v___x_1280_; uint8_t v___x_1281_; 
v_toApplicative_1275_ = lean_ctor_get(v_inst_1272_, 0);
v_toPure_1276_ = lean_ctor_get(v_toApplicative_1275_, 1);
v_data_1277_ = lean_ctor_get(v_e_1273_, 0);
v_expr_1278_ = lean_ctor_get(v_e_1273_, 1);
v___x_1279_ = lean_ptr_addr(v_expr_1278_);
v___x_1280_ = lean_ptr_addr(v_newExpr_1274_);
v___x_1281_ = lean_usize_dec_eq(v___x_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_inc(v_data_1277_);
lean_dec_ref_known(v_e_1273_, 2);
v___x_1282_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1271_, v_inst_1272_, v_data_1277_, v_newExpr_1274_);
return v___x_1282_;
}
else
{
lean_object* v___x_1283_; 
lean_inc(v_toPure_1276_);
lean_dec_ref(v_newExpr_1274_);
lean_dec_ref(v_inst_1272_);
lean_dec_ref(v_inst_1271_);
v___x_1283_ = lean_apply_2(v_toPure_1276_, lean_box(0), v_e_1273_);
return v___x_1283_;
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec_ref(v_newExpr_1274_);
lean_dec_ref(v_e_1273_);
lean_dec_ref(v_inst_1271_);
v___x_1284_ = l_Lean_instInhabitedExpr;
v___x_1285_ = l_instInhabitedOfMonad___redArg(v_inst_1272_, v___x_1284_);
v___x_1286_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1287_ = l_panic___redArg(v___x_1285_, v___x_1286_);
lean_dec(v___x_1285_);
return v___x_1287_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1290_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__1));
v___x_1291_ = lean_unsigned_to_nat(25u);
v___x_1292_ = lean_unsigned_to_nat(156u);
v___x_1293_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__0));
v___x_1294_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1295_ = l_mkPanicMessageWithDecl(v___x_1294_, v___x_1293_, v___x_1292_, v___x_1291_, v___x_1290_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21___redArg(lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_e_1298_, lean_object* v_newExpr_1299_){
_start:
{
if (lean_obj_tag(v_e_1298_) == 11)
{
lean_object* v_toApplicative_1300_; lean_object* v_toPure_1301_; lean_object* v_typeName_1302_; lean_object* v_idx_1303_; lean_object* v_struct_1304_; size_t v___x_1305_; size_t v___x_1306_; uint8_t v___x_1307_; 
v_toApplicative_1300_ = lean_ctor_get(v_inst_1297_, 0);
v_toPure_1301_ = lean_ctor_get(v_toApplicative_1300_, 1);
v_typeName_1302_ = lean_ctor_get(v_e_1298_, 0);
v_idx_1303_ = lean_ctor_get(v_e_1298_, 1);
v_struct_1304_ = lean_ctor_get(v_e_1298_, 2);
v___x_1305_ = lean_ptr_addr(v_struct_1304_);
v___x_1306_ = lean_ptr_addr(v_newExpr_1299_);
v___x_1307_ = lean_usize_dec_eq(v___x_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; 
lean_inc(v_idx_1303_);
lean_inc(v_typeName_1302_);
lean_dec_ref_known(v_e_1298_, 3);
v___x_1308_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1296_, v_inst_1297_, v_typeName_1302_, v_idx_1303_, v_newExpr_1299_);
return v___x_1308_;
}
else
{
lean_object* v___x_1309_; 
lean_inc(v_toPure_1301_);
lean_dec_ref(v_newExpr_1299_);
lean_dec_ref(v_inst_1297_);
lean_dec_ref(v_inst_1296_);
v___x_1309_ = lean_apply_2(v_toPure_1301_, lean_box(0), v_e_1298_);
return v___x_1309_;
}
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_dec_ref(v_newExpr_1299_);
lean_dec_ref(v_e_1298_);
lean_dec_ref(v_inst_1296_);
v___x_1310_ = l_Lean_instInhabitedExpr;
v___x_1311_ = l_instInhabitedOfMonad___redArg(v_inst_1297_, v___x_1310_);
v___x_1312_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1313_ = l_panic___redArg(v___x_1311_, v___x_1312_);
lean_dec(v___x_1311_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21(lean_object* v_m_1314_, lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_e_1317_, lean_object* v_newExpr_1318_){
_start:
{
if (lean_obj_tag(v_e_1317_) == 11)
{
lean_object* v_toApplicative_1319_; lean_object* v_toPure_1320_; lean_object* v_typeName_1321_; lean_object* v_idx_1322_; lean_object* v_struct_1323_; size_t v___x_1324_; size_t v___x_1325_; uint8_t v___x_1326_; 
v_toApplicative_1319_ = lean_ctor_get(v_inst_1316_, 0);
v_toPure_1320_ = lean_ctor_get(v_toApplicative_1319_, 1);
v_typeName_1321_ = lean_ctor_get(v_e_1317_, 0);
v_idx_1322_ = lean_ctor_get(v_e_1317_, 1);
v_struct_1323_ = lean_ctor_get(v_e_1317_, 2);
v___x_1324_ = lean_ptr_addr(v_struct_1323_);
v___x_1325_ = lean_ptr_addr(v_newExpr_1318_);
v___x_1326_ = lean_usize_dec_eq(v___x_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
lean_inc(v_idx_1322_);
lean_inc(v_typeName_1321_);
lean_dec_ref_known(v_e_1317_, 3);
v___x_1327_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1315_, v_inst_1316_, v_typeName_1321_, v_idx_1322_, v_newExpr_1318_);
return v___x_1327_;
}
else
{
lean_object* v___x_1328_; 
lean_inc(v_toPure_1320_);
lean_dec_ref(v_newExpr_1318_);
lean_dec_ref(v_inst_1316_);
lean_dec_ref(v_inst_1315_);
v___x_1328_ = lean_apply_2(v_toPure_1320_, lean_box(0), v_e_1317_);
return v___x_1328_;
}
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec_ref(v_newExpr_1318_);
lean_dec_ref(v_e_1317_);
lean_dec_ref(v_inst_1315_);
v___x_1329_ = l_Lean_instInhabitedExpr;
v___x_1330_ = l_instInhabitedOfMonad___redArg(v_inst_1316_, v___x_1329_);
v___x_1331_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1332_ = l_panic___redArg(v___x_1330_, v___x_1331_);
lean_dec(v___x_1330_);
return v___x_1332_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1335_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__1));
v___x_1336_ = lean_unsigned_to_nat(31u);
v___x_1337_ = lean_unsigned_to_nat(160u);
v___x_1338_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__0));
v___x_1339_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1340_ = l_mkPanicMessageWithDecl(v___x_1339_, v___x_1338_, v___x_1337_, v___x_1336_, v___x_1335_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21___redArg(lean_object* v_inst_1341_, lean_object* v_inst_1342_, lean_object* v_e_1343_, lean_object* v_newDomain_1344_, lean_object* v_newBody_1345_){
_start:
{
if (lean_obj_tag(v_e_1343_) == 7)
{
lean_object* v_toApplicative_1346_; lean_object* v_toPure_1347_; lean_object* v_binderName_1348_; lean_object* v_binderType_1349_; lean_object* v_body_1350_; uint8_t v_binderInfo_1351_; size_t v___x_1352_; size_t v___x_1353_; uint8_t v___x_1354_; 
v_toApplicative_1346_ = lean_ctor_get(v_inst_1342_, 0);
v_toPure_1347_ = lean_ctor_get(v_toApplicative_1346_, 1);
v_binderName_1348_ = lean_ctor_get(v_e_1343_, 0);
v_binderType_1349_ = lean_ctor_get(v_e_1343_, 1);
v_body_1350_ = lean_ctor_get(v_e_1343_, 2);
v_binderInfo_1351_ = lean_ctor_get_uint8(v_e_1343_, sizeof(void*)*3 + 8);
v___x_1352_ = lean_ptr_addr(v_binderType_1349_);
v___x_1353_ = lean_ptr_addr(v_newDomain_1344_);
v___x_1354_ = lean_usize_dec_eq(v___x_1352_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
lean_inc(v_binderName_1348_);
lean_dec_ref_known(v_e_1343_, 3);
v___x_1355_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1341_, v_inst_1342_, v_binderName_1348_, v_binderInfo_1351_, v_newDomain_1344_, v_newBody_1345_);
return v___x_1355_;
}
else
{
size_t v___x_1356_; size_t v___x_1357_; uint8_t v___x_1358_; 
v___x_1356_ = lean_ptr_addr(v_body_1350_);
v___x_1357_ = lean_ptr_addr(v_newBody_1345_);
v___x_1358_ = lean_usize_dec_eq(v___x_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
lean_inc(v_binderName_1348_);
lean_dec_ref_known(v_e_1343_, 3);
v___x_1359_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1341_, v_inst_1342_, v_binderName_1348_, v_binderInfo_1351_, v_newDomain_1344_, v_newBody_1345_);
return v___x_1359_;
}
else
{
lean_object* v___x_1360_; 
lean_inc(v_toPure_1347_);
lean_dec_ref(v_newBody_1345_);
lean_dec_ref(v_newDomain_1344_);
lean_dec_ref(v_inst_1342_);
lean_dec_ref(v_inst_1341_);
v___x_1360_ = lean_apply_2(v_toPure_1347_, lean_box(0), v_e_1343_);
return v___x_1360_;
}
}
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_dec_ref(v_newBody_1345_);
lean_dec_ref(v_newDomain_1344_);
lean_dec_ref(v_e_1343_);
lean_dec_ref(v_inst_1341_);
v___x_1361_ = l_Lean_instInhabitedExpr;
v___x_1362_ = l_instInhabitedOfMonad___redArg(v_inst_1342_, v___x_1361_);
v___x_1363_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1364_ = l_panic___redArg(v___x_1362_, v___x_1363_);
lean_dec(v___x_1362_);
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21(lean_object* v_m_1365_, lean_object* v_inst_1366_, lean_object* v_inst_1367_, lean_object* v_e_1368_, lean_object* v_newDomain_1369_, lean_object* v_newBody_1370_){
_start:
{
if (lean_obj_tag(v_e_1368_) == 7)
{
lean_object* v_toApplicative_1371_; lean_object* v_toPure_1372_; lean_object* v_binderName_1373_; lean_object* v_binderType_1374_; lean_object* v_body_1375_; uint8_t v_binderInfo_1376_; size_t v___x_1377_; size_t v___x_1378_; uint8_t v___x_1379_; 
v_toApplicative_1371_ = lean_ctor_get(v_inst_1367_, 0);
v_toPure_1372_ = lean_ctor_get(v_toApplicative_1371_, 1);
v_binderName_1373_ = lean_ctor_get(v_e_1368_, 0);
v_binderType_1374_ = lean_ctor_get(v_e_1368_, 1);
v_body_1375_ = lean_ctor_get(v_e_1368_, 2);
v_binderInfo_1376_ = lean_ctor_get_uint8(v_e_1368_, sizeof(void*)*3 + 8);
v___x_1377_ = lean_ptr_addr(v_binderType_1374_);
v___x_1378_ = lean_ptr_addr(v_newDomain_1369_);
v___x_1379_ = lean_usize_dec_eq(v___x_1377_, v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
lean_inc(v_binderName_1373_);
lean_dec_ref_known(v_e_1368_, 3);
v___x_1380_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1366_, v_inst_1367_, v_binderName_1373_, v_binderInfo_1376_, v_newDomain_1369_, v_newBody_1370_);
return v___x_1380_;
}
else
{
size_t v___x_1381_; size_t v___x_1382_; uint8_t v___x_1383_; 
v___x_1381_ = lean_ptr_addr(v_body_1375_);
v___x_1382_ = lean_ptr_addr(v_newBody_1370_);
v___x_1383_ = lean_usize_dec_eq(v___x_1381_, v___x_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; 
lean_inc(v_binderName_1373_);
lean_dec_ref_known(v_e_1368_, 3);
v___x_1384_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1366_, v_inst_1367_, v_binderName_1373_, v_binderInfo_1376_, v_newDomain_1369_, v_newBody_1370_);
return v___x_1384_;
}
else
{
lean_object* v___x_1385_; 
lean_inc(v_toPure_1372_);
lean_dec_ref(v_newBody_1370_);
lean_dec_ref(v_newDomain_1369_);
lean_dec_ref(v_inst_1367_);
lean_dec_ref(v_inst_1366_);
v___x_1385_ = lean_apply_2(v_toPure_1372_, lean_box(0), v_e_1368_);
return v___x_1385_;
}
}
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec_ref(v_newBody_1370_);
lean_dec_ref(v_newDomain_1369_);
lean_dec_ref(v_e_1368_);
lean_dec_ref(v_inst_1366_);
v___x_1386_ = l_Lean_instInhabitedExpr;
v___x_1387_ = l_instInhabitedOfMonad___redArg(v_inst_1367_, v___x_1386_);
v___x_1388_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1389_ = l_panic___redArg(v___x_1387_, v___x_1388_);
lean_dec(v___x_1387_);
return v___x_1389_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1392_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__1));
v___x_1393_ = lean_unsigned_to_nat(27u);
v___x_1394_ = lean_unsigned_to_nat(167u);
v___x_1395_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__0));
v___x_1396_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1397_ = l_mkPanicMessageWithDecl(v___x_1396_, v___x_1395_, v___x_1394_, v___x_1393_, v___x_1392_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21___redArg(lean_object* v_inst_1398_, lean_object* v_inst_1399_, lean_object* v_e_1400_, lean_object* v_newDomain_1401_, lean_object* v_newBody_1402_){
_start:
{
if (lean_obj_tag(v_e_1400_) == 6)
{
lean_object* v_toApplicative_1403_; lean_object* v_toPure_1404_; lean_object* v_binderName_1405_; lean_object* v_binderType_1406_; lean_object* v_body_1407_; uint8_t v_binderInfo_1408_; size_t v___x_1409_; size_t v___x_1410_; uint8_t v___x_1411_; 
v_toApplicative_1403_ = lean_ctor_get(v_inst_1399_, 0);
v_toPure_1404_ = lean_ctor_get(v_toApplicative_1403_, 1);
v_binderName_1405_ = lean_ctor_get(v_e_1400_, 0);
v_binderType_1406_ = lean_ctor_get(v_e_1400_, 1);
v_body_1407_ = lean_ctor_get(v_e_1400_, 2);
v_binderInfo_1408_ = lean_ctor_get_uint8(v_e_1400_, sizeof(void*)*3 + 8);
v___x_1409_ = lean_ptr_addr(v_binderType_1406_);
v___x_1410_ = lean_ptr_addr(v_newDomain_1401_);
v___x_1411_ = lean_usize_dec_eq(v___x_1409_, v___x_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; 
lean_inc(v_binderName_1405_);
lean_dec_ref_known(v_e_1400_, 3);
v___x_1412_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1398_, v_inst_1399_, v_binderName_1405_, v_binderInfo_1408_, v_newDomain_1401_, v_newBody_1402_);
return v___x_1412_;
}
else
{
size_t v___x_1413_; size_t v___x_1414_; uint8_t v___x_1415_; 
v___x_1413_ = lean_ptr_addr(v_body_1407_);
v___x_1414_ = lean_ptr_addr(v_newBody_1402_);
v___x_1415_ = lean_usize_dec_eq(v___x_1413_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; 
lean_inc(v_binderName_1405_);
lean_dec_ref_known(v_e_1400_, 3);
v___x_1416_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1398_, v_inst_1399_, v_binderName_1405_, v_binderInfo_1408_, v_newDomain_1401_, v_newBody_1402_);
return v___x_1416_;
}
else
{
lean_object* v___x_1417_; 
lean_inc(v_toPure_1404_);
lean_dec_ref(v_newBody_1402_);
lean_dec_ref(v_newDomain_1401_);
lean_dec_ref(v_inst_1399_);
lean_dec_ref(v_inst_1398_);
v___x_1417_ = lean_apply_2(v_toPure_1404_, lean_box(0), v_e_1400_);
return v___x_1417_;
}
}
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_dec_ref(v_newBody_1402_);
lean_dec_ref(v_newDomain_1401_);
lean_dec_ref(v_e_1400_);
lean_dec_ref(v_inst_1398_);
v___x_1418_ = l_Lean_instInhabitedExpr;
v___x_1419_ = l_instInhabitedOfMonad___redArg(v_inst_1399_, v___x_1418_);
v___x_1420_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1421_ = l_panic___redArg(v___x_1419_, v___x_1420_);
lean_dec(v___x_1419_);
return v___x_1421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21(lean_object* v_m_1422_, lean_object* v_inst_1423_, lean_object* v_inst_1424_, lean_object* v_e_1425_, lean_object* v_newDomain_1426_, lean_object* v_newBody_1427_){
_start:
{
if (lean_obj_tag(v_e_1425_) == 6)
{
lean_object* v_toApplicative_1428_; lean_object* v_toPure_1429_; lean_object* v_binderName_1430_; lean_object* v_binderType_1431_; lean_object* v_body_1432_; uint8_t v_binderInfo_1433_; size_t v___x_1434_; size_t v___x_1435_; uint8_t v___x_1436_; 
v_toApplicative_1428_ = lean_ctor_get(v_inst_1424_, 0);
v_toPure_1429_ = lean_ctor_get(v_toApplicative_1428_, 1);
v_binderName_1430_ = lean_ctor_get(v_e_1425_, 0);
v_binderType_1431_ = lean_ctor_get(v_e_1425_, 1);
v_body_1432_ = lean_ctor_get(v_e_1425_, 2);
v_binderInfo_1433_ = lean_ctor_get_uint8(v_e_1425_, sizeof(void*)*3 + 8);
v___x_1434_ = lean_ptr_addr(v_binderType_1431_);
v___x_1435_ = lean_ptr_addr(v_newDomain_1426_);
v___x_1436_ = lean_usize_dec_eq(v___x_1434_, v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; 
lean_inc(v_binderName_1430_);
lean_dec_ref_known(v_e_1425_, 3);
v___x_1437_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1423_, v_inst_1424_, v_binderName_1430_, v_binderInfo_1433_, v_newDomain_1426_, v_newBody_1427_);
return v___x_1437_;
}
else
{
size_t v___x_1438_; size_t v___x_1439_; uint8_t v___x_1440_; 
v___x_1438_ = lean_ptr_addr(v_body_1432_);
v___x_1439_ = lean_ptr_addr(v_newBody_1427_);
v___x_1440_ = lean_usize_dec_eq(v___x_1438_, v___x_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; 
lean_inc(v_binderName_1430_);
lean_dec_ref_known(v_e_1425_, 3);
v___x_1441_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1423_, v_inst_1424_, v_binderName_1430_, v_binderInfo_1433_, v_newDomain_1426_, v_newBody_1427_);
return v___x_1441_;
}
else
{
lean_object* v___x_1442_; 
lean_inc(v_toPure_1429_);
lean_dec_ref(v_newBody_1427_);
lean_dec_ref(v_newDomain_1426_);
lean_dec_ref(v_inst_1424_);
lean_dec_ref(v_inst_1423_);
v___x_1442_ = lean_apply_2(v_toPure_1429_, lean_box(0), v_e_1425_);
return v___x_1442_;
}
}
}
else
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec_ref(v_newBody_1427_);
lean_dec_ref(v_newDomain_1426_);
lean_dec_ref(v_e_1425_);
lean_dec_ref(v_inst_1423_);
v___x_1443_ = l_Lean_instInhabitedExpr;
v___x_1444_ = l_instInhabitedOfMonad___redArg(v_inst_1424_, v___x_1443_);
v___x_1445_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1446_ = l_panic___redArg(v___x_1444_, v___x_1445_);
lean_dec(v___x_1444_);
return v___x_1446_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1449_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__1));
v___x_1450_ = lean_unsigned_to_nat(34u);
v___x_1451_ = lean_unsigned_to_nat(174u);
v___x_1452_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__0));
v___x_1453_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1454_ = l_mkPanicMessageWithDecl(v___x_1453_, v___x_1452_, v___x_1451_, v___x_1450_, v___x_1449_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21___redArg(lean_object* v_inst_1455_, lean_object* v_inst_1456_, lean_object* v_e_1457_, lean_object* v_newType_1458_, lean_object* v_newVal_1459_, lean_object* v_newBody_1460_){
_start:
{
if (lean_obj_tag(v_e_1457_) == 8)
{
lean_object* v_toApplicative_1461_; lean_object* v_toPure_1462_; lean_object* v_declName_1463_; lean_object* v_type_1464_; lean_object* v_value_1465_; lean_object* v_body_1466_; uint8_t v_nondep_1467_; size_t v___x_1468_; size_t v___x_1469_; uint8_t v___x_1470_; 
v_toApplicative_1461_ = lean_ctor_get(v_inst_1456_, 0);
v_toPure_1462_ = lean_ctor_get(v_toApplicative_1461_, 1);
v_declName_1463_ = lean_ctor_get(v_e_1457_, 0);
v_type_1464_ = lean_ctor_get(v_e_1457_, 1);
v_value_1465_ = lean_ctor_get(v_e_1457_, 2);
v_body_1466_ = lean_ctor_get(v_e_1457_, 3);
v_nondep_1467_ = lean_ctor_get_uint8(v_e_1457_, sizeof(void*)*4 + 8);
v___x_1468_ = lean_ptr_addr(v_type_1464_);
v___x_1469_ = lean_ptr_addr(v_newType_1458_);
v___x_1470_ = lean_usize_dec_eq(v___x_1468_, v___x_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; 
lean_inc(v_declName_1463_);
lean_dec_ref_known(v_e_1457_, 4);
v___x_1471_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1455_, v_inst_1456_, v_declName_1463_, v_newType_1458_, v_newVal_1459_, v_newBody_1460_, v_nondep_1467_);
return v___x_1471_;
}
else
{
size_t v___x_1472_; size_t v___x_1473_; uint8_t v___x_1474_; 
v___x_1472_ = lean_ptr_addr(v_value_1465_);
v___x_1473_ = lean_ptr_addr(v_newVal_1459_);
v___x_1474_ = lean_usize_dec_eq(v___x_1472_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; 
lean_inc(v_declName_1463_);
lean_dec_ref_known(v_e_1457_, 4);
v___x_1475_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1455_, v_inst_1456_, v_declName_1463_, v_newType_1458_, v_newVal_1459_, v_newBody_1460_, v_nondep_1467_);
return v___x_1475_;
}
else
{
size_t v___x_1476_; size_t v___x_1477_; uint8_t v___x_1478_; 
v___x_1476_ = lean_ptr_addr(v_body_1466_);
v___x_1477_ = lean_ptr_addr(v_newBody_1460_);
v___x_1478_ = lean_usize_dec_eq(v___x_1476_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; 
lean_inc(v_declName_1463_);
lean_dec_ref_known(v_e_1457_, 4);
v___x_1479_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1455_, v_inst_1456_, v_declName_1463_, v_newType_1458_, v_newVal_1459_, v_newBody_1460_, v_nondep_1467_);
return v___x_1479_;
}
else
{
lean_object* v___x_1480_; 
lean_inc(v_toPure_1462_);
lean_dec_ref(v_newBody_1460_);
lean_dec_ref(v_newVal_1459_);
lean_dec_ref(v_newType_1458_);
lean_dec_ref(v_inst_1456_);
lean_dec_ref(v_inst_1455_);
v___x_1480_ = lean_apply_2(v_toPure_1462_, lean_box(0), v_e_1457_);
return v___x_1480_;
}
}
}
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec_ref(v_newBody_1460_);
lean_dec_ref(v_newVal_1459_);
lean_dec_ref(v_newType_1458_);
lean_dec_ref(v_e_1457_);
lean_dec_ref(v_inst_1455_);
v___x_1481_ = l_Lean_instInhabitedExpr;
v___x_1482_ = l_instInhabitedOfMonad___redArg(v_inst_1456_, v___x_1481_);
v___x_1483_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1484_ = l_panic___redArg(v___x_1482_, v___x_1483_);
lean_dec(v___x_1482_);
return v___x_1484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21(lean_object* v_m_1485_, lean_object* v_inst_1486_, lean_object* v_inst_1487_, lean_object* v_e_1488_, lean_object* v_newType_1489_, lean_object* v_newVal_1490_, lean_object* v_newBody_1491_){
_start:
{
if (lean_obj_tag(v_e_1488_) == 8)
{
lean_object* v_toApplicative_1492_; lean_object* v_toPure_1493_; lean_object* v_declName_1494_; lean_object* v_type_1495_; lean_object* v_value_1496_; lean_object* v_body_1497_; uint8_t v_nondep_1498_; size_t v___x_1499_; size_t v___x_1500_; uint8_t v___x_1501_; 
v_toApplicative_1492_ = lean_ctor_get(v_inst_1487_, 0);
v_toPure_1493_ = lean_ctor_get(v_toApplicative_1492_, 1);
v_declName_1494_ = lean_ctor_get(v_e_1488_, 0);
v_type_1495_ = lean_ctor_get(v_e_1488_, 1);
v_value_1496_ = lean_ctor_get(v_e_1488_, 2);
v_body_1497_ = lean_ctor_get(v_e_1488_, 3);
v_nondep_1498_ = lean_ctor_get_uint8(v_e_1488_, sizeof(void*)*4 + 8);
v___x_1499_ = lean_ptr_addr(v_type_1495_);
v___x_1500_ = lean_ptr_addr(v_newType_1489_);
v___x_1501_ = lean_usize_dec_eq(v___x_1499_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; 
lean_inc(v_declName_1494_);
lean_dec_ref_known(v_e_1488_, 4);
v___x_1502_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1486_, v_inst_1487_, v_declName_1494_, v_newType_1489_, v_newVal_1490_, v_newBody_1491_, v_nondep_1498_);
return v___x_1502_;
}
else
{
size_t v___x_1503_; size_t v___x_1504_; uint8_t v___x_1505_; 
v___x_1503_ = lean_ptr_addr(v_value_1496_);
v___x_1504_ = lean_ptr_addr(v_newVal_1490_);
v___x_1505_ = lean_usize_dec_eq(v___x_1503_, v___x_1504_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; 
lean_inc(v_declName_1494_);
lean_dec_ref_known(v_e_1488_, 4);
v___x_1506_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1486_, v_inst_1487_, v_declName_1494_, v_newType_1489_, v_newVal_1490_, v_newBody_1491_, v_nondep_1498_);
return v___x_1506_;
}
else
{
size_t v___x_1507_; size_t v___x_1508_; uint8_t v___x_1509_; 
v___x_1507_ = lean_ptr_addr(v_body_1497_);
v___x_1508_ = lean_ptr_addr(v_newBody_1491_);
v___x_1509_ = lean_usize_dec_eq(v___x_1507_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; 
lean_inc(v_declName_1494_);
lean_dec_ref_known(v_e_1488_, 4);
v___x_1510_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1486_, v_inst_1487_, v_declName_1494_, v_newType_1489_, v_newVal_1490_, v_newBody_1491_, v_nondep_1498_);
return v___x_1510_;
}
else
{
lean_object* v___x_1511_; 
lean_inc(v_toPure_1493_);
lean_dec_ref(v_newBody_1491_);
lean_dec_ref(v_newVal_1490_);
lean_dec_ref(v_newType_1489_);
lean_dec_ref(v_inst_1487_);
lean_dec_ref(v_inst_1486_);
v___x_1511_ = lean_apply_2(v_toPure_1493_, lean_box(0), v_e_1488_);
return v___x_1511_;
}
}
}
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec_ref(v_newBody_1491_);
lean_dec_ref(v_newVal_1490_);
lean_dec_ref(v_newType_1489_);
lean_dec_ref(v_e_1488_);
lean_dec_ref(v_inst_1486_);
v___x_1512_ = l_Lean_instInhabitedExpr;
v___x_1513_ = l_instInhabitedOfMonad___redArg(v_inst_1487_, v___x_1512_);
v___x_1514_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1515_ = l_panic___redArg(v___x_1513_, v___x_1514_);
lean_dec(v___x_1513_);
return v___x_1515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0(lean_object* v_inst_1516_, lean_object* v_inst_1517_, lean_object* v_a_u2082_1518_, lean_object* v_____do__lift_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1516_, v_inst_1517_, v_____do__lift_1519_, v_a_u2082_1518_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_f_1523_, lean_object* v_a_u2081_1524_, lean_object* v_a_u2082_1525_){
_start:
{
lean_object* v_toBind_1526_; lean_object* v___f_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_toBind_1526_ = lean_ctor_get(v_inst_1522_, 1);
lean_inc(v_toBind_1526_);
lean_inc_ref(v_inst_1522_);
lean_inc_ref(v_inst_1521_);
v___f_1527_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1527_, 0, v_inst_1521_);
lean_closure_set(v___f_1527_, 1, v_inst_1522_);
lean_closure_set(v___f_1527_, 2, v_a_u2082_1525_);
v___x_1528_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1521_, v_inst_1522_, v_f_1523_, v_a_u2081_1524_);
v___x_1529_ = lean_apply_4(v_toBind_1526_, lean_box(0), lean_box(0), v___x_1528_, v___f_1527_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082(lean_object* v_m_1530_, lean_object* v_inst_1531_, lean_object* v_inst_1532_, lean_object* v_f_1533_, lean_object* v_a_u2081_1534_, lean_object* v_a_u2082_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1531_, v_inst_1532_, v_f_1533_, v_a_u2081_1534_, v_a_u2082_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0(lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_a_u2083_1539_, lean_object* v_____do__lift_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1537_, v_inst_1538_, v_____do__lift_1540_, v_a_u2083_1539_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v_f_1544_, lean_object* v_a_u2081_1545_, lean_object* v_a_u2082_1546_, lean_object* v_a_u2083_1547_){
_start:
{
lean_object* v_toBind_1548_; lean_object* v___f_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v_toBind_1548_ = lean_ctor_get(v_inst_1543_, 1);
lean_inc(v_toBind_1548_);
lean_inc_ref(v_inst_1543_);
lean_inc_ref(v_inst_1542_);
v___f_1549_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1549_, 0, v_inst_1542_);
lean_closure_set(v___f_1549_, 1, v_inst_1543_);
lean_closure_set(v___f_1549_, 2, v_a_u2083_1547_);
v___x_1550_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1542_, v_inst_1543_, v_f_1544_, v_a_u2081_1545_, v_a_u2082_1546_);
v___x_1551_ = lean_apply_4(v_toBind_1548_, lean_box(0), lean_box(0), v___x_1550_, v___f_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083(lean_object* v_m_1552_, lean_object* v_inst_1553_, lean_object* v_inst_1554_, lean_object* v_f_1555_, lean_object* v_a_u2081_1556_, lean_object* v_a_u2082_1557_, lean_object* v_a_u2083_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1553_, v_inst_1554_, v_f_1555_, v_a_u2081_1556_, v_a_u2082_1557_, v_a_u2083_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0(lean_object* v_inst_1560_, lean_object* v_inst_1561_, lean_object* v_a_u2084_1562_, lean_object* v_____do__lift_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1560_, v_inst_1561_, v_____do__lift_1563_, v_a_u2084_1562_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(lean_object* v_inst_1565_, lean_object* v_inst_1566_, lean_object* v_f_1567_, lean_object* v_a_u2081_1568_, lean_object* v_a_u2082_1569_, lean_object* v_a_u2083_1570_, lean_object* v_a_u2084_1571_){
_start:
{
lean_object* v_toBind_1572_; lean_object* v___f_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v_toBind_1572_ = lean_ctor_get(v_inst_1566_, 1);
lean_inc(v_toBind_1572_);
lean_inc_ref(v_inst_1566_);
lean_inc_ref(v_inst_1565_);
v___f_1573_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1573_, 0, v_inst_1565_);
lean_closure_set(v___f_1573_, 1, v_inst_1566_);
lean_closure_set(v___f_1573_, 2, v_a_u2084_1571_);
v___x_1574_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1565_, v_inst_1566_, v_f_1567_, v_a_u2081_1568_, v_a_u2082_1569_, v_a_u2083_1570_);
v___x_1575_ = lean_apply_4(v_toBind_1572_, lean_box(0), lean_box(0), v___x_1574_, v___f_1573_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084(lean_object* v_m_1576_, lean_object* v_inst_1577_, lean_object* v_inst_1578_, lean_object* v_f_1579_, lean_object* v_a_u2081_1580_, lean_object* v_a_u2082_1581_, lean_object* v_a_u2083_1582_, lean_object* v_a_u2084_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1577_, v_inst_1578_, v_f_1579_, v_a_u2081_1580_, v_a_u2082_1581_, v_a_u2083_1582_, v_a_u2084_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0(lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_a_u2085_1587_, lean_object* v_____do__lift_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1585_, v_inst_1586_, v_____do__lift_1588_, v_a_u2085_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_f_1592_, lean_object* v_a_u2081_1593_, lean_object* v_a_u2082_1594_, lean_object* v_a_u2083_1595_, lean_object* v_a_u2084_1596_, lean_object* v_a_u2085_1597_){
_start:
{
lean_object* v_toBind_1598_; lean_object* v___f_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_toBind_1598_ = lean_ctor_get(v_inst_1591_, 1);
lean_inc(v_toBind_1598_);
lean_inc_ref(v_inst_1591_);
lean_inc_ref(v_inst_1590_);
v___f_1599_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1599_, 0, v_inst_1590_);
lean_closure_set(v___f_1599_, 1, v_inst_1591_);
lean_closure_set(v___f_1599_, 2, v_a_u2085_1597_);
v___x_1600_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1590_, v_inst_1591_, v_f_1592_, v_a_u2081_1593_, v_a_u2082_1594_, v_a_u2083_1595_, v_a_u2084_1596_);
v___x_1601_ = lean_apply_4(v_toBind_1598_, lean_box(0), lean_box(0), v___x_1600_, v___f_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085(lean_object* v_m_1602_, lean_object* v_inst_1603_, lean_object* v_inst_1604_, lean_object* v_f_1605_, lean_object* v_a_u2081_1606_, lean_object* v_a_u2082_1607_, lean_object* v_a_u2083_1608_, lean_object* v_a_u2084_1609_, lean_object* v_a_u2085_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1603_, v_inst_1604_, v_f_1605_, v_a_u2081_1606_, v_a_u2082_1607_, v_a_u2083_1608_, v_a_u2084_1609_, v_a_u2085_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0(lean_object* v_inst_1612_, lean_object* v_inst_1613_, lean_object* v_a_u2086_1614_, lean_object* v_____do__lift_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1612_, v_inst_1613_, v_____do__lift_1615_, v_a_u2086_1614_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(lean_object* v_inst_1617_, lean_object* v_inst_1618_, lean_object* v_f_1619_, lean_object* v_a_u2081_1620_, lean_object* v_a_u2082_1621_, lean_object* v_a_u2083_1622_, lean_object* v_a_u2084_1623_, lean_object* v_a_u2085_1624_, lean_object* v_a_u2086_1625_){
_start:
{
lean_object* v_toBind_1626_; lean_object* v___f_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_toBind_1626_ = lean_ctor_get(v_inst_1618_, 1);
lean_inc(v_toBind_1626_);
lean_inc_ref(v_inst_1618_);
lean_inc_ref(v_inst_1617_);
v___f_1627_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1627_, 0, v_inst_1617_);
lean_closure_set(v___f_1627_, 1, v_inst_1618_);
lean_closure_set(v___f_1627_, 2, v_a_u2086_1625_);
v___x_1628_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1617_, v_inst_1618_, v_f_1619_, v_a_u2081_1620_, v_a_u2082_1621_, v_a_u2083_1622_, v_a_u2084_1623_, v_a_u2085_1624_);
v___x_1629_ = lean_apply_4(v_toBind_1626_, lean_box(0), lean_box(0), v___x_1628_, v___f_1627_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086(lean_object* v_m_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_f_1633_, lean_object* v_a_u2081_1634_, lean_object* v_a_u2082_1635_, lean_object* v_a_u2083_1636_, lean_object* v_a_u2084_1637_, lean_object* v_a_u2085_1638_, lean_object* v_a_u2086_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1631_, v_inst_1632_, v_f_1633_, v_a_u2081_1634_, v_a_u2082_1635_, v_a_u2083_1636_, v_a_u2084_1637_, v_a_u2085_1638_, v_a_u2086_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0(lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_a_u2087_1643_, lean_object* v_____do__lift_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1641_, v_inst_1642_, v_____do__lift_1644_, v_a_u2087_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(lean_object* v_inst_1646_, lean_object* v_inst_1647_, lean_object* v_f_1648_, lean_object* v_a_u2081_1649_, lean_object* v_a_u2082_1650_, lean_object* v_a_u2083_1651_, lean_object* v_a_u2084_1652_, lean_object* v_a_u2085_1653_, lean_object* v_a_u2086_1654_, lean_object* v_a_u2087_1655_){
_start:
{
lean_object* v_toBind_1656_; lean_object* v___f_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v_toBind_1656_ = lean_ctor_get(v_inst_1647_, 1);
lean_inc(v_toBind_1656_);
lean_inc_ref(v_inst_1647_);
lean_inc_ref(v_inst_1646_);
v___f_1657_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1657_, 0, v_inst_1646_);
lean_closure_set(v___f_1657_, 1, v_inst_1647_);
lean_closure_set(v___f_1657_, 2, v_a_u2087_1655_);
v___x_1658_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1646_, v_inst_1647_, v_f_1648_, v_a_u2081_1649_, v_a_u2082_1650_, v_a_u2083_1651_, v_a_u2084_1652_, v_a_u2085_1653_, v_a_u2086_1654_);
v___x_1659_ = lean_apply_4(v_toBind_1656_, lean_box(0), lean_box(0), v___x_1658_, v___f_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087(lean_object* v_m_1660_, lean_object* v_inst_1661_, lean_object* v_inst_1662_, lean_object* v_f_1663_, lean_object* v_a_u2081_1664_, lean_object* v_a_u2082_1665_, lean_object* v_a_u2083_1666_, lean_object* v_a_u2084_1667_, lean_object* v_a_u2085_1668_, lean_object* v_a_u2086_1669_, lean_object* v_a_u2087_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1661_, v_inst_1662_, v_f_1663_, v_a_u2081_1664_, v_a_u2082_1665_, v_a_u2083_1666_, v_a_u2084_1667_, v_a_u2085_1668_, v_a_u2086_1669_, v_a_u2087_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0(lean_object* v_inst_1672_, lean_object* v_inst_1673_, lean_object* v_a_u2088_1674_, lean_object* v_____do__lift_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1672_, v_inst_1673_, v_____do__lift_1675_, v_a_u2088_1674_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(lean_object* v_inst_1677_, lean_object* v_inst_1678_, lean_object* v_f_1679_, lean_object* v_a_u2081_1680_, lean_object* v_a_u2082_1681_, lean_object* v_a_u2083_1682_, lean_object* v_a_u2084_1683_, lean_object* v_a_u2085_1684_, lean_object* v_a_u2086_1685_, lean_object* v_a_u2087_1686_, lean_object* v_a_u2088_1687_){
_start:
{
lean_object* v_toBind_1688_; lean_object* v___f_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v_toBind_1688_ = lean_ctor_get(v_inst_1678_, 1);
lean_inc(v_toBind_1688_);
lean_inc_ref(v_inst_1678_);
lean_inc_ref(v_inst_1677_);
v___f_1689_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1689_, 0, v_inst_1677_);
lean_closure_set(v___f_1689_, 1, v_inst_1678_);
lean_closure_set(v___f_1689_, 2, v_a_u2088_1687_);
v___x_1690_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1677_, v_inst_1678_, v_f_1679_, v_a_u2081_1680_, v_a_u2082_1681_, v_a_u2083_1682_, v_a_u2084_1683_, v_a_u2085_1684_, v_a_u2086_1685_, v_a_u2087_1686_);
v___x_1691_ = lean_apply_4(v_toBind_1688_, lean_box(0), lean_box(0), v___x_1690_, v___f_1689_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088(lean_object* v_m_1692_, lean_object* v_inst_1693_, lean_object* v_inst_1694_, lean_object* v_f_1695_, lean_object* v_a_u2081_1696_, lean_object* v_a_u2082_1697_, lean_object* v_a_u2083_1698_, lean_object* v_a_u2084_1699_, lean_object* v_a_u2085_1700_, lean_object* v_a_u2086_1701_, lean_object* v_a_u2087_1702_, lean_object* v_a_u2088_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1693_, v_inst_1694_, v_f_1695_, v_a_u2081_1696_, v_a_u2082_1697_, v_a_u2083_1698_, v_a_u2084_1699_, v_a_u2085_1700_, v_a_u2086_1701_, v_a_u2087_1702_, v_a_u2088_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0(lean_object* v_inst_1705_, lean_object* v_inst_1706_, lean_object* v_a_u2089_1707_, lean_object* v_____do__lift_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1705_, v_inst_1706_, v_____do__lift_1708_, v_a_u2089_1707_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_f_1712_, lean_object* v_a_u2081_1713_, lean_object* v_a_u2082_1714_, lean_object* v_a_u2083_1715_, lean_object* v_a_u2084_1716_, lean_object* v_a_u2085_1717_, lean_object* v_a_u2086_1718_, lean_object* v_a_u2087_1719_, lean_object* v_a_u2088_1720_, lean_object* v_a_u2089_1721_){
_start:
{
lean_object* v_toBind_1722_; lean_object* v___f_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v_toBind_1722_ = lean_ctor_get(v_inst_1711_, 1);
lean_inc(v_toBind_1722_);
lean_inc_ref(v_inst_1711_);
lean_inc_ref(v_inst_1710_);
v___f_1723_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1723_, 0, v_inst_1710_);
lean_closure_set(v___f_1723_, 1, v_inst_1711_);
lean_closure_set(v___f_1723_, 2, v_a_u2089_1721_);
v___x_1724_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1710_, v_inst_1711_, v_f_1712_, v_a_u2081_1713_, v_a_u2082_1714_, v_a_u2083_1715_, v_a_u2084_1716_, v_a_u2085_1717_, v_a_u2086_1718_, v_a_u2087_1719_, v_a_u2088_1720_);
v___x_1725_ = lean_apply_4(v_toBind_1722_, lean_box(0), lean_box(0), v___x_1724_, v___f_1723_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089(lean_object* v_m_1726_, lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_f_1729_, lean_object* v_a_u2081_1730_, lean_object* v_a_u2082_1731_, lean_object* v_a_u2083_1732_, lean_object* v_a_u2084_1733_, lean_object* v_a_u2085_1734_, lean_object* v_a_u2086_1735_, lean_object* v_a_u2087_1736_, lean_object* v_a_u2088_1737_, lean_object* v_a_u2089_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1727_, v_inst_1728_, v_f_1729_, v_a_u2081_1730_, v_a_u2082_1731_, v_a_u2083_1732_, v_a_u2084_1733_, v_a_u2085_1734_, v_a_u2086_1735_, v_a_u2087_1736_, v_a_u2088_1737_, v_a_u2089_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0(lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_a_u2081_u2080_1742_, lean_object* v_____do__lift_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1740_, v_inst_1741_, v_____do__lift_1743_, v_a_u2081_u2080_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(lean_object* v_inst_1745_, lean_object* v_inst_1746_, lean_object* v_f_1747_, lean_object* v_a_u2081_1748_, lean_object* v_a_u2082_1749_, lean_object* v_a_u2083_1750_, lean_object* v_a_u2084_1751_, lean_object* v_a_u2085_1752_, lean_object* v_a_u2086_1753_, lean_object* v_a_u2087_1754_, lean_object* v_a_u2088_1755_, lean_object* v_a_u2089_1756_, lean_object* v_a_u2081_u2080_1757_){
_start:
{
lean_object* v_toBind_1758_; lean_object* v___f_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_toBind_1758_ = lean_ctor_get(v_inst_1746_, 1);
lean_inc(v_toBind_1758_);
lean_inc_ref(v_inst_1746_);
lean_inc_ref(v_inst_1745_);
v___f_1759_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1759_, 0, v_inst_1745_);
lean_closure_set(v___f_1759_, 1, v_inst_1746_);
lean_closure_set(v___f_1759_, 2, v_a_u2081_u2080_1757_);
v___x_1760_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1745_, v_inst_1746_, v_f_1747_, v_a_u2081_1748_, v_a_u2082_1749_, v_a_u2083_1750_, v_a_u2084_1751_, v_a_u2085_1752_, v_a_u2086_1753_, v_a_u2087_1754_, v_a_u2088_1755_, v_a_u2089_1756_);
v___x_1761_ = lean_apply_4(v_toBind_1758_, lean_box(0), lean_box(0), v___x_1760_, v___f_1759_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080(lean_object* v_m_1762_, lean_object* v_inst_1763_, lean_object* v_inst_1764_, lean_object* v_f_1765_, lean_object* v_a_u2081_1766_, lean_object* v_a_u2082_1767_, lean_object* v_a_u2083_1768_, lean_object* v_a_u2084_1769_, lean_object* v_a_u2085_1770_, lean_object* v_a_u2086_1771_, lean_object* v_a_u2087_1772_, lean_object* v_a_u2088_1773_, lean_object* v_a_u2089_1774_, lean_object* v_a_u2081_u2080_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1763_, v_inst_1764_, v_f_1765_, v_a_u2081_1766_, v_a_u2082_1767_, v_a_u2083_1768_, v_a_u2084_1769_, v_a_u2085_1770_, v_a_u2086_1771_, v_a_u2087_1772_, v_a_u2088_1773_, v_a_u2089_1774_, v_a_u2081_u2080_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0(lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_a_u2081_u2081_1779_, lean_object* v_____do__lift_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1777_, v_inst_1778_, v_____do__lift_1780_, v_a_u2081_u2081_1779_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(lean_object* v_inst_1782_, lean_object* v_inst_1783_, lean_object* v_f_1784_, lean_object* v_a_u2081_1785_, lean_object* v_a_u2082_1786_, lean_object* v_a_u2083_1787_, lean_object* v_a_u2084_1788_, lean_object* v_a_u2085_1789_, lean_object* v_a_u2086_1790_, lean_object* v_a_u2087_1791_, lean_object* v_a_u2088_1792_, lean_object* v_a_u2089_1793_, lean_object* v_a_u2081_u2080_1794_, lean_object* v_a_u2081_u2081_1795_){
_start:
{
lean_object* v_toBind_1796_; lean_object* v___f_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v_toBind_1796_ = lean_ctor_get(v_inst_1783_, 1);
lean_inc(v_toBind_1796_);
lean_inc_ref(v_inst_1783_);
lean_inc_ref(v_inst_1782_);
v___f_1797_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1797_, 0, v_inst_1782_);
lean_closure_set(v___f_1797_, 1, v_inst_1783_);
lean_closure_set(v___f_1797_, 2, v_a_u2081_u2081_1795_);
v___x_1798_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1782_, v_inst_1783_, v_f_1784_, v_a_u2081_1785_, v_a_u2082_1786_, v_a_u2083_1787_, v_a_u2084_1788_, v_a_u2085_1789_, v_a_u2086_1790_, v_a_u2087_1791_, v_a_u2088_1792_, v_a_u2089_1793_, v_a_u2081_u2080_1794_);
v___x_1799_ = lean_apply_4(v_toBind_1796_, lean_box(0), lean_box(0), v___x_1798_, v___f_1797_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081(lean_object* v_m_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_f_1803_, lean_object* v_a_u2081_1804_, lean_object* v_a_u2082_1805_, lean_object* v_a_u2083_1806_, lean_object* v_a_u2084_1807_, lean_object* v_a_u2085_1808_, lean_object* v_a_u2086_1809_, lean_object* v_a_u2087_1810_, lean_object* v_a_u2088_1811_, lean_object* v_a_u2089_1812_, lean_object* v_a_u2081_u2080_1813_, lean_object* v_a_u2081_u2081_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(v_inst_1801_, v_inst_1802_, v_f_1803_, v_a_u2081_1804_, v_a_u2082_1805_, v_a_u2083_1806_, v_a_u2084_1807_, v_a_u2085_1808_, v_a_u2086_1809_, v_a_u2087_1810_, v_a_u2088_1811_, v_a_u2089_1812_, v_a_u2081_u2080_1813_, v_a_u2081_u2081_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed(lean_object* v_i_1816_, lean_object* v_inst_1817_, lean_object* v_inst_1818_, lean_object* v_args_1819_, lean_object* v_endIdx_1820_, lean_object* v_____do__lift_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(v_i_1816_, v_inst_1817_, v_inst_1818_, v_args_1819_, v_endIdx_1820_, v_____do__lift_1821_);
lean_dec(v_i_1816_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(lean_object* v_inst_1823_, lean_object* v_inst_1824_, lean_object* v_args_1825_, lean_object* v_endIdx_1826_, lean_object* v_b_1827_, lean_object* v_i_1828_){
_start:
{
lean_object* v_toApplicative_1829_; lean_object* v_toBind_1830_; lean_object* v_toPure_1831_; uint8_t v___x_1832_; 
v_toApplicative_1829_ = lean_ctor_get(v_inst_1824_, 0);
v_toBind_1830_ = lean_ctor_get(v_inst_1824_, 1);
lean_inc(v_toBind_1830_);
v_toPure_1831_ = lean_ctor_get(v_toApplicative_1829_, 1);
v___x_1832_ = lean_nat_dec_le(v_endIdx_1826_, v_i_1828_);
if (v___x_1832_ == 0)
{
lean_object* v___f_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_inc_ref(v_args_1825_);
lean_inc_ref(v_inst_1824_);
lean_inc_ref(v_inst_1823_);
lean_inc(v_i_1828_);
v___f_1833_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1833_, 0, v_i_1828_);
lean_closure_set(v___f_1833_, 1, v_inst_1823_);
lean_closure_set(v___f_1833_, 2, v_inst_1824_);
lean_closure_set(v___f_1833_, 3, v_args_1825_);
lean_closure_set(v___f_1833_, 4, v_endIdx_1826_);
v___x_1834_ = l_Lean_instInhabitedExpr;
v___x_1835_ = lean_array_get(v___x_1834_, v_args_1825_, v_i_1828_);
lean_dec(v_i_1828_);
lean_dec_ref(v_args_1825_);
v___x_1836_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1823_, v_inst_1824_, v_b_1827_, v___x_1835_);
v___x_1837_ = lean_apply_4(v_toBind_1830_, lean_box(0), lean_box(0), v___x_1836_, v___f_1833_);
return v___x_1837_;
}
else
{
lean_object* v___x_1838_; 
lean_inc(v_toPure_1831_);
lean_dec(v_toBind_1830_);
lean_dec(v_i_1828_);
lean_dec(v_endIdx_1826_);
lean_dec_ref(v_args_1825_);
lean_dec_ref(v_inst_1824_);
lean_dec_ref(v_inst_1823_);
v___x_1838_ = lean_apply_2(v_toPure_1831_, lean_box(0), v_b_1827_);
return v___x_1838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(lean_object* v_i_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_args_1842_, lean_object* v_endIdx_1843_, lean_object* v_____do__lift_1844_){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = lean_unsigned_to_nat(1u);
v___x_1846_ = lean_nat_add(v_i_1839_, v___x_1845_);
v___x_1847_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1840_, v_inst_1841_, v_args_1842_, v_endIdx_1843_, v_____do__lift_1844_, v___x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go(lean_object* v_m_1848_, lean_object* v_inst_1849_, lean_object* v_inst_1850_, lean_object* v_args_1851_, lean_object* v_endIdx_1852_, lean_object* v_b_1853_, lean_object* v_i_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1849_, v_inst_1850_, v_args_1851_, v_endIdx_1852_, v_b_1853_, v_i_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS___redArg(lean_object* v_inst_1856_, lean_object* v_inst_1857_, lean_object* v_f_1858_, lean_object* v_beginIdx_1859_, lean_object* v_endIdx_1860_, lean_object* v_args_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1856_, v_inst_1857_, v_args_1861_, v_endIdx_1860_, v_f_1858_, v_beginIdx_1859_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS(lean_object* v_m_1863_, lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_f_1866_, lean_object* v_beginIdx_1867_, lean_object* v_endIdx_1868_, lean_object* v_args_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1864_, v_inst_1865_, v_args_1869_, v_endIdx_1868_, v_f_1866_, v_beginIdx_1867_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___redArg(lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_f_1873_, lean_object* v_args_1874_){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_unsigned_to_nat(0u);
v___x_1876_ = lean_array_get_size(v_args_1874_);
v___x_1877_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1871_, v_inst_1872_, v_args_1874_, v___x_1876_, v_f_1873_, v___x_1875_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS(lean_object* v_m_1878_, lean_object* v_inst_1879_, lean_object* v_inst_1880_, lean_object* v_f_1881_, lean_object* v_args_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_Meta_Sym_Internal_mkAppNS___redArg(v_inst_1879_, v_inst_1880_, v_f_1881_, v_args_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed(lean_object* v_inst_1884_, lean_object* v_inst_1885_, lean_object* v_revArgs_1886_, lean_object* v_start_1887_, lean_object* v_i_1888_, lean_object* v_____do__lift_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(v_inst_1884_, v_inst_1885_, v_revArgs_1886_, v_start_1887_, v_i_1888_, v_____do__lift_1889_);
lean_dec(v_i_1888_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(lean_object* v_inst_1891_, lean_object* v_inst_1892_, lean_object* v_revArgs_1893_, lean_object* v_start_1894_, lean_object* v_b_1895_, lean_object* v_i_1896_){
_start:
{
lean_object* v_toApplicative_1897_; lean_object* v_toBind_1898_; lean_object* v_toPure_1899_; uint8_t v___x_1900_; 
v_toApplicative_1897_ = lean_ctor_get(v_inst_1892_, 0);
v_toBind_1898_ = lean_ctor_get(v_inst_1892_, 1);
lean_inc(v_toBind_1898_);
v_toPure_1899_ = lean_ctor_get(v_toApplicative_1897_, 1);
v___x_1900_ = lean_nat_dec_le(v_i_1896_, v_start_1894_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v_i_1903_; lean_object* v___f_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1901_ = l_Lean_instInhabitedExpr;
v___x_1902_ = lean_unsigned_to_nat(1u);
v_i_1903_ = lean_nat_sub(v_i_1896_, v___x_1902_);
lean_inc(v_i_1903_);
lean_inc_ref(v_revArgs_1893_);
lean_inc_ref(v_inst_1892_);
lean_inc_ref(v_inst_1891_);
v___f_1904_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1904_, 0, v_inst_1891_);
lean_closure_set(v___f_1904_, 1, v_inst_1892_);
lean_closure_set(v___f_1904_, 2, v_revArgs_1893_);
lean_closure_set(v___f_1904_, 3, v_start_1894_);
lean_closure_set(v___f_1904_, 4, v_i_1903_);
v___x_1905_ = lean_array_get(v___x_1901_, v_revArgs_1893_, v_i_1903_);
lean_dec(v_i_1903_);
lean_dec_ref(v_revArgs_1893_);
v___x_1906_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1891_, v_inst_1892_, v_b_1895_, v___x_1905_);
v___x_1907_ = lean_apply_4(v_toBind_1898_, lean_box(0), lean_box(0), v___x_1906_, v___f_1904_);
return v___x_1907_;
}
else
{
lean_object* v___x_1908_; 
lean_inc(v_toPure_1899_);
lean_dec(v_toBind_1898_);
lean_dec(v_start_1894_);
lean_dec_ref(v_revArgs_1893_);
lean_dec_ref(v_inst_1892_);
lean_dec_ref(v_inst_1891_);
v___x_1908_ = lean_apply_2(v_toPure_1899_, lean_box(0), v_b_1895_);
return v___x_1908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(lean_object* v_inst_1909_, lean_object* v_inst_1910_, lean_object* v_revArgs_1911_, lean_object* v_start_1912_, lean_object* v_i_1913_, lean_object* v_____do__lift_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1909_, v_inst_1910_, v_revArgs_1911_, v_start_1912_, v_____do__lift_1914_, v_i_1913_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___boxed(lean_object* v_inst_1916_, lean_object* v_inst_1917_, lean_object* v_revArgs_1918_, lean_object* v_start_1919_, lean_object* v_b_1920_, lean_object* v_i_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1916_, v_inst_1917_, v_revArgs_1918_, v_start_1919_, v_b_1920_, v_i_1921_);
lean_dec(v_i_1921_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(lean_object* v_m_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_revArgs_1926_, lean_object* v_start_1927_, lean_object* v_b_1928_, lean_object* v_i_1929_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1924_, v_inst_1925_, v_revArgs_1926_, v_start_1927_, v_b_1928_, v_i_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___boxed(lean_object* v_m_1931_, lean_object* v_inst_1932_, lean_object* v_inst_1933_, lean_object* v_revArgs_1934_, lean_object* v_start_1935_, lean_object* v_b_1936_, lean_object* v_i_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(v_m_1931_, v_inst_1932_, v_inst_1933_, v_revArgs_1934_, v_start_1935_, v_b_1936_, v_i_1937_);
lean_dec(v_i_1937_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(lean_object* v_inst_1939_, lean_object* v_inst_1940_, lean_object* v_f_1941_, lean_object* v_beginIdx_1942_, lean_object* v_endIdx_1943_, lean_object* v_revArgs_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1939_, v_inst_1940_, v_revArgs_1944_, v_beginIdx_1942_, v_f_1941_, v_endIdx_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg___boxed(lean_object* v_inst_1946_, lean_object* v_inst_1947_, lean_object* v_f_1948_, lean_object* v_beginIdx_1949_, lean_object* v_endIdx_1950_, lean_object* v_revArgs_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(v_inst_1946_, v_inst_1947_, v_f_1948_, v_beginIdx_1949_, v_endIdx_1950_, v_revArgs_1951_);
lean_dec(v_endIdx_1950_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS(lean_object* v_m_1953_, lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v_f_1956_, lean_object* v_beginIdx_1957_, lean_object* v_endIdx_1958_, lean_object* v_revArgs_1959_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1954_, v_inst_1955_, v_revArgs_1959_, v_beginIdx_1957_, v_f_1956_, v_endIdx_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___boxed(lean_object* v_m_1961_, lean_object* v_inst_1962_, lean_object* v_inst_1963_, lean_object* v_f_1964_, lean_object* v_beginIdx_1965_, lean_object* v_endIdx_1966_, lean_object* v_revArgs_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS(v_m_1961_, v_inst_1962_, v_inst_1963_, v_f_1964_, v_beginIdx_1965_, v_endIdx_1966_, v_revArgs_1967_);
lean_dec(v_endIdx_1966_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_f_1971_, lean_object* v_revArgs_1972_){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1973_ = lean_unsigned_to_nat(0u);
v___x_1974_ = lean_array_get_size(v_revArgs_1972_);
v___x_1975_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1969_, v_inst_1970_, v_revArgs_1972_, v___x_1973_, v_f_1971_, v___x_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS(lean_object* v_m_1976_, lean_object* v_inst_1977_, lean_object* v_inst_1978_, lean_object* v_f_1979_, lean_object* v_revArgs_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(v_inst_1977_, v_inst_1978_, v_f_1979_, v_revArgs_1980_);
return v___x_1981_;
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
