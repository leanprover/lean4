// Lean compiler output
// Module: Lean.Meta.Tactic.Intro
// Imports: public import Lean.Meta.Tactic.Util
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
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getUnusedName(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMCtxMetaM;
extern lean_object* l_Lean_Core_instMonadNameGeneratorCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshFVarId___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "introN"};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 179, 69, 171, 232, 145, 98, 43)}};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "There are no additional binders or `let` bindings in the goal to introduce"};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1;
static const lean_closure_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8;
static const lean_closure_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__1_value),((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__8_value),((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__3_value),((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__4_value),((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__5_value),((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__6_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__9_value),((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__7_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_fvarId_x21___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "hygienic"};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(106, 53, 183, 57, 182, 192, 14, 150)}};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "make sure tactics are hygienic"};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 82, 89, 96, 183, 68, 254, 125)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(179, 184, 241, 48, 181, 222, 216, 48)}};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tactic_hygienic;
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_introNCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_introNCore___closed__0 = (const lean_object*)&l_Lean_Meta_introNCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_introN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_introN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_introNP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_introNP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_intro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1P(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1P___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_intro1___00__lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "intro1_: expected arrow type\n"};
static const lean_object* l_Lean_MVarId_intro1___00__lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_intro1___00__lam__0___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_intro1___00__lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_intro1___00__lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1__(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getIntrosSize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getIntrosSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0(lean_object* v_mvarId_1_, lean_object* v_type_2_, lean_object* v_fvars_3_, uint8_t v_isZero_4_, lean_object* v___x_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_11_; 
lean_inc(v_mvarId_1_);
v___x_11_ = l_Lean_MVarId_getTag(v_mvarId_1_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v_a_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_a_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc(v_a_12_);
lean_dec_ref_known(v___x_11_, 1);
v___x_13_ = l_Lean_Expr_headBeta(v_type_2_);
v___x_14_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_13_, v_a_12_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v_a_15_; uint8_t v___x_16_; uint8_t v___x_17_; lean_object* v___x_18_; 
v_a_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc_n(v_a_15_, 2);
lean_dec_ref_known(v___x_14_, 1);
v___x_16_ = 0;
v___x_17_ = 1;
v___x_18_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3_, v_a_15_, v___x_16_, v_isZero_4_, v___x_16_, v_isZero_4_, v___x_17_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_1533__overap_20_; lean_object* v___x_21_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_a_19_);
lean_dec_ref_known(v___x_18_, 1);
v___x_1533__overap_20_ = l_Lean_MVarId_assign___redArg(v___x_5_, v_mvarId_1_, v_a_19_);
v___x_21_ = lean_apply_5(v___x_1533__overap_20_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_30_; 
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_30_ == 0)
{
lean_object* v_unused_31_; 
v_unused_31_ = lean_ctor_get(v___x_21_, 0);
lean_dec(v_unused_31_);
v___x_23_ = v___x_21_;
v_isShared_24_ = v_isSharedCheck_30_;
goto v_resetjp_22_;
}
else
{
lean_dec(v___x_21_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_30_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_25_ = l_Lean_Expr_mvarId_x21(v_a_15_);
lean_dec(v_a_15_);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v_fvars_3_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 0, v___x_26_);
v___x_28_ = v___x_23_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
else
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
lean_dec(v_a_15_);
lean_dec_ref(v_fvars_3_);
v_a_32_ = lean_ctor_get(v___x_21_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v___x_21_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_21_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_a_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
else
{
lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_47_; 
lean_dec(v_a_15_);
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
lean_dec(v___y_7_);
lean_dec_ref(v___y_6_);
lean_dec_ref(v___x_5_);
lean_dec_ref(v_fvars_3_);
lean_dec(v_mvarId_1_);
v_a_40_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_47_ == 0)
{
v___x_42_ = v___x_18_;
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_dec(v___x_18_);
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
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_a_40_);
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
else
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_55_; 
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
lean_dec(v___y_7_);
lean_dec_ref(v___y_6_);
lean_dec_ref(v___x_5_);
lean_dec_ref(v_fvars_3_);
lean_dec(v_mvarId_1_);
v_a_48_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_55_ == 0)
{
v___x_50_ = v___x_14_;
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_14_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_53_; 
if (v_isShared_51_ == 0)
{
v___x_53_ = v___x_50_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_a_48_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
}
else
{
lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_63_; 
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
lean_dec(v___y_7_);
lean_dec_ref(v___y_6_);
lean_dec_ref(v___x_5_);
lean_dec_ref(v_fvars_3_);
lean_dec_ref(v_type_2_);
lean_dec(v_mvarId_1_);
v_a_56_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_63_ == 0)
{
v___x_58_ = v___x_11_;
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_dec(v___x_11_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_a_56_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0___boxed(lean_object* v_mvarId_64_, lean_object* v_type_65_, lean_object* v_fvars_66_, lean_object* v_isZero_67_, lean_object* v___x_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
uint8_t v_isZero_boxed_74_; lean_object* v_res_75_; 
v_isZero_boxed_74_ = lean_unbox(v_isZero_67_);
v_res_75_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0(v_mvarId_64_, v_type_65_, v_fvars_66_, v_isZero_boxed_74_, v___x_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
return v_res_75_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__2));
v___x_81_ = l_Lean_stringToMessageData(v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3);
v___x_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
return v___x_83_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0(void){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_instMonadEIO(lean_box(0));
return v___x_84_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0);
v___x_86_ = l_StateRefT_x27_instMonad___redArg(v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = l_Lean_Core_instMonadNameGeneratorCoreM;
v___x_93_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__7));
v___x_94_ = l_Lean_monadNameGeneratorLift___redArg(v___x_93_, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9(void){
_start:
{
lean_object* v___x_96_; lean_object* v___f_97_; lean_object* v___x_98_; 
v___x_96_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8);
v___f_97_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__6));
v___x_98_ = l_Lean_monadNameGeneratorLift___redArg(v___f_97_, v___x_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___boxed(lean_object* v___x_99_, lean_object* v___x_100_, lean_object* v_type_101_, lean_object* v_mvarId_102_, lean_object* v_n_103_, lean_object* v_mkName_104_, lean_object* v_lctx_105_, lean_object* v_fvars_106_, lean_object* v___x_107_, lean_object* v_s_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1(v___x_99_, v___x_100_, v_type_101_, v_mvarId_102_, v_n_103_, v_mkName_104_, v_lctx_105_, v_fvars_106_, v___x_107_, v_s_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
lean_dec(v_n_103_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(lean_object* v_mvarId_115_, lean_object* v_mkName_116_, lean_object* v_i_117_, lean_object* v_lctx_118_, lean_object* v_fvars_119_, lean_object* v_j_120_, lean_object* v_s_121_, lean_object* v_type_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v___x_128_; lean_object* v_toApplicative_129_; lean_object* v_toFunctor_130_; lean_object* v_toSeq_131_; lean_object* v_toSeqLeft_132_; lean_object* v_toSeqRight_133_; lean_object* v___f_134_; lean_object* v___f_135_; lean_object* v___f_136_; lean_object* v___f_137_; lean_object* v___x_138_; lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v_toApplicative_147_; lean_object* v_toFunctor_148_; lean_object* v_toSeq_149_; lean_object* v_toSeqLeft_150_; lean_object* v_toSeqRight_151_; lean_object* v___f_152_; lean_object* v___f_153_; lean_object* v___x_154_; lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v_toApplicative_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_282_; 
v___x_128_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
v_toApplicative_129_ = lean_ctor_get(v___x_128_, 0);
v_toFunctor_130_ = lean_ctor_get(v_toApplicative_129_, 0);
v_toSeq_131_ = lean_ctor_get(v_toApplicative_129_, 2);
v_toSeqLeft_132_ = lean_ctor_get(v_toApplicative_129_, 3);
v_toSeqRight_133_ = lean_ctor_get(v_toApplicative_129_, 4);
v___f_134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2));
v___f_135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_130_, 2);
v___f_136_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_136_, 0, v_toFunctor_130_);
v___f_137_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_137_, 0, v_toFunctor_130_);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v___f_136_);
lean_ctor_set(v___x_138_, 1, v___f_137_);
lean_inc(v_toSeqRight_133_);
v___f_139_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_139_, 0, v_toSeqRight_133_);
lean_inc(v_toSeqLeft_132_);
v___f_140_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_140_, 0, v_toSeqLeft_132_);
lean_inc(v_toSeq_131_);
v___f_141_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_141_, 0, v_toSeq_131_);
v___x_142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_142_, 0, v___x_138_);
lean_ctor_set(v___x_142_, 1, v___f_134_);
lean_ctor_set(v___x_142_, 2, v___f_141_);
lean_ctor_set(v___x_142_, 3, v___f_140_);
lean_ctor_set(v___x_142_, 4, v___f_139_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___f_135_);
v___x_144_ = l_StateRefT_x27_instMonad___redArg(v___x_143_);
v___x_145_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_145_, 0, lean_box(0));
lean_closure_set(v___x_145_, 1, lean_box(0));
lean_closure_set(v___x_145_, 2, v___x_144_);
v___x_146_ = l_instMonadControlTOfPure___redArg(v___x_145_);
v_toApplicative_147_ = lean_ctor_get(v___x_128_, 0);
v_toFunctor_148_ = lean_ctor_get(v_toApplicative_147_, 0);
v_toSeq_149_ = lean_ctor_get(v_toApplicative_147_, 2);
v_toSeqLeft_150_ = lean_ctor_get(v_toApplicative_147_, 3);
v_toSeqRight_151_ = lean_ctor_get(v_toApplicative_147_, 4);
lean_inc_ref_n(v_toFunctor_148_, 2);
v___f_152_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_152_, 0, v_toFunctor_148_);
v___f_153_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_153_, 0, v_toFunctor_148_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v___f_152_);
lean_ctor_set(v___x_154_, 1, v___f_153_);
lean_inc(v_toSeqRight_151_);
v___f_155_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_155_, 0, v_toSeqRight_151_);
lean_inc(v_toSeqLeft_150_);
v___f_156_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_156_, 0, v_toSeqLeft_150_);
lean_inc(v_toSeq_149_);
v___f_157_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_157_, 0, v_toSeq_149_);
v___x_158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_158_, 0, v___x_154_);
lean_ctor_set(v___x_158_, 1, v___f_134_);
lean_ctor_set(v___x_158_, 2, v___f_157_);
lean_ctor_set(v___x_158_, 3, v___f_156_);
lean_ctor_set(v___x_158_, 4, v___f_155_);
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___f_135_);
v___x_160_ = l_StateRefT_x27_instMonad___redArg(v___x_159_);
v_toApplicative_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; 
v_unused_283_ = lean_ctor_get(v___x_160_, 1);
lean_dec(v_unused_283_);
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_282_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_toApplicative_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_282_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v_toFunctor_165_; lean_object* v_toSeq_166_; lean_object* v_toSeqLeft_167_; lean_object* v_toSeqRight_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_280_; 
v_toFunctor_165_ = lean_ctor_get(v_toApplicative_161_, 0);
v_toSeq_166_ = lean_ctor_get(v_toApplicative_161_, 2);
v_toSeqLeft_167_ = lean_ctor_get(v_toApplicative_161_, 3);
v_toSeqRight_168_ = lean_ctor_get(v_toApplicative_161_, 4);
v_isSharedCheck_280_ = !lean_is_exclusive(v_toApplicative_161_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; 
v_unused_281_ = lean_ctor_get(v_toApplicative_161_, 1);
lean_dec(v_unused_281_);
v___x_170_ = v_toApplicative_161_;
v_isShared_171_ = v_isSharedCheck_280_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_toSeqRight_168_);
lean_inc(v_toSeqLeft_167_);
lean_inc(v_toSeq_166_);
lean_inc(v_toFunctor_165_);
lean_dec(v_toApplicative_161_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_280_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___x_176_; lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___x_181_; 
v___f_172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4));
v___f_173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5));
lean_inc_ref(v_toFunctor_165_);
v___f_174_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_174_, 0, v_toFunctor_165_);
v___f_175_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_175_, 0, v_toFunctor_165_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___f_174_);
lean_ctor_set(v___x_176_, 1, v___f_175_);
v___f_177_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_177_, 0, v_toSeqRight_168_);
v___f_178_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_178_, 0, v_toSeqLeft_167_);
v___f_179_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_179_, 0, v_toSeq_166_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 4, v___f_177_);
lean_ctor_set(v___x_170_, 3, v___f_178_);
lean_ctor_set(v___x_170_, 2, v___f_179_);
lean_ctor_set(v___x_170_, 1, v___f_172_);
lean_ctor_set(v___x_170_, 0, v___x_176_);
v___x_181_ = v___x_170_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___f_172_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v___f_179_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v___f_178_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v___f_177_);
v___x_181_ = v_reuseFailAlloc_279_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_183_; 
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 1, v___f_173_);
lean_ctor_set(v___x_163_, 0, v___x_181_);
v___x_183_ = v___x_163_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___f_173_);
v___x_183_ = v_reuseFailAlloc_278_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_zero_186_; uint8_t v_isZero_187_; 
v___x_184_ = l_Lean_Meta_instMonadMCtxMetaM;
v___x_185_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9);
v_zero_186_ = lean_unsigned_to_nat(0u);
v_isZero_187_ = lean_nat_dec_eq(v_i_117_, v_zero_186_);
if (v_isZero_187_ == 1)
{
lean_object* v___x_188_; lean_object* v_type_189_; lean_object* v___x_190_; lean_object* v___f_191_; lean_object* v___x_192_; lean_object* v___x_1284__overap_193_; lean_object* v___x_194_; 
lean_dec(v_s_121_);
lean_dec(v_i_117_);
lean_dec_ref(v_mkName_116_);
v___x_188_ = lean_array_get_size(v_fvars_119_);
v_type_189_ = lean_expr_instantiate_rev_range(v_type_122_, v_j_120_, v___x_188_, v_fvars_119_);
lean_dec_ref(v_type_122_);
v___x_190_ = lean_box(v_isZero_187_);
lean_inc_ref(v_fvars_119_);
v___f_191_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_191_, 0, v_mvarId_115_);
lean_closure_set(v___f_191_, 1, v_type_189_);
lean_closure_set(v___f_191_, 2, v_fvars_119_);
lean_closure_set(v___f_191_, 3, v___x_190_);
lean_closure_set(v___f_191_, 4, v___x_184_);
lean_inc_ref(v___x_183_);
lean_inc_ref(v___x_146_);
v___x_192_ = l_Lean_Meta_withNewLocalInstances___redArg(v___x_146_, v___x_183_, v_fvars_119_, v_j_120_, v___f_191_);
v___x_1284__overap_193_ = l_Lean_Meta_withLCtx_x27___redArg(v___x_146_, v___x_183_, v_lctx_118_, v___x_192_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
v___x_194_ = lean_apply_5(v___x_1284__overap_193_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
return v___x_194_;
}
else
{
lean_object* v_one_195_; lean_object* v_n_196_; 
v_one_195_ = lean_unsigned_to_nat(1u);
v_n_196_ = lean_nat_sub(v_i_117_, v_one_195_);
lean_dec(v_i_117_);
switch(lean_obj_tag(v_type_122_))
{
case 8:
{
lean_object* v_declName_197_; lean_object* v_type_198_; lean_object* v_value_199_; lean_object* v_body_200_; lean_object* v___x_1314__overap_201_; lean_object* v___x_202_; 
lean_dec_ref(v___x_146_);
v_declName_197_ = lean_ctor_get(v_type_122_, 0);
lean_inc(v_declName_197_);
v_type_198_ = lean_ctor_get(v_type_122_, 1);
lean_inc_ref(v_type_198_);
v_value_199_ = lean_ctor_get(v_type_122_, 2);
lean_inc_ref(v_value_199_);
v_body_200_ = lean_ctor_get(v_type_122_, 3);
lean_inc_ref(v_body_200_);
lean_dec_ref_known(v_type_122_, 4);
v___x_1314__overap_201_ = l_Lean_mkFreshFVarId___redArg(v___x_183_, v___x_185_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
v___x_202_ = lean_apply_5(v___x_1314__overap_201_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; uint8_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_202_, 1);
v___x_204_ = 1;
v___x_205_ = lean_box(v___x_204_);
lean_inc_ref(v_mkName_116_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
lean_inc_ref(v_lctx_118_);
v___x_206_ = lean_apply_9(v_mkName_116_, v_lctx_118_, v_declName_197_, v___x_205_, v_s_121_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v_fst_208_; lean_object* v_snd_209_; lean_object* v___x_210_; lean_object* v_type_211_; lean_object* v_type_212_; lean_object* v_val_213_; uint8_t v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref_known(v___x_206_, 1);
v_fst_208_ = lean_ctor_get(v_a_207_, 0);
lean_inc(v_fst_208_);
v_snd_209_ = lean_ctor_get(v_a_207_, 1);
lean_inc(v_snd_209_);
lean_dec(v_a_207_);
v___x_210_ = lean_array_get_size(v_fvars_119_);
v_type_211_ = lean_expr_instantiate_rev_range(v_type_198_, v_j_120_, v___x_210_, v_fvars_119_);
lean_dec_ref(v_type_198_);
v_type_212_ = l_Lean_Expr_headBeta(v_type_211_);
v_val_213_ = lean_expr_instantiate_rev_range(v_value_199_, v_j_120_, v___x_210_, v_fvars_119_);
lean_dec_ref(v_value_199_);
v___x_214_ = 0;
lean_inc(v_a_203_);
v___x_215_ = l_Lean_LocalContext_mkLetDecl(v_lctx_118_, v_a_203_, v_fst_208_, v_type_212_, v_val_213_, v_isZero_187_, v___x_214_);
v___x_216_ = l_Lean_mkFVar(v_a_203_);
v___x_217_ = lean_array_push(v_fvars_119_, v___x_216_);
v_i_117_ = v_n_196_;
v_lctx_118_ = v___x_215_;
v_fvars_119_ = v___x_217_;
v_s_121_ = v_snd_209_;
v_type_122_ = v_body_200_;
goto _start;
}
else
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
lean_dec(v_a_203_);
lean_dec_ref(v_body_200_);
lean_dec_ref(v_value_199_);
lean_dec_ref(v_type_198_);
lean_dec(v_n_196_);
lean_dec(v_j_120_);
lean_dec_ref(v_fvars_119_);
lean_dec_ref(v_lctx_118_);
lean_dec_ref(v_mkName_116_);
lean_dec(v_mvarId_115_);
v_a_219_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_206_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_206_);
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
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_219_);
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
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec_ref(v_body_200_);
lean_dec_ref(v_value_199_);
lean_dec_ref(v_type_198_);
lean_dec(v_declName_197_);
lean_dec(v_n_196_);
lean_dec(v_s_121_);
lean_dec(v_j_120_);
lean_dec_ref(v_fvars_119_);
lean_dec_ref(v_lctx_118_);
lean_dec_ref(v_mkName_116_);
lean_dec(v_mvarId_115_);
v_a_227_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_202_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_202_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
case 7:
{
lean_object* v_binderName_235_; lean_object* v_binderType_236_; lean_object* v_body_237_; uint8_t v_binderInfo_238_; lean_object* v___x_1363__overap_239_; lean_object* v___x_240_; 
lean_dec_ref(v___x_146_);
v_binderName_235_ = lean_ctor_get(v_type_122_, 0);
lean_inc(v_binderName_235_);
v_binderType_236_ = lean_ctor_get(v_type_122_, 1);
lean_inc_ref(v_binderType_236_);
v_body_237_ = lean_ctor_get(v_type_122_, 2);
lean_inc_ref(v_body_237_);
v_binderInfo_238_ = lean_ctor_get_uint8(v_type_122_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_122_, 3);
v___x_1363__overap_239_ = l_Lean_mkFreshFVarId___redArg(v___x_183_, v___x_185_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
v___x_240_ = lean_apply_5(v___x_1363__overap_239_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_241_);
lean_dec_ref_known(v___x_240_, 1);
v___x_242_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_238_);
v___x_243_ = lean_box(v___x_242_);
lean_inc_ref(v_mkName_116_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
lean_inc_ref(v_lctx_118_);
v___x_244_ = lean_apply_9(v_mkName_116_, v_lctx_118_, v_binderName_235_, v___x_243_, v_s_121_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v_fst_246_; lean_object* v_snd_247_; lean_object* v___x_248_; lean_object* v_type_249_; lean_object* v_type_250_; uint8_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref_known(v___x_244_, 1);
v_fst_246_ = lean_ctor_get(v_a_245_, 0);
lean_inc(v_fst_246_);
v_snd_247_ = lean_ctor_get(v_a_245_, 1);
lean_inc(v_snd_247_);
lean_dec(v_a_245_);
v___x_248_ = lean_array_get_size(v_fvars_119_);
v_type_249_ = lean_expr_instantiate_rev_range(v_binderType_236_, v_j_120_, v___x_248_, v_fvars_119_);
lean_dec_ref(v_binderType_236_);
v_type_250_ = l_Lean_Expr_headBeta(v_type_249_);
v___x_251_ = 0;
lean_inc(v_a_241_);
v___x_252_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_118_, v_a_241_, v_fst_246_, v_type_250_, v_binderInfo_238_, v___x_251_);
v___x_253_ = l_Lean_mkFVar(v_a_241_);
v___x_254_ = lean_array_push(v_fvars_119_, v___x_253_);
v_i_117_ = v_n_196_;
v_lctx_118_ = v___x_252_;
v_fvars_119_ = v___x_254_;
v_s_121_ = v_snd_247_;
v_type_122_ = v_body_237_;
goto _start;
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec(v_a_241_);
lean_dec_ref(v_body_237_);
lean_dec_ref(v_binderType_236_);
lean_dec(v_n_196_);
lean_dec(v_j_120_);
lean_dec_ref(v_fvars_119_);
lean_dec_ref(v_lctx_118_);
lean_dec_ref(v_mkName_116_);
lean_dec(v_mvarId_115_);
v_a_256_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_244_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_244_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec_ref(v_body_237_);
lean_dec_ref(v_binderType_236_);
lean_dec(v_binderName_235_);
lean_dec(v_n_196_);
lean_dec(v_s_121_);
lean_dec(v_j_120_);
lean_dec_ref(v_fvars_119_);
lean_dec_ref(v_lctx_118_);
lean_dec_ref(v_mkName_116_);
lean_dec(v_mvarId_115_);
v_a_264_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_240_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_240_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
default: 
{
lean_object* v___x_272_; lean_object* v_type_273_; lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___x_1437__overap_276_; lean_object* v___x_277_; 
v___x_272_ = lean_array_get_size(v_fvars_119_);
v_type_273_ = lean_expr_instantiate_rev_range(v_type_122_, v_j_120_, v___x_272_, v_fvars_119_);
lean_dec_ref(v_type_122_);
lean_inc_ref(v_fvars_119_);
lean_inc_ref(v_lctx_118_);
lean_inc_ref_n(v___x_183_, 2);
v___f_274_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___boxed), 15, 10);
lean_closure_set(v___f_274_, 0, v___x_183_);
lean_closure_set(v___f_274_, 1, v___x_184_);
lean_closure_set(v___f_274_, 2, v_type_273_);
lean_closure_set(v___f_274_, 3, v_mvarId_115_);
lean_closure_set(v___f_274_, 4, v_n_196_);
lean_closure_set(v___f_274_, 5, v_mkName_116_);
lean_closure_set(v___f_274_, 6, v_lctx_118_);
lean_closure_set(v___f_274_, 7, v_fvars_119_);
lean_closure_set(v___f_274_, 8, v___x_272_);
lean_closure_set(v___f_274_, 9, v_s_121_);
lean_inc_ref(v___x_146_);
v___x_275_ = l_Lean_Meta_withNewLocalInstances___redArg(v___x_146_, v___x_183_, v_fvars_119_, v_j_120_, v___f_274_);
v___x_1437__overap_276_ = l_Lean_Meta_withLCtx_x27___redArg(v___x_146_, v___x_183_, v_lctx_118_, v___x_275_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
v___x_277_ = lean_apply_5(v___x_1437__overap_276_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
return v___x_277_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1(lean_object* v___x_284_, lean_object* v___x_285_, lean_object* v_type_286_, lean_object* v_mvarId_287_, lean_object* v_n_288_, lean_object* v_mkName_289_, lean_object* v_lctx_290_, lean_object* v_fvars_291_, lean_object* v___x_292_, lean_object* v_s_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_1560__overap_299_; lean_object* v___x_300_; 
v___x_1560__overap_299_ = l_Lean_instantiateMVars___redArg(v___x_284_, v___x_285_, v_type_286_);
lean_inc(v___y_297_);
lean_inc_ref(v___y_296_);
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
v___x_300_ = lean_apply_5(v___x_1560__overap_299_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, lean_box(0));
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_302_; uint8_t v___y_304_; uint8_t v___x_325_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref_known(v___x_300_, 1);
v___x_302_ = l_Lean_Expr_cleanupAnnotations(v_a_301_);
v___x_325_ = l_Lean_Expr_isForall(v___x_302_);
if (v___x_325_ == 0)
{
uint8_t v___x_326_; 
v___x_326_ = l_Lean_Expr_isLet(v___x_302_);
v___y_304_ = v___x_326_;
goto v___jp_303_;
}
else
{
v___y_304_ = v___x_325_;
goto v___jp_303_;
}
v___jp_303_:
{
if (v___y_304_ == 0)
{
lean_object* v___x_305_; 
lean_inc(v___y_297_);
lean_inc_ref(v___y_296_);
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
v___x_305_ = lean_whnf(v___x_302_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; uint8_t v___x_307_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_306_);
lean_dec_ref_known(v___x_305_, 1);
v___x_307_ = l_Lean_Expr_isForall(v_a_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec(v_a_306_);
lean_dec(v_s_293_);
lean_dec(v___x_292_);
lean_dec_ref(v_fvars_291_);
lean_dec_ref(v_lctx_290_);
lean_dec_ref(v_mkName_289_);
v___x_308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
v___x_309_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4);
v___x_310_ = l_Lean_Meta_throwTacticEx___redArg(v___x_308_, v_mvarId_287_, v___x_309_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
return v___x_310_;
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_add(v_n_288_, v___x_311_);
v___x_313_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_287_, v_mkName_289_, v___x_312_, v_lctx_290_, v_fvars_291_, v___x_292_, v_s_293_, v_a_306_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
return v___x_313_;
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v_s_293_);
lean_dec(v___x_292_);
lean_dec_ref(v_fvars_291_);
lean_dec_ref(v_lctx_290_);
lean_dec_ref(v_mkName_289_);
lean_dec(v_mvarId_287_);
v_a_314_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_305_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_305_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_add(v_n_288_, v___x_322_);
v___x_324_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_287_, v_mkName_289_, v___x_323_, v_lctx_290_, v_fvars_291_, v___x_292_, v_s_293_, v___x_302_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
return v___x_324_;
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v_s_293_);
lean_dec(v___x_292_);
lean_dec_ref(v_fvars_291_);
lean_dec_ref(v_lctx_290_);
lean_dec_ref(v_mkName_289_);
lean_dec(v_mvarId_287_);
v_a_327_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_300_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_300_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___boxed(lean_object* v_mvarId_335_, lean_object* v_mkName_336_, lean_object* v_i_337_, lean_object* v_lctx_338_, lean_object* v_fvars_339_, lean_object* v_j_340_, lean_object* v_s_341_, lean_object* v_type_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_335_, v_mkName_336_, v_i_337_, v_lctx_338_, v_fvars_339_, v_j_340_, v_s_341_, v_type_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(lean_object* v_00_u03c3_349_, lean_object* v_mvarId_350_, lean_object* v_mkName_351_, lean_object* v_i_352_, lean_object* v_lctx_353_, lean_object* v_fvars_354_, lean_object* v_j_355_, lean_object* v_s_356_, lean_object* v_type_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_350_, v_mkName_351_, v_i_352_, v_lctx_353_, v_fvars_354_, v_j_355_, v_s_356_, v_type_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___boxed(lean_object* v_00_u03c3_364_, lean_object* v_mvarId_365_, lean_object* v_mkName_366_, lean_object* v_i_367_, lean_object* v_lctx_368_, lean_object* v_fvars_369_, lean_object* v_j_370_, lean_object* v_s_371_, lean_object* v_type_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(v_00_u03c3_364_, v_mvarId_365_, v_mkName_366_, v_i_367_, v_lctx_368_, v_fvars_369_, v_j_370_, v_s_371_, v_type_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0(lean_object* v_mvarId_400_, lean_object* v___x_401_, lean_object* v_mkName_402_, lean_object* v_n_403_, lean_object* v_s_404_, lean_object* v___f_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___x_411_; 
lean_inc(v_mvarId_400_);
v___x_411_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_400_, v___x_401_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v___x_412_; 
lean_dec_ref_known(v___x_411_, 1);
lean_inc(v_mvarId_400_);
v___x_412_ = l_Lean_MVarId_getType(v_mvarId_400_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v_lctx_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v_lctx_414_ = lean_ctor_get(v___y_406_, 2);
lean_inc_ref(v_lctx_414_);
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__0));
v___x_417_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_400_, v_mkName_402_, v_n_403_, v_lctx_414_, v___x_416_, v___x_415_, v_s_404_, v_a_413_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec_ref(v___y_406_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_438_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_438_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_438_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_438_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_fst_422_; lean_object* v_snd_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_437_; 
v_fst_422_ = lean_ctor_get(v_a_418_, 0);
v_snd_423_ = lean_ctor_get(v_a_418_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v_a_418_);
if (v_isSharedCheck_437_ == 0)
{
v___x_425_ = v_a_418_;
v_isShared_426_ = v_isSharedCheck_437_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_snd_423_);
lean_inc(v_fst_422_);
lean_dec(v_a_418_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_437_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; size_t v_sz_428_; size_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__10));
v_sz_428_ = lean_array_size(v_fst_422_);
v___x_429_ = ((size_t)0ULL);
v___x_430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_427_, v___f_405_, v_sz_428_, v___x_429_, v_fst_422_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_430_);
v___x_432_ = v___x_425_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_snd_423_);
v___x_432_ = v_reuseFailAlloc_436_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_434_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_432_);
v___x_434_ = v___x_420_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec_ref(v___f_405_);
v_a_439_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_417_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_417_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec_ref(v___y_406_);
lean_dec_ref(v___f_405_);
lean_dec(v_s_404_);
lean_dec(v_n_403_);
lean_dec_ref(v_mkName_402_);
lean_dec(v_mvarId_400_);
v_a_447_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_412_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_412_);
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
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
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
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec_ref(v___y_406_);
lean_dec_ref(v___f_405_);
lean_dec(v_s_404_);
lean_dec(v_n_403_);
lean_dec_ref(v_mkName_402_);
lean_dec(v_mvarId_400_);
v_a_455_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_411_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_411_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed(lean_object* v_mvarId_463_, lean_object* v___x_464_, lean_object* v_mkName_465_, lean_object* v_n_466_, lean_object* v_s_467_, lean_object* v___f_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0(v_mvarId_463_, v___x_464_, v_mkName_465_, v_n_466_, v_s_467_, v___f_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg(lean_object* v_mvarId_476_, lean_object* v_n_477_, lean_object* v_mkName_478_, lean_object* v_s_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_485_; lean_object* v_toApplicative_486_; lean_object* v_toFunctor_487_; lean_object* v_toSeq_488_; lean_object* v_toSeqLeft_489_; lean_object* v_toSeqRight_490_; lean_object* v___f_491_; lean_object* v___f_492_; lean_object* v___f_493_; lean_object* v___f_494_; lean_object* v___x_495_; lean_object* v___f_496_; lean_object* v___f_497_; lean_object* v___f_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v_toApplicative_504_; lean_object* v_toFunctor_505_; lean_object* v_toSeq_506_; lean_object* v_toSeqLeft_507_; lean_object* v_toSeqRight_508_; lean_object* v___f_509_; lean_object* v___f_510_; lean_object* v___x_511_; lean_object* v___f_512_; lean_object* v___f_513_; lean_object* v___f_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v_toApplicative_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_550_; 
v___x_485_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
v_toApplicative_486_ = lean_ctor_get(v___x_485_, 0);
v_toFunctor_487_ = lean_ctor_get(v_toApplicative_486_, 0);
v_toSeq_488_ = lean_ctor_get(v_toApplicative_486_, 2);
v_toSeqLeft_489_ = lean_ctor_get(v_toApplicative_486_, 3);
v_toSeqRight_490_ = lean_ctor_get(v_toApplicative_486_, 4);
v___f_491_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2));
v___f_492_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_487_, 2);
v___f_493_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_493_, 0, v_toFunctor_487_);
v___f_494_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_494_, 0, v_toFunctor_487_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___f_493_);
lean_ctor_set(v___x_495_, 1, v___f_494_);
lean_inc(v_toSeqRight_490_);
v___f_496_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_496_, 0, v_toSeqRight_490_);
lean_inc(v_toSeqLeft_489_);
v___f_497_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_497_, 0, v_toSeqLeft_489_);
lean_inc(v_toSeq_488_);
v___f_498_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_498_, 0, v_toSeq_488_);
v___x_499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_499_, 0, v___x_495_);
lean_ctor_set(v___x_499_, 1, v___f_491_);
lean_ctor_set(v___x_499_, 2, v___f_498_);
lean_ctor_set(v___x_499_, 3, v___f_497_);
lean_ctor_set(v___x_499_, 4, v___f_496_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v___f_492_);
v___x_501_ = l_StateRefT_x27_instMonad___redArg(v___x_500_);
v___x_502_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_502_, 0, lean_box(0));
lean_closure_set(v___x_502_, 1, lean_box(0));
lean_closure_set(v___x_502_, 2, v___x_501_);
v___x_503_ = l_instMonadControlTOfPure___redArg(v___x_502_);
v_toApplicative_504_ = lean_ctor_get(v___x_485_, 0);
v_toFunctor_505_ = lean_ctor_get(v_toApplicative_504_, 0);
v_toSeq_506_ = lean_ctor_get(v_toApplicative_504_, 2);
v_toSeqLeft_507_ = lean_ctor_get(v_toApplicative_504_, 3);
v_toSeqRight_508_ = lean_ctor_get(v_toApplicative_504_, 4);
lean_inc_ref_n(v_toFunctor_505_, 2);
v___f_509_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_509_, 0, v_toFunctor_505_);
v___f_510_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_510_, 0, v_toFunctor_505_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___f_509_);
lean_ctor_set(v___x_511_, 1, v___f_510_);
lean_inc(v_toSeqRight_508_);
v___f_512_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_512_, 0, v_toSeqRight_508_);
lean_inc(v_toSeqLeft_507_);
v___f_513_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_513_, 0, v_toSeqLeft_507_);
lean_inc(v_toSeq_506_);
v___f_514_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_514_, 0, v_toSeq_506_);
v___x_515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_515_, 0, v___x_511_);
lean_ctor_set(v___x_515_, 1, v___f_491_);
lean_ctor_set(v___x_515_, 2, v___f_514_);
lean_ctor_set(v___x_515_, 3, v___f_513_);
lean_ctor_set(v___x_515_, 4, v___f_512_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v___f_492_);
v___x_517_ = l_StateRefT_x27_instMonad___redArg(v___x_516_);
v_toApplicative_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v___x_517_, 1);
lean_dec(v_unused_551_);
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_550_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_toApplicative_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_550_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_toFunctor_522_; lean_object* v_toSeq_523_; lean_object* v_toSeqLeft_524_; lean_object* v_toSeqRight_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_548_; 
v_toFunctor_522_ = lean_ctor_get(v_toApplicative_518_, 0);
v_toSeq_523_ = lean_ctor_get(v_toApplicative_518_, 2);
v_toSeqLeft_524_ = lean_ctor_get(v_toApplicative_518_, 3);
v_toSeqRight_525_ = lean_ctor_get(v_toApplicative_518_, 4);
v_isSharedCheck_548_ = !lean_is_exclusive(v_toApplicative_518_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v_toApplicative_518_, 1);
lean_dec(v_unused_549_);
v___x_527_ = v_toApplicative_518_;
v_isShared_528_ = v_isSharedCheck_548_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_toSeqRight_525_);
lean_inc(v_toSeqLeft_524_);
lean_inc(v_toSeq_523_);
lean_inc(v_toFunctor_522_);
lean_dec(v_toApplicative_518_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_548_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___f_529_; lean_object* v___f_530_; lean_object* v___f_531_; lean_object* v___f_532_; lean_object* v___f_533_; lean_object* v___x_534_; lean_object* v___f_535_; lean_object* v___f_536_; lean_object* v___f_537_; lean_object* v___x_539_; 
v___f_529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0));
v___f_530_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4));
v___f_531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5));
lean_inc_ref(v_toFunctor_522_);
v___f_532_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_532_, 0, v_toFunctor_522_);
v___f_533_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_533_, 0, v_toFunctor_522_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v___f_532_);
lean_ctor_set(v___x_534_, 1, v___f_533_);
v___f_535_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_535_, 0, v_toSeqRight_525_);
v___f_536_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_536_, 0, v_toSeqLeft_524_);
v___f_537_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_537_, 0, v_toSeq_523_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 4, v___f_535_);
lean_ctor_set(v___x_527_, 3, v___f_536_);
lean_ctor_set(v___x_527_, 2, v___f_537_);
lean_ctor_set(v___x_527_, 1, v___f_530_);
lean_ctor_set(v___x_527_, 0, v___x_534_);
v___x_539_ = v___x_527_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___f_530_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v___f_537_);
lean_ctor_set(v_reuseFailAlloc_547_, 3, v___f_536_);
lean_ctor_set(v_reuseFailAlloc_547_, 4, v___f_535_);
v___x_539_ = v_reuseFailAlloc_547_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_541_; 
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 1, v___f_531_);
lean_ctor_set(v___x_520_, 0, v___x_539_);
v___x_541_ = v___x_520_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v___f_531_);
v___x_541_ = v_reuseFailAlloc_546_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___f_543_; lean_object* v___x_43__overap_544_; lean_object* v___x_545_; 
v___x_542_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
lean_inc(v_mvarId_476_);
v___f_543_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_543_, 0, v_mvarId_476_);
lean_closure_set(v___f_543_, 1, v___x_542_);
lean_closure_set(v___f_543_, 2, v_mkName_478_);
lean_closure_set(v___f_543_, 3, v_n_477_);
lean_closure_set(v___f_543_, 4, v_s_479_);
lean_closure_set(v___f_543_, 5, v___f_529_);
v___x_43__overap_544_ = l_Lean_MVarId_withContext___redArg(v___x_503_, v___x_541_, v_mvarId_476_, v___f_543_);
lean_inc(v_a_483_);
lean_inc_ref(v_a_482_);
lean_inc(v_a_481_);
lean_inc_ref(v_a_480_);
v___x_545_ = lean_apply_5(v___x_43__overap_544_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, lean_box(0));
return v___x_545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___boxed(lean_object* v_mvarId_552_, lean_object* v_n_553_, lean_object* v_mkName_554_, lean_object* v_s_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg(v_mvarId_552_, v_n_553_, v_mkName_554_, v_s_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(lean_object* v_00_u03c3_562_, lean_object* v_mvarId_563_, lean_object* v_n_564_, lean_object* v_mkName_565_, lean_object* v_s_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___x_572_; lean_object* v_toApplicative_573_; lean_object* v_toFunctor_574_; lean_object* v_toSeq_575_; lean_object* v_toSeqLeft_576_; lean_object* v_toSeqRight_577_; lean_object* v___f_578_; lean_object* v___f_579_; lean_object* v___f_580_; lean_object* v___f_581_; lean_object* v___x_582_; lean_object* v___f_583_; lean_object* v___f_584_; lean_object* v___f_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v_toApplicative_591_; lean_object* v_toFunctor_592_; lean_object* v_toSeq_593_; lean_object* v_toSeqLeft_594_; lean_object* v_toSeqRight_595_; lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___x_598_; lean_object* v___f_599_; lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v_toApplicative_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_637_; 
v___x_572_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
v_toApplicative_573_ = lean_ctor_get(v___x_572_, 0);
v_toFunctor_574_ = lean_ctor_get(v_toApplicative_573_, 0);
v_toSeq_575_ = lean_ctor_get(v_toApplicative_573_, 2);
v_toSeqLeft_576_ = lean_ctor_get(v_toApplicative_573_, 3);
v_toSeqRight_577_ = lean_ctor_get(v_toApplicative_573_, 4);
v___f_578_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2));
v___f_579_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_574_, 2);
v___f_580_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_580_, 0, v_toFunctor_574_);
v___f_581_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_581_, 0, v_toFunctor_574_);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v___f_580_);
lean_ctor_set(v___x_582_, 1, v___f_581_);
lean_inc(v_toSeqRight_577_);
v___f_583_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_583_, 0, v_toSeqRight_577_);
lean_inc(v_toSeqLeft_576_);
v___f_584_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_584_, 0, v_toSeqLeft_576_);
lean_inc(v_toSeq_575_);
v___f_585_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_585_, 0, v_toSeq_575_);
v___x_586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_586_, 0, v___x_582_);
lean_ctor_set(v___x_586_, 1, v___f_578_);
lean_ctor_set(v___x_586_, 2, v___f_585_);
lean_ctor_set(v___x_586_, 3, v___f_584_);
lean_ctor_set(v___x_586_, 4, v___f_583_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___f_579_);
v___x_588_ = l_StateRefT_x27_instMonad___redArg(v___x_587_);
v___x_589_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_589_, 0, lean_box(0));
lean_closure_set(v___x_589_, 1, lean_box(0));
lean_closure_set(v___x_589_, 2, v___x_588_);
v___x_590_ = l_instMonadControlTOfPure___redArg(v___x_589_);
v_toApplicative_591_ = lean_ctor_get(v___x_572_, 0);
v_toFunctor_592_ = lean_ctor_get(v_toApplicative_591_, 0);
v_toSeq_593_ = lean_ctor_get(v_toApplicative_591_, 2);
v_toSeqLeft_594_ = lean_ctor_get(v_toApplicative_591_, 3);
v_toSeqRight_595_ = lean_ctor_get(v_toApplicative_591_, 4);
lean_inc_ref_n(v_toFunctor_592_, 2);
v___f_596_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_596_, 0, v_toFunctor_592_);
v___f_597_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_597_, 0, v_toFunctor_592_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v___f_596_);
lean_ctor_set(v___x_598_, 1, v___f_597_);
lean_inc(v_toSeqRight_595_);
v___f_599_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_599_, 0, v_toSeqRight_595_);
lean_inc(v_toSeqLeft_594_);
v___f_600_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_600_, 0, v_toSeqLeft_594_);
lean_inc(v_toSeq_593_);
v___f_601_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_601_, 0, v_toSeq_593_);
v___x_602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_602_, 0, v___x_598_);
lean_ctor_set(v___x_602_, 1, v___f_578_);
lean_ctor_set(v___x_602_, 2, v___f_601_);
lean_ctor_set(v___x_602_, 3, v___f_600_);
lean_ctor_set(v___x_602_, 4, v___f_599_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v___f_579_);
v___x_604_ = l_StateRefT_x27_instMonad___redArg(v___x_603_);
v_toApplicative_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; 
v_unused_638_ = lean_ctor_get(v___x_604_, 1);
lean_dec(v_unused_638_);
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_637_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_toApplicative_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_637_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_toFunctor_609_; lean_object* v_toSeq_610_; lean_object* v_toSeqLeft_611_; lean_object* v_toSeqRight_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_635_; 
v_toFunctor_609_ = lean_ctor_get(v_toApplicative_605_, 0);
v_toSeq_610_ = lean_ctor_get(v_toApplicative_605_, 2);
v_toSeqLeft_611_ = lean_ctor_get(v_toApplicative_605_, 3);
v_toSeqRight_612_ = lean_ctor_get(v_toApplicative_605_, 4);
v_isSharedCheck_635_ = !lean_is_exclusive(v_toApplicative_605_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v_toApplicative_605_, 1);
lean_dec(v_unused_636_);
v___x_614_ = v_toApplicative_605_;
v_isShared_615_ = v_isSharedCheck_635_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_toSeqRight_612_);
lean_inc(v_toSeqLeft_611_);
lean_inc(v_toSeq_610_);
lean_inc(v_toFunctor_609_);
lean_dec(v_toApplicative_605_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_635_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___f_616_; lean_object* v___f_617_; lean_object* v___f_618_; lean_object* v___f_619_; lean_object* v___f_620_; lean_object* v___x_621_; lean_object* v___f_622_; lean_object* v___f_623_; lean_object* v___f_624_; lean_object* v___x_626_; 
v___f_616_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0));
v___f_617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4));
v___f_618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5));
lean_inc_ref(v_toFunctor_609_);
v___f_619_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_619_, 0, v_toFunctor_609_);
v___f_620_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_620_, 0, v_toFunctor_609_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v___f_619_);
lean_ctor_set(v___x_621_, 1, v___f_620_);
v___f_622_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_622_, 0, v_toSeqRight_612_);
v___f_623_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_623_, 0, v_toSeqLeft_611_);
v___f_624_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_624_, 0, v_toSeq_610_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 4, v___f_622_);
lean_ctor_set(v___x_614_, 3, v___f_623_);
lean_ctor_set(v___x_614_, 2, v___f_624_);
lean_ctor_set(v___x_614_, 1, v___f_617_);
lean_ctor_set(v___x_614_, 0, v___x_621_);
v___x_626_ = v___x_614_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v___f_617_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v___f_624_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v___f_623_);
lean_ctor_set(v_reuseFailAlloc_634_, 4, v___f_622_);
v___x_626_ = v_reuseFailAlloc_634_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_628_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___f_618_);
lean_ctor_set(v___x_607_, 0, v___x_626_);
v___x_628_ = v___x_607_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___f_618_);
v___x_628_ = v_reuseFailAlloc_633_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; lean_object* v___f_630_; lean_object* v___x_617__overap_631_; lean_object* v___x_632_; 
v___x_629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
lean_inc(v_mvarId_563_);
v___f_630_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_630_, 0, v_mvarId_563_);
lean_closure_set(v___f_630_, 1, v___x_629_);
lean_closure_set(v___f_630_, 2, v_mkName_565_);
lean_closure_set(v___f_630_, 3, v_n_564_);
lean_closure_set(v___f_630_, 4, v_s_566_);
lean_closure_set(v___f_630_, 5, v___f_616_);
v___x_617__overap_631_ = l_Lean_MVarId_withContext___redArg(v___x_590_, v___x_628_, v_mvarId_563_, v___f_630_);
lean_inc(v_a_570_);
lean_inc_ref(v_a_569_);
lean_inc(v_a_568_);
lean_inc_ref(v_a_567_);
v___x_632_ = lean_apply_5(v___x_617__overap_631_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, lean_box(0));
return v___x_632_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___boxed(lean_object* v_00_u03c3_639_, lean_object* v_mvarId_640_, lean_object* v_n_641_, lean_object* v_mkName_642_, lean_object* v_s_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(v_00_u03c3_639_, v_mvarId_640_, v_n_641_, v_mkName_642_, v_s_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(lean_object* v_name_650_, lean_object* v_decl_651_, lean_object* v_ref_652_){
_start:
{
lean_object* v_defValue_654_; lean_object* v_descr_655_; lean_object* v_deprecation_x3f_656_; lean_object* v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_defValue_654_ = lean_ctor_get(v_decl_651_, 0);
v_descr_655_ = lean_ctor_get(v_decl_651_, 1);
v_deprecation_x3f_656_ = lean_ctor_get(v_decl_651_, 2);
v___x_657_ = lean_alloc_ctor(1, 0, 1);
v___x_658_ = lean_unbox(v_defValue_654_);
lean_ctor_set_uint8(v___x_657_, 0, v___x_658_);
lean_inc(v_deprecation_x3f_656_);
lean_inc_ref(v_descr_655_);
lean_inc_n(v_name_650_, 2);
v___x_659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_659_, 0, v_name_650_);
lean_ctor_set(v___x_659_, 1, v_ref_652_);
lean_ctor_set(v___x_659_, 2, v___x_657_);
lean_ctor_set(v___x_659_, 3, v_descr_655_);
lean_ctor_set(v___x_659_, 4, v_deprecation_x3f_656_);
v___x_660_ = lean_register_option(v_name_650_, v___x_659_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_668_; 
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; 
v_unused_669_ = lean_ctor_get(v___x_660_, 0);
lean_dec(v_unused_669_);
v___x_662_ = v___x_660_;
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
else
{
lean_dec(v___x_660_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
lean_inc(v_defValue_654_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v_name_650_);
lean_ctor_set(v___x_664_, 1, v_defValue_654_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec(v_name_650_);
v_a_670_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_660_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_660_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_678_, lean_object* v_decl_679_, lean_object* v_ref_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(v_name_678_, v_decl_679_, v_ref_680_);
lean_dec_ref(v_decl_679_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_));
v___x_703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_));
v___x_704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_));
v___x_705_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(v___x_702_, v___x_703_, v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4____boxed(lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_();
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(lean_object* v_lctx_708_, lean_object* v_binderName_709_, uint8_t v_hygienic_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
if (v_hygienic_710_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = l_Lean_LocalContext_getUnusedName(v_lctx_708_, v_binderName_709_);
lean_dec(v_binderName_709_);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Core_mkFreshUserName(v_binderName_709_, v_a_711_, v_a_712_);
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg___boxed(lean_object* v_lctx_717_, lean_object* v_binderName_718_, lean_object* v_hygienic_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
uint8_t v_hygienic_boxed_723_; lean_object* v_res_724_; 
v_hygienic_boxed_723_ = lean_unbox(v_hygienic_719_);
v_res_724_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_717_, v_binderName_718_, v_hygienic_boxed_723_, v_a_720_, v_a_721_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec_ref(v_lctx_717_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore(lean_object* v_lctx_725_, lean_object* v_binderName_726_, uint8_t v_hygienic_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_725_, v_binderName_726_, v_hygienic_727_, v_a_730_, v_a_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore___boxed(lean_object* v_lctx_734_, lean_object* v_binderName_735_, lean_object* v_hygienic_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
uint8_t v_hygienic_boxed_742_; lean_object* v_res_743_; 
v_hygienic_boxed_742_ = lean_unbox(v_hygienic_736_);
v_res_743_ = l_Lean_Meta_mkFreshBinderNameForTacticCore(v_lctx_734_, v_binderName_735_, v_hygienic_boxed_742_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec_ref(v_lctx_734_);
return v_res_743_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(lean_object* v_opts_744_, lean_object* v_opt_745_){
_start:
{
lean_object* v_name_746_; lean_object* v_defValue_747_; lean_object* v_map_748_; lean_object* v___x_749_; 
v_name_746_ = lean_ctor_get(v_opt_745_, 0);
v_defValue_747_ = lean_ctor_get(v_opt_745_, 1);
v_map_748_ = lean_ctor_get(v_opts_744_, 0);
v___x_749_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_748_, v_name_746_);
if (lean_obj_tag(v___x_749_) == 0)
{
uint8_t v___x_750_; 
v___x_750_ = lean_unbox(v_defValue_747_);
return v___x_750_;
}
else
{
lean_object* v_val_751_; 
v_val_751_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_val_751_);
lean_dec_ref_known(v___x_749_, 1);
if (lean_obj_tag(v_val_751_) == 1)
{
uint8_t v_v_752_; 
v_v_752_ = lean_ctor_get_uint8(v_val_751_, 0);
lean_dec_ref_known(v_val_751_, 0);
return v_v_752_;
}
else
{
uint8_t v___x_753_; 
lean_dec(v_val_751_);
v___x_753_ = lean_unbox(v_defValue_747_);
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0___boxed(lean_object* v_opts_754_, lean_object* v_opt_755_){
_start:
{
uint8_t v_res_756_; lean_object* v_r_757_; 
v_res_756_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v_opts_754_, v_opt_755_);
lean_dec_ref(v_opt_755_);
lean_dec_ref(v_opts_754_);
v_r_757_ = lean_box(v_res_756_);
return v_r_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg(lean_object* v_binderName_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_lctx_763_; lean_object* v_options_764_; lean_object* v___x_765_; uint8_t v___x_766_; lean_object* v___x_767_; 
v_lctx_763_ = lean_ctor_get(v_a_759_, 2);
v_options_764_ = lean_ctor_get(v_a_760_, 2);
v___x_765_ = l_Lean_Meta_tactic_hygienic;
v___x_766_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v_options_764_, v___x_765_);
v___x_767_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_763_, v_binderName_758_, v___x_766_, v_a_760_, v_a_761_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg___boxed(lean_object* v_binderName_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_binderName_768_, v_a_769_, v_a_770_, v_a_771_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec_ref(v_a_769_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic(lean_object* v_binderName_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_binderName_774_, v_a_775_, v_a_777_, v_a_778_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___boxed(lean_object* v_binderName_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Meta_mkFreshBinderNameForTactic(v_binderName_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(uint8_t v_preserveBinderNames_791_, uint8_t v_hygienic_792_, lean_object* v_lctx_793_, lean_object* v_binderName_794_, lean_object* v_rest_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v_binderName_800_; lean_object* v___y_801_; lean_object* v___y_802_; uint8_t v___x_823_; 
v___x_823_ = l_Lean_Name_isAnonymous(v_binderName_794_);
if (v___x_823_ == 0)
{
v_binderName_800_ = v_binderName_794_;
v___y_801_ = v_a_796_;
v___y_802_ = v_a_797_;
goto v___jp_799_;
}
else
{
lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec(v_binderName_794_);
v___x_824_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__1));
v___x_825_ = l_Lean_Core_mkFreshUserName(v___x_824_, v_a_796_, v_a_797_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v___x_825_, 1);
v_binderName_800_ = v_a_826_;
v___y_801_ = v_a_796_;
v___y_802_ = v_a_797_;
goto v___jp_799_;
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_rest_795_);
v_a_827_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_825_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_825_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
v___jp_799_:
{
if (v_preserveBinderNames_791_ == 0)
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_793_, v_binderName_800_, v_hygienic_792_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_812_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_812_ == 0)
{
v___x_806_ = v___x_803_;
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v_a_804_);
lean_ctor_set(v___x_808_, 1, v_rest_795_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_808_);
v___x_810_ = v___x_806_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec(v_rest_795_);
v_a_813_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_803_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_803_);
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
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
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
else
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_binderName_800_);
lean_ctor_set(v___x_821_, 1, v_rest_795_);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___boxed(lean_object* v_preserveBinderNames_835_, lean_object* v_hygienic_836_, lean_object* v_lctx_837_, lean_object* v_binderName_838_, lean_object* v_rest_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
uint8_t v_preserveBinderNames_boxed_843_; uint8_t v_hygienic_boxed_844_; lean_object* v_res_845_; 
v_preserveBinderNames_boxed_843_ = lean_unbox(v_preserveBinderNames_835_);
v_hygienic_boxed_844_ = lean_unbox(v_hygienic_836_);
v_res_845_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_boxed_843_, v_hygienic_boxed_844_, v_lctx_837_, v_binderName_838_, v_rest_839_, v_a_840_, v_a_841_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec_ref(v_lctx_837_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(uint8_t v_preserveBinderNames_846_, uint8_t v_hygienic_847_, lean_object* v_lctx_848_, lean_object* v_binderName_849_, lean_object* v_rest_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_846_, v_hygienic_847_, v_lctx_848_, v_binderName_849_, v_rest_850_, v_a_853_, v_a_854_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___boxed(lean_object* v_preserveBinderNames_857_, lean_object* v_hygienic_858_, lean_object* v_lctx_859_, lean_object* v_binderName_860_, lean_object* v_rest_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
uint8_t v_preserveBinderNames_boxed_867_; uint8_t v_hygienic_boxed_868_; lean_object* v_res_869_; 
v_preserveBinderNames_boxed_867_ = lean_unbox(v_preserveBinderNames_857_);
v_hygienic_boxed_868_ = lean_unbox(v_hygienic_858_);
v_res_869_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(v_preserveBinderNames_boxed_867_, v_hygienic_boxed_868_, v_lctx_859_, v_binderName_860_, v_rest_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec_ref(v_lctx_859_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(uint8_t v_preserveBinderNames_874_, uint8_t v_hygienic_875_, uint8_t v_useNamesForExplicitOnly_876_, lean_object* v_lctx_877_, lean_object* v_binderName_878_, uint8_t v_isExplicit_879_, lean_object* v_x_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
if (lean_obj_tag(v_x_880_) == 0)
{
lean_object* v___x_884_; 
v___x_884_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_874_, v_hygienic_875_, v_lctx_877_, v_binderName_878_, v_x_880_, v_a_881_, v_a_882_);
return v___x_884_;
}
else
{
lean_object* v_head_885_; lean_object* v_tail_886_; 
v_head_885_ = lean_ctor_get(v_x_880_, 0);
v_tail_886_ = lean_ctor_get(v_x_880_, 1);
if (v_useNamesForExplicitOnly_876_ == 0)
{
lean_inc(v_tail_886_);
lean_inc(v_head_885_);
lean_dec_ref_known(v_x_880_, 2);
goto v___jp_887_;
}
else
{
uint8_t v___x_894_; 
v___x_894_ = lean_bool_not(v_isExplicit_879_);
if (v___x_894_ == 0)
{
lean_inc(v_tail_886_);
lean_inc(v_head_885_);
lean_dec_ref_known(v_x_880_, 2);
goto v___jp_887_;
}
else
{
lean_object* v___x_895_; 
v___x_895_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_874_, v_hygienic_875_, v_lctx_877_, v_binderName_878_, v_x_880_, v_a_881_, v_a_882_);
return v___x_895_;
}
}
v___jp_887_:
{
lean_object* v___x_888_; uint8_t v___x_889_; uint8_t v___x_890_; 
v___x_888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__1));
v___x_889_ = lean_name_eq(v_head_885_, v___x_888_);
v___x_890_ = lean_bool_not(v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
lean_dec(v_head_885_);
v___x_891_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_874_, v_hygienic_875_, v_lctx_877_, v_binderName_878_, v_tail_886_, v_a_881_, v_a_882_);
return v___x_891_;
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec(v_binderName_878_);
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v_head_885_);
lean_ctor_set(v___x_892_, 1, v_tail_886_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___boxed(lean_object* v_preserveBinderNames_896_, lean_object* v_hygienic_897_, lean_object* v_useNamesForExplicitOnly_898_, lean_object* v_lctx_899_, lean_object* v_binderName_900_, lean_object* v_isExplicit_901_, lean_object* v_x_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
uint8_t v_preserveBinderNames_boxed_906_; uint8_t v_hygienic_boxed_907_; uint8_t v_useNamesForExplicitOnly_boxed_908_; uint8_t v_isExplicit_boxed_909_; lean_object* v_res_910_; 
v_preserveBinderNames_boxed_906_ = lean_unbox(v_preserveBinderNames_896_);
v_hygienic_boxed_907_ = lean_unbox(v_hygienic_897_);
v_useNamesForExplicitOnly_boxed_908_ = lean_unbox(v_useNamesForExplicitOnly_898_);
v_isExplicit_boxed_909_ = lean_unbox(v_isExplicit_901_);
v_res_910_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_boxed_906_, v_hygienic_boxed_907_, v_useNamesForExplicitOnly_boxed_908_, v_lctx_899_, v_binderName_900_, v_isExplicit_boxed_909_, v_x_902_, v_a_903_, v_a_904_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec_ref(v_lctx_899_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(uint8_t v_preserveBinderNames_911_, uint8_t v_hygienic_912_, uint8_t v_useNamesForExplicitOnly_913_, lean_object* v_lctx_914_, lean_object* v_binderName_915_, uint8_t v_isExplicit_916_, lean_object* v_x_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_911_, v_hygienic_912_, v_useNamesForExplicitOnly_913_, v_lctx_914_, v_binderName_915_, v_isExplicit_916_, v_x_917_, v_a_920_, v_a_921_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___boxed(lean_object* v_preserveBinderNames_924_, lean_object* v_hygienic_925_, lean_object* v_useNamesForExplicitOnly_926_, lean_object* v_lctx_927_, lean_object* v_binderName_928_, lean_object* v_isExplicit_929_, lean_object* v_x_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
uint8_t v_preserveBinderNames_boxed_936_; uint8_t v_hygienic_boxed_937_; uint8_t v_useNamesForExplicitOnly_boxed_938_; uint8_t v_isExplicit_boxed_939_; lean_object* v_res_940_; 
v_preserveBinderNames_boxed_936_ = lean_unbox(v_preserveBinderNames_924_);
v_hygienic_boxed_937_ = lean_unbox(v_hygienic_925_);
v_useNamesForExplicitOnly_boxed_938_ = lean_unbox(v_useNamesForExplicitOnly_926_);
v_isExplicit_boxed_939_ = lean_unbox(v_isExplicit_929_);
v_res_940_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(v_preserveBinderNames_boxed_936_, v_hygienic_boxed_937_, v_useNamesForExplicitOnly_boxed_938_, v_lctx_927_, v_binderName_928_, v_isExplicit_boxed_939_, v_x_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec_ref(v_lctx_927_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(lean_object* v_mvarId_941_, lean_object* v_x_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_941_, v_x_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_948_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_948_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg___boxed(lean_object* v_mvarId_965_, lean_object* v_x_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_965_, v_x_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(lean_object* v_00_u03b1_973_, lean_object* v_mvarId_974_, lean_object* v_x_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_974_, v_x_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___boxed(lean_object* v_00_u03b1_982_, lean_object* v_mvarId_983_, lean_object* v_x_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(v_00_u03b1_982_, v_mvarId_983_, v_x_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(size_t v_sz_991_, size_t v_i_992_, lean_object* v_bs_993_){
_start:
{
uint8_t v___x_994_; 
v___x_994_ = lean_usize_dec_lt(v_i_992_, v_sz_991_);
if (v___x_994_ == 0)
{
return v_bs_993_;
}
else
{
lean_object* v_v_995_; lean_object* v___x_996_; lean_object* v_bs_x27_997_; lean_object* v___x_998_; size_t v___x_999_; size_t v___x_1000_; lean_object* v___x_1001_; 
v_v_995_ = lean_array_uget(v_bs_993_, v_i_992_);
v___x_996_ = lean_unsigned_to_nat(0u);
v_bs_x27_997_ = lean_array_uset(v_bs_993_, v_i_992_, v___x_996_);
v___x_998_ = l_Lean_Expr_fvarId_x21(v_v_995_);
lean_dec(v_v_995_);
v___x_999_ = ((size_t)1ULL);
v___x_1000_ = lean_usize_add(v_i_992_, v___x_999_);
v___x_1001_ = lean_array_uset(v_bs_x27_997_, v_i_992_, v___x_998_);
v_i_992_ = v___x_1000_;
v_bs_993_ = v___x_1001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1___boxed(lean_object* v_sz_1003_, lean_object* v_i_1004_, lean_object* v_bs_1005_){
_start:
{
size_t v_sz_boxed_1006_; size_t v_i_boxed_1007_; lean_object* v_res_1008_; 
v_sz_boxed_1006_ = lean_unbox_usize(v_sz_1003_);
lean_dec(v_sz_1003_);
v_i_boxed_1007_ = lean_unbox_usize(v_i_1004_);
lean_dec(v_i_1004_);
v_res_1008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(v_sz_boxed_1006_, v_i_boxed_1007_, v_bs_1005_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(lean_object* v_e_1009_, lean_object* v___y_1010_){
_start:
{
uint8_t v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = l_Lean_Expr_hasMVar(v_e_1009_);
v___x_1013_ = lean_bool_not(v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; lean_object* v_mctx_1015_; lean_object* v___x_1016_; lean_object* v_fst_1017_; lean_object* v_snd_1018_; lean_object* v___x_1019_; lean_object* v_cache_1020_; lean_object* v_zetaDeltaFVarIds_1021_; lean_object* v_postponed_1022_; lean_object* v_diag_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1032_; 
v___x_1014_ = lean_st_ref_get(v___y_1010_);
v_mctx_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc_ref(v_mctx_1015_);
lean_dec(v___x_1014_);
v___x_1016_ = l_Lean_instantiateMVarsCore(v_mctx_1015_, v_e_1009_);
v_fst_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_fst_1017_);
v_snd_1018_ = lean_ctor_get(v___x_1016_, 1);
lean_inc(v_snd_1018_);
lean_dec_ref(v___x_1016_);
v___x_1019_ = lean_st_ref_take(v___y_1010_);
v_cache_1020_ = lean_ctor_get(v___x_1019_, 1);
v_zetaDeltaFVarIds_1021_ = lean_ctor_get(v___x_1019_, 2);
v_postponed_1022_ = lean_ctor_get(v___x_1019_, 3);
v_diag_1023_ = lean_ctor_get(v___x_1019_, 4);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v___x_1019_, 0);
lean_dec(v_unused_1033_);
v___x_1025_ = v___x_1019_;
v_isShared_1026_ = v_isSharedCheck_1032_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_diag_1023_);
lean_inc(v_postponed_1022_);
lean_inc(v_zetaDeltaFVarIds_1021_);
lean_inc(v_cache_1020_);
lean_dec(v___x_1019_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1032_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v_snd_1018_);
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_snd_1018_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_cache_1020_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v_zetaDeltaFVarIds_1021_);
lean_ctor_set(v_reuseFailAlloc_1031_, 3, v_postponed_1022_);
lean_ctor_set(v_reuseFailAlloc_1031_, 4, v_diag_1023_);
v___x_1028_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_st_ref_set(v___y_1010_, v___x_1028_);
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v_fst_1017_);
return v___x_1030_;
}
}
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v_e_1009_);
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg___boxed(lean_object* v_e_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_1035_, v___y_1036_);
lean_dec(v___y_1036_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1041_; lean_object* v_ngen_1042_; lean_object* v_namePrefix_1043_; lean_object* v_idx_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1073_; 
v___x_1041_ = lean_st_ref_get(v___y_1039_);
v_ngen_1042_ = lean_ctor_get(v___x_1041_, 2);
lean_inc_ref(v_ngen_1042_);
lean_dec(v___x_1041_);
v_namePrefix_1043_ = lean_ctor_get(v_ngen_1042_, 0);
v_idx_1044_ = lean_ctor_get(v_ngen_1042_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_ngen_1042_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1046_ = v_ngen_1042_;
v_isShared_1047_ = v_isSharedCheck_1073_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_idx_1044_);
lean_inc(v_namePrefix_1043_);
lean_dec(v_ngen_1042_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1073_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v_env_1049_; lean_object* v_nextMacroScope_1050_; lean_object* v_auxDeclNGen_1051_; lean_object* v_traceState_1052_; lean_object* v_cache_1053_; lean_object* v_messages_1054_; lean_object* v_infoState_1055_; lean_object* v_snapshotTasks_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1071_; 
v___x_1048_ = lean_st_ref_take(v___y_1039_);
v_env_1049_ = lean_ctor_get(v___x_1048_, 0);
v_nextMacroScope_1050_ = lean_ctor_get(v___x_1048_, 1);
v_auxDeclNGen_1051_ = lean_ctor_get(v___x_1048_, 3);
v_traceState_1052_ = lean_ctor_get(v___x_1048_, 4);
v_cache_1053_ = lean_ctor_get(v___x_1048_, 5);
v_messages_1054_ = lean_ctor_get(v___x_1048_, 6);
v_infoState_1055_ = lean_ctor_get(v___x_1048_, 7);
v_snapshotTasks_1056_ = lean_ctor_get(v___x_1048_, 8);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v___x_1048_, 2);
lean_dec(v_unused_1072_);
v___x_1058_ = v___x_1048_;
v_isShared_1059_ = v_isSharedCheck_1071_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_snapshotTasks_1056_);
lean_inc(v_infoState_1055_);
lean_inc(v_messages_1054_);
lean_inc(v_cache_1053_);
lean_inc(v_traceState_1052_);
lean_inc(v_auxDeclNGen_1051_);
lean_inc(v_nextMacroScope_1050_);
lean_inc(v_env_1049_);
lean_dec(v___x_1048_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1071_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v_r_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
lean_inc(v_idx_1044_);
lean_inc(v_namePrefix_1043_);
v_r_1060_ = l_Lean_Name_num___override(v_namePrefix_1043_, v_idx_1044_);
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_nat_add(v_idx_1044_, v___x_1061_);
lean_dec(v_idx_1044_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 1, v___x_1062_);
v___x_1064_ = v___x_1046_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_namePrefix_1043_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1066_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 2, v___x_1064_);
v___x_1066_ = v___x_1058_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_env_1049_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_nextMacroScope_1050_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v_auxDeclNGen_1051_);
lean_ctor_set(v_reuseFailAlloc_1069_, 4, v_traceState_1052_);
lean_ctor_set(v_reuseFailAlloc_1069_, 5, v_cache_1053_);
lean_ctor_set(v_reuseFailAlloc_1069_, 6, v_messages_1054_);
lean_ctor_set(v_reuseFailAlloc_1069_, 7, v_infoState_1055_);
lean_ctor_set(v_reuseFailAlloc_1069_, 8, v_snapshotTasks_1056_);
v___x_1066_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_st_ref_set(v___y_1039_, v___x_1066_);
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v_r_1060_);
return v___x_1068_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1074_);
lean_dec(v___y_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v___x_1082_; lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v___x_1082_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1080_);
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3___boxed(lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(lean_object* v_fvars_1097_, lean_object* v_j_1098_, lean_object* v_x_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp(lean_box(0), v_fvars_1097_, v_j_1098_, v_x_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
v_a_1114_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1105_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1105_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_fvars_1122_, lean_object* v_j_1123_, lean_object* v_x_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1122_, v_j_1123_, v_x_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(lean_object* v_fvars_1131_, lean_object* v_j_1132_, lean_object* v_x_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1131_, v_j_1132_, v_x_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
v_a_1148_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1139_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1139_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg___boxed(lean_object* v_fvars_1156_, lean_object* v_j_1157_, lean_object* v_x_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(v_fvars_1156_, v_j_1157_, v_x_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1(lean_object* v_00_u03b1_1165_, lean_object* v_fvars_1166_, lean_object* v_j_1167_, lean_object* v_x_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(v_fvars_1166_, v_j_1167_, v_x_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1175_, lean_object* v_fvars_1176_, lean_object* v_j_1177_, lean_object* v_x_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1(v_00_u03b1_1175_, v_fvars_1176_, v_j_1177_, v_x_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(lean_object* v_x_1185_, lean_object* v_x_1186_, lean_object* v_x_1187_, lean_object* v_x_1188_){
_start:
{
lean_object* v_ks_1189_; lean_object* v_vs_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1214_; 
v_ks_1189_ = lean_ctor_get(v_x_1185_, 0);
v_vs_1190_ = lean_ctor_get(v_x_1185_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_x_1185_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1192_ = v_x_1185_;
v_isShared_1193_ = v_isSharedCheck_1214_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_vs_1190_);
lean_inc(v_ks_1189_);
lean_dec(v_x_1185_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1214_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = lean_array_get_size(v_ks_1189_);
v___x_1195_ = lean_nat_dec_lt(v_x_1186_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
lean_dec(v_x_1186_);
v___x_1196_ = lean_array_push(v_ks_1189_, v_x_1187_);
v___x_1197_ = lean_array_push(v_vs_1190_, v_x_1188_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v___x_1197_);
lean_ctor_set(v___x_1192_, 0, v___x_1196_);
v___x_1199_ = v___x_1192_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
else
{
lean_object* v_k_x27_1201_; uint8_t v___x_1202_; 
v_k_x27_1201_ = lean_array_fget_borrowed(v_ks_1189_, v_x_1186_);
v___x_1202_ = l_Lean_instBEqMVarId_beq(v_x_1187_, v_k_x27_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1204_; 
if (v_isShared_1193_ == 0)
{
v___x_1204_ = v___x_1192_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_ks_1189_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_vs_1190_);
v___x_1204_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_unsigned_to_nat(1u);
v___x_1206_ = lean_nat_add(v_x_1186_, v___x_1205_);
lean_dec(v_x_1186_);
v_x_1185_ = v___x_1204_;
v_x_1186_ = v___x_1206_;
goto _start;
}
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1209_ = lean_array_fset(v_ks_1189_, v_x_1186_, v_x_1187_);
v___x_1210_ = lean_array_fset(v_vs_1190_, v_x_1186_, v_x_1188_);
lean_dec(v_x_1186_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v___x_1210_);
lean_ctor_set(v___x_1192_, 0, v___x_1209_);
v___x_1212_ = v___x_1192_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(lean_object* v_n_1215_, lean_object* v_k_1216_, lean_object* v_v_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1219_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(v_n_1215_, v___x_1218_, v_k_1216_, v_v_1217_);
return v___x_1219_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_1221_, size_t v_x_1222_, size_t v_x_1223_, lean_object* v_x_1224_, lean_object* v_x_1225_){
_start:
{
if (lean_obj_tag(v_x_1221_) == 0)
{
lean_object* v_es_1226_; size_t v___x_1227_; size_t v___x_1228_; lean_object* v_j_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v_es_1226_ = lean_ctor_get(v_x_1221_, 0);
v___x_1227_ = ((size_t)31ULL);
v___x_1228_ = lean_usize_land(v_x_1222_, v___x_1227_);
v_j_1229_ = lean_usize_to_nat(v___x_1228_);
v___x_1230_ = lean_array_get_size(v_es_1226_);
v___x_1231_ = lean_nat_dec_lt(v_j_1229_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_dec(v_j_1229_);
lean_dec(v_x_1225_);
lean_dec(v_x_1224_);
return v_x_1221_;
}
else
{
lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1270_; 
lean_inc_ref(v_es_1226_);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_x_1221_);
if (v_isSharedCheck_1270_ == 0)
{
lean_object* v_unused_1271_; 
v_unused_1271_ = lean_ctor_get(v_x_1221_, 0);
lean_dec(v_unused_1271_);
v___x_1233_ = v_x_1221_;
v_isShared_1234_ = v_isSharedCheck_1270_;
goto v_resetjp_1232_;
}
else
{
lean_dec(v_x_1221_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1270_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v_v_1235_; lean_object* v___x_1236_; lean_object* v_xs_x27_1237_; lean_object* v___y_1239_; 
v_v_1235_ = lean_array_fget(v_es_1226_, v_j_1229_);
v___x_1236_ = lean_box(0);
v_xs_x27_1237_ = lean_array_fset(v_es_1226_, v_j_1229_, v___x_1236_);
switch(lean_obj_tag(v_v_1235_))
{
case 0:
{
lean_object* v_key_1244_; lean_object* v_val_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1255_; 
v_key_1244_ = lean_ctor_get(v_v_1235_, 0);
v_val_1245_ = lean_ctor_get(v_v_1235_, 1);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_v_1235_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1247_ = v_v_1235_;
v_isShared_1248_ = v_isSharedCheck_1255_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_val_1245_);
lean_inc(v_key_1244_);
lean_dec(v_v_1235_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1255_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
uint8_t v___x_1249_; 
v___x_1249_ = l_Lean_instBEqMVarId_beq(v_x_1224_, v_key_1244_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_del_object(v___x_1247_);
v___x_1250_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1244_, v_val_1245_, v_x_1224_, v_x_1225_);
v___x_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
v___y_1239_ = v___x_1251_;
goto v___jp_1238_;
}
else
{
lean_object* v___x_1253_; 
lean_dec(v_val_1245_);
lean_dec(v_key_1244_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 1, v_x_1225_);
lean_ctor_set(v___x_1247_, 0, v_x_1224_);
v___x_1253_ = v___x_1247_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_x_1224_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_x_1225_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
v___y_1239_ = v___x_1253_;
goto v___jp_1238_;
}
}
}
}
case 1:
{
lean_object* v_node_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1268_; 
v_node_1256_ = lean_ctor_get(v_v_1235_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_v_1235_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1258_ = v_v_1235_;
v_isShared_1259_ = v_isSharedCheck_1268_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_node_1256_);
lean_dec(v_v_1235_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1268_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
size_t v___x_1260_; size_t v___x_1261_; size_t v___x_1262_; size_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1260_ = ((size_t)5ULL);
v___x_1261_ = lean_usize_shift_right(v_x_1222_, v___x_1260_);
v___x_1262_ = ((size_t)1ULL);
v___x_1263_ = lean_usize_add(v_x_1223_, v___x_1262_);
v___x_1264_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_node_1256_, v___x_1261_, v___x_1263_, v_x_1224_, v_x_1225_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 0, v___x_1264_);
v___x_1266_ = v___x_1258_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
v___y_1239_ = v___x_1266_;
goto v___jp_1238_;
}
}
}
default: 
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v_x_1224_);
lean_ctor_set(v___x_1269_, 1, v_x_1225_);
v___y_1239_ = v___x_1269_;
goto v___jp_1238_;
}
}
v___jp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1240_ = lean_array_fset(v_xs_x27_1237_, v_j_1229_, v___y_1239_);
lean_dec(v_j_1229_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1240_);
v___x_1242_ = v___x_1233_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
else
{
lean_object* v_ks_1272_; lean_object* v_vs_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1293_; 
v_ks_1272_ = lean_ctor_get(v_x_1221_, 0);
v_vs_1273_ = lean_ctor_get(v_x_1221_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_x_1221_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1275_ = v_x_1221_;
v_isShared_1276_ = v_isSharedCheck_1293_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_vs_1273_);
lean_inc(v_ks_1272_);
lean_dec(v_x_1221_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1293_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_ks_1272_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_vs_1273_);
v___x_1278_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v_newNode_1279_; uint8_t v___y_1281_; size_t v___x_1287_; uint8_t v___x_1288_; 
v_newNode_1279_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(v___x_1278_, v_x_1224_, v_x_1225_);
v___x_1287_ = ((size_t)7ULL);
v___x_1288_ = lean_usize_dec_le(v___x_1287_, v_x_1223_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1289_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1279_);
v___x_1290_ = lean_unsigned_to_nat(4u);
v___x_1291_ = lean_nat_dec_lt(v___x_1289_, v___x_1290_);
lean_dec(v___x_1289_);
v___y_1281_ = v___x_1291_;
goto v___jp_1280_;
}
else
{
v___y_1281_ = v___x_1288_;
goto v___jp_1280_;
}
v___jp_1280_:
{
if (v___y_1281_ == 0)
{
lean_object* v_ks_1282_; lean_object* v_vs_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_ks_1282_ = lean_ctor_get(v_newNode_1279_, 0);
lean_inc_ref(v_ks_1282_);
v_vs_1283_ = lean_ctor_get(v_newNode_1279_, 1);
lean_inc_ref(v_vs_1283_);
lean_dec_ref(v_newNode_1279_);
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0);
v___x_1286_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_x_1223_, v_ks_1282_, v_vs_1283_, v___x_1284_, v___x_1285_);
lean_dec_ref(v_vs_1283_);
lean_dec_ref(v_ks_1282_);
return v___x_1286_;
}
else
{
return v_newNode_1279_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(size_t v_depth_1294_, lean_object* v_keys_1295_, lean_object* v_vals_1296_, lean_object* v_i_1297_, lean_object* v_entries_1298_){
_start:
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = lean_array_get_size(v_keys_1295_);
v___x_1300_ = lean_nat_dec_lt(v_i_1297_, v___x_1299_);
if (v___x_1300_ == 0)
{
lean_dec(v_i_1297_);
return v_entries_1298_;
}
else
{
lean_object* v_k_1301_; lean_object* v_v_1302_; uint64_t v___x_1303_; size_t v_h_1304_; size_t v___x_1305_; lean_object* v___x_1306_; size_t v___x_1307_; size_t v___x_1308_; size_t v___x_1309_; size_t v_h_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_k_1301_ = lean_array_fget_borrowed(v_keys_1295_, v_i_1297_);
v_v_1302_ = lean_array_fget_borrowed(v_vals_1296_, v_i_1297_);
v___x_1303_ = l_Lean_instHashableMVarId_hash(v_k_1301_);
v_h_1304_ = lean_uint64_to_usize(v___x_1303_);
v___x_1305_ = ((size_t)5ULL);
v___x_1306_ = lean_unsigned_to_nat(1u);
v___x_1307_ = ((size_t)1ULL);
v___x_1308_ = lean_usize_sub(v_depth_1294_, v___x_1307_);
v___x_1309_ = lean_usize_mul(v___x_1305_, v___x_1308_);
v_h_1310_ = lean_usize_shift_right(v_h_1304_, v___x_1309_);
v___x_1311_ = lean_nat_add(v_i_1297_, v___x_1306_);
lean_dec(v_i_1297_);
lean_inc(v_v_1302_);
lean_inc(v_k_1301_);
v___x_1312_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_entries_1298_, v_h_1310_, v_depth_1294_, v_k_1301_, v_v_1302_);
v_i_1297_ = v___x_1311_;
v_entries_1298_ = v___x_1312_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_depth_1314_, lean_object* v_keys_1315_, lean_object* v_vals_1316_, lean_object* v_i_1317_, lean_object* v_entries_1318_){
_start:
{
size_t v_depth_boxed_1319_; lean_object* v_res_1320_; 
v_depth_boxed_1319_ = lean_unbox_usize(v_depth_1314_);
lean_dec(v_depth_1314_);
v_res_1320_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_boxed_1319_, v_keys_1315_, v_vals_1316_, v_i_1317_, v_entries_1318_);
lean_dec_ref(v_vals_1316_);
lean_dec_ref(v_keys_1315_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_x_1321_, lean_object* v_x_1322_, lean_object* v_x_1323_, lean_object* v_x_1324_, lean_object* v_x_1325_){
_start:
{
size_t v_x_3896__boxed_1326_; size_t v_x_3897__boxed_1327_; lean_object* v_res_1328_; 
v_x_3896__boxed_1326_ = lean_unbox_usize(v_x_1322_);
lean_dec(v_x_1322_);
v_x_3897__boxed_1327_ = lean_unbox_usize(v_x_1323_);
lean_dec(v_x_1323_);
v_res_1328_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1321_, v_x_3896__boxed_1326_, v_x_3897__boxed_1327_, v_x_1324_, v_x_1325_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_){
_start:
{
uint64_t v___x_1332_; size_t v___x_1333_; size_t v___x_1334_; lean_object* v___x_1335_; 
v___x_1332_ = l_Lean_instHashableMVarId_hash(v_x_1330_);
v___x_1333_ = lean_uint64_to_usize(v___x_1332_);
v___x_1334_ = ((size_t)1ULL);
v___x_1335_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1329_, v___x_1333_, v___x_1334_, v_x_1330_, v_x_1331_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(lean_object* v_mvarId_1336_, lean_object* v_val_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; lean_object* v_mctx_1341_; lean_object* v_cache_1342_; lean_object* v_zetaDeltaFVarIds_1343_; lean_object* v_postponed_1344_; lean_object* v_diag_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1373_; 
v___x_1340_ = lean_st_ref_take(v___y_1338_);
v_mctx_1341_ = lean_ctor_get(v___x_1340_, 0);
v_cache_1342_ = lean_ctor_get(v___x_1340_, 1);
v_zetaDeltaFVarIds_1343_ = lean_ctor_get(v___x_1340_, 2);
v_postponed_1344_ = lean_ctor_get(v___x_1340_, 3);
v_diag_1345_ = lean_ctor_get(v___x_1340_, 4);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1347_ = v___x_1340_;
v_isShared_1348_ = v_isSharedCheck_1373_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_diag_1345_);
lean_inc(v_postponed_1344_);
lean_inc(v_zetaDeltaFVarIds_1343_);
lean_inc(v_cache_1342_);
lean_inc(v_mctx_1341_);
lean_dec(v___x_1340_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1373_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v_depth_1349_; lean_object* v_levelAssignDepth_1350_; lean_object* v_lmvarCounter_1351_; lean_object* v_mvarCounter_1352_; lean_object* v_lDecls_1353_; lean_object* v_decls_1354_; lean_object* v_userNames_1355_; lean_object* v_lAssignment_1356_; lean_object* v_eAssignment_1357_; lean_object* v_dAssignment_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1372_; 
v_depth_1349_ = lean_ctor_get(v_mctx_1341_, 0);
v_levelAssignDepth_1350_ = lean_ctor_get(v_mctx_1341_, 1);
v_lmvarCounter_1351_ = lean_ctor_get(v_mctx_1341_, 2);
v_mvarCounter_1352_ = lean_ctor_get(v_mctx_1341_, 3);
v_lDecls_1353_ = lean_ctor_get(v_mctx_1341_, 4);
v_decls_1354_ = lean_ctor_get(v_mctx_1341_, 5);
v_userNames_1355_ = lean_ctor_get(v_mctx_1341_, 6);
v_lAssignment_1356_ = lean_ctor_get(v_mctx_1341_, 7);
v_eAssignment_1357_ = lean_ctor_get(v_mctx_1341_, 8);
v_dAssignment_1358_ = lean_ctor_get(v_mctx_1341_, 9);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_mctx_1341_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1360_ = v_mctx_1341_;
v_isShared_1361_ = v_isSharedCheck_1372_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_dAssignment_1358_);
lean_inc(v_eAssignment_1357_);
lean_inc(v_lAssignment_1356_);
lean_inc(v_userNames_1355_);
lean_inc(v_decls_1354_);
lean_inc(v_lDecls_1353_);
lean_inc(v_mvarCounter_1352_);
lean_inc(v_lmvarCounter_1351_);
lean_inc(v_levelAssignDepth_1350_);
lean_inc(v_depth_1349_);
lean_dec(v_mctx_1341_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1372_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1362_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(v_eAssignment_1357_, v_mvarId_1336_, v_val_1337_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 8, v___x_1362_);
v___x_1364_ = v___x_1360_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_depth_1349_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_levelAssignDepth_1350_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v_lmvarCounter_1351_);
lean_ctor_set(v_reuseFailAlloc_1371_, 3, v_mvarCounter_1352_);
lean_ctor_set(v_reuseFailAlloc_1371_, 4, v_lDecls_1353_);
lean_ctor_set(v_reuseFailAlloc_1371_, 5, v_decls_1354_);
lean_ctor_set(v_reuseFailAlloc_1371_, 6, v_userNames_1355_);
lean_ctor_set(v_reuseFailAlloc_1371_, 7, v_lAssignment_1356_);
lean_ctor_set(v_reuseFailAlloc_1371_, 8, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1371_, 9, v_dAssignment_1358_);
v___x_1364_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1366_; 
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1364_);
v___x_1366_ = v___x_1347_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_cache_1342_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v_zetaDeltaFVarIds_1343_);
lean_ctor_set(v_reuseFailAlloc_1370_, 3, v_postponed_1344_);
lean_ctor_set(v_reuseFailAlloc_1370_, 4, v_diag_1345_);
v___x_1366_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1367_ = lean_st_ref_set(v___y_1338_, v___x_1366_);
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
return v___x_1369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg___boxed(lean_object* v_mvarId_1374_, lean_object* v_val_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1374_, v_val_1375_, v___y_1376_);
lean_dec(v___y_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(lean_object* v_mvarId_1379_, lean_object* v_type_1380_, lean_object* v_fvars_1381_, uint8_t v_isZero_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v___x_1388_; 
lean_inc(v_mvarId_1379_);
v___x_1388_ = l_Lean_MVarId_getTag(v_mvarId_1379_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1388_, 1);
v___x_1390_ = l_Lean_Expr_headBeta(v_type_1380_);
v___x_1391_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1390_, v_a_1389_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; uint8_t v___x_1393_; uint8_t v___x_1394_; lean_object* v___x_1395_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc_n(v_a_1392_, 2);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = 0;
v___x_1394_ = 1;
v___x_1395_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1381_, v_a_1392_, v___x_1393_, v_isZero_1382_, v___x_1393_, v_isZero_1382_, v___x_1394_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1397_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1397_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1379_, v_a_1396_, v___y_1384_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1406_; 
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; 
v_unused_1407_ = lean_ctor_get(v___x_1397_, 0);
lean_dec(v_unused_1407_);
v___x_1399_ = v___x_1397_;
v_isShared_1400_ = v_isSharedCheck_1406_;
goto v_resetjp_1398_;
}
else
{
lean_dec(v___x_1397_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1406_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1401_ = l_Lean_Expr_mvarId_x21(v_a_1392_);
lean_dec(v_a_1392_);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_fvars_1381_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1402_);
v___x_1404_ = v___x_1399_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v_a_1392_);
lean_dec_ref(v_fvars_1381_);
v_a_1408_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1397_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1397_);
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
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec(v_a_1392_);
lean_dec_ref(v_fvars_1381_);
lean_dec(v_mvarId_1379_);
v_a_1416_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1395_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1395_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec_ref(v_fvars_1381_);
lean_dec(v_mvarId_1379_);
v_a_1424_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1391_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1391_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec_ref(v_fvars_1381_);
lean_dec_ref(v_type_1380_);
lean_dec(v_mvarId_1379_);
v_a_1432_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1388_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1388_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0___boxed(lean_object* v_mvarId_1440_, lean_object* v_type_1441_, lean_object* v_fvars_1442_, lean_object* v_isZero_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
uint8_t v_isZero_boxed_1449_; lean_object* v_res_1450_; 
v_isZero_boxed_1449_ = lean_unbox(v_isZero_1443_);
v_res_1450_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(v_mvarId_1440_, v_type_1441_, v_fvars_1442_, v_isZero_boxed_1449_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(lean_object* v_lctx_1451_, lean_object* v_x_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_keyedConfig_1458_; uint8_t v_trackZetaDelta_1459_; lean_object* v_zetaDeltaSet_1460_; lean_object* v_localInstances_1461_; lean_object* v_defEqCtx_x3f_1462_; lean_object* v_synthPendingDepth_1463_; lean_object* v_canUnfold_x3f_1464_; uint8_t v_univApprox_1465_; uint8_t v_inTypeClassResolution_1466_; uint8_t v_cacheInferType_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v_keyedConfig_1458_ = lean_ctor_get(v___y_1453_, 0);
v_trackZetaDelta_1459_ = lean_ctor_get_uint8(v___y_1453_, sizeof(void*)*7);
v_zetaDeltaSet_1460_ = lean_ctor_get(v___y_1453_, 1);
v_localInstances_1461_ = lean_ctor_get(v___y_1453_, 3);
v_defEqCtx_x3f_1462_ = lean_ctor_get(v___y_1453_, 4);
v_synthPendingDepth_1463_ = lean_ctor_get(v___y_1453_, 5);
v_canUnfold_x3f_1464_ = lean_ctor_get(v___y_1453_, 6);
v_univApprox_1465_ = lean_ctor_get_uint8(v___y_1453_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1466_ = lean_ctor_get_uint8(v___y_1453_, sizeof(void*)*7 + 2);
v_cacheInferType_1467_ = lean_ctor_get_uint8(v___y_1453_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_1464_);
lean_inc(v_synthPendingDepth_1463_);
lean_inc(v_defEqCtx_x3f_1462_);
lean_inc_ref(v_localInstances_1461_);
lean_inc(v_zetaDeltaSet_1460_);
lean_inc_ref(v_keyedConfig_1458_);
v___x_1468_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1468_, 0, v_keyedConfig_1458_);
lean_ctor_set(v___x_1468_, 1, v_zetaDeltaSet_1460_);
lean_ctor_set(v___x_1468_, 2, v_lctx_1451_);
lean_ctor_set(v___x_1468_, 3, v_localInstances_1461_);
lean_ctor_set(v___x_1468_, 4, v_defEqCtx_x3f_1462_);
lean_ctor_set(v___x_1468_, 5, v_synthPendingDepth_1463_);
lean_ctor_set(v___x_1468_, 6, v_canUnfold_x3f_1464_);
lean_ctor_set_uint8(v___x_1468_, sizeof(void*)*7, v_trackZetaDelta_1459_);
lean_ctor_set_uint8(v___x_1468_, sizeof(void*)*7 + 1, v_univApprox_1465_);
lean_ctor_set_uint8(v___x_1468_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1466_);
lean_ctor_set_uint8(v___x_1468_, sizeof(void*)*7 + 3, v_cacheInferType_1467_);
lean_inc(v___y_1456_);
lean_inc_ref(v___y_1455_);
lean_inc(v___y_1454_);
v___x_1469_ = lean_apply_5(v_x_1452_, v___x_1468_, v___y_1454_, v___y_1455_, v___y_1456_, lean_box(0));
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg___boxed(lean_object* v_lctx_1470_, lean_object* v_x_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1470_, v_x_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed(lean_object* v_type_1478_, lean_object* v_mvarId_1479_, lean_object* v_n_1480_, lean_object* v_preserveBinderNames_1481_, lean_object* v___x_1482_, lean_object* v_useNamesForExplicitOnly_1483_, lean_object* v_lctx_1484_, lean_object* v_fvars_1485_, lean_object* v___x_1486_, lean_object* v_s_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1493_; uint8_t v___x_4257__boxed_1494_; uint8_t v_useNamesForExplicitOnly_boxed_1495_; lean_object* v_res_1496_; 
v_preserveBinderNames_boxed_1493_ = lean_unbox(v_preserveBinderNames_1481_);
v___x_4257__boxed_1494_ = lean_unbox(v___x_1482_);
v_useNamesForExplicitOnly_boxed_1495_ = lean_unbox(v_useNamesForExplicitOnly_1483_);
v_res_1496_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(v_type_1478_, v_mvarId_1479_, v_n_1480_, v_preserveBinderNames_boxed_1493_, v___x_4257__boxed_1494_, v_useNamesForExplicitOnly_boxed_1495_, v_lctx_1484_, v_fvars_1485_, v___x_1486_, v_s_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v_n_1480_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(uint8_t v_preserveBinderNames_1497_, uint8_t v___x_1498_, uint8_t v_useNamesForExplicitOnly_1499_, lean_object* v_mvarId_1500_, lean_object* v_i_1501_, lean_object* v_lctx_1502_, lean_object* v_fvars_1503_, lean_object* v_j_1504_, lean_object* v_s_1505_, lean_object* v_type_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v_zero_1512_; uint8_t v_isZero_1513_; 
v_zero_1512_ = lean_unsigned_to_nat(0u);
v_isZero_1513_ = lean_nat_dec_eq(v_i_1501_, v_zero_1512_);
if (v_isZero_1513_ == 1)
{
lean_object* v___x_1514_; lean_object* v_type_1515_; lean_object* v___x_1516_; lean_object* v___f_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec(v_s_1505_);
lean_dec(v_i_1501_);
v___x_1514_ = lean_array_get_size(v_fvars_1503_);
v_type_1515_ = lean_expr_instantiate_rev_range(v_type_1506_, v_j_1504_, v___x_1514_, v_fvars_1503_);
lean_dec_ref(v_type_1506_);
v___x_1516_ = lean_box(v_isZero_1513_);
lean_inc_ref(v_fvars_1503_);
v___f_1517_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1517_, 0, v_mvarId_1500_);
lean_closure_set(v___f_1517_, 1, v_type_1515_);
lean_closure_set(v___f_1517_, 2, v_fvars_1503_);
lean_closure_set(v___f_1517_, 3, v___x_1516_);
v___x_1518_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed), 9, 4);
lean_closure_set(v___x_1518_, 0, lean_box(0));
lean_closure_set(v___x_1518_, 1, v_fvars_1503_);
lean_closure_set(v___x_1518_, 2, v_j_1504_);
lean_closure_set(v___x_1518_, 3, v___f_1517_);
v___x_1519_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1502_, v___x_1518_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
return v___x_1519_;
}
else
{
lean_object* v_one_1520_; lean_object* v_n_1521_; 
v_one_1520_ = lean_unsigned_to_nat(1u);
v_n_1521_ = lean_nat_sub(v_i_1501_, v_one_1520_);
lean_dec(v_i_1501_);
switch(lean_obj_tag(v_type_1506_))
{
case 8:
{
lean_object* v_declName_1522_; lean_object* v_type_1523_; lean_object* v_value_1524_; lean_object* v_body_1525_; lean_object* v___x_1526_; 
v_declName_1522_ = lean_ctor_get(v_type_1506_, 0);
lean_inc(v_declName_1522_);
v_type_1523_ = lean_ctor_get(v_type_1506_, 1);
lean_inc_ref(v_type_1523_);
v_value_1524_ = lean_ctor_get(v_type_1506_, 2);
lean_inc_ref(v_value_1524_);
v_body_1525_ = lean_ctor_get(v_type_1506_, 3);
lean_inc_ref(v_body_1525_);
lean_dec_ref_known(v_type_1506_, 4);
v___x_1526_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v___x_1528_ = 1;
v___x_1529_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_1497_, v___x_1498_, v_useNamesForExplicitOnly_1499_, v_lctx_1502_, v_declName_1522_, v___x_1528_, v_s_1505_, v_a_1509_, v_a_1510_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v_fst_1531_; lean_object* v_snd_1532_; lean_object* v___x_1533_; lean_object* v_type_1534_; lean_object* v_type_1535_; lean_object* v_val_1536_; uint8_t v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v_fst_1531_ = lean_ctor_get(v_a_1530_, 0);
lean_inc(v_fst_1531_);
v_snd_1532_ = lean_ctor_get(v_a_1530_, 1);
lean_inc(v_snd_1532_);
lean_dec(v_a_1530_);
v___x_1533_ = lean_array_get_size(v_fvars_1503_);
v_type_1534_ = lean_expr_instantiate_rev_range(v_type_1523_, v_j_1504_, v___x_1533_, v_fvars_1503_);
lean_dec_ref(v_type_1523_);
v_type_1535_ = l_Lean_Expr_headBeta(v_type_1534_);
v_val_1536_ = lean_expr_instantiate_rev_range(v_value_1524_, v_j_1504_, v___x_1533_, v_fvars_1503_);
lean_dec_ref(v_value_1524_);
v___x_1537_ = 0;
lean_inc(v_a_1527_);
v___x_1538_ = l_Lean_LocalContext_mkLetDecl(v_lctx_1502_, v_a_1527_, v_fst_1531_, v_type_1535_, v_val_1536_, v_isZero_1513_, v___x_1537_);
v___x_1539_ = l_Lean_mkFVar(v_a_1527_);
v___x_1540_ = lean_array_push(v_fvars_1503_, v___x_1539_);
v_i_1501_ = v_n_1521_;
v_lctx_1502_ = v___x_1538_;
v_fvars_1503_ = v___x_1540_;
v_s_1505_ = v_snd_1532_;
v_type_1506_ = v_body_1525_;
goto _start;
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec(v_a_1527_);
lean_dec_ref(v_body_1525_);
lean_dec_ref(v_value_1524_);
lean_dec_ref(v_type_1523_);
lean_dec(v_n_1521_);
lean_dec(v_j_1504_);
lean_dec_ref(v_fvars_1503_);
lean_dec_ref(v_lctx_1502_);
lean_dec(v_mvarId_1500_);
v_a_1542_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1529_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1529_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
lean_dec_ref(v_body_1525_);
lean_dec_ref(v_value_1524_);
lean_dec_ref(v_type_1523_);
lean_dec(v_declName_1522_);
lean_dec(v_n_1521_);
lean_dec(v_s_1505_);
lean_dec(v_j_1504_);
lean_dec_ref(v_fvars_1503_);
lean_dec_ref(v_lctx_1502_);
lean_dec(v_mvarId_1500_);
v_a_1550_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1526_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1526_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1558_; lean_object* v_binderType_1559_; lean_object* v_body_1560_; uint8_t v_binderInfo_1561_; lean_object* v___x_1562_; 
v_binderName_1558_ = lean_ctor_get(v_type_1506_, 0);
lean_inc(v_binderName_1558_);
v_binderType_1559_ = lean_ctor_get(v_type_1506_, 1);
lean_inc_ref(v_binderType_1559_);
v_body_1560_ = lean_ctor_get(v_type_1506_, 2);
lean_inc_ref(v_body_1560_);
v_binderInfo_1561_ = lean_ctor_get_uint8(v_type_1506_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_1506_, 3);
v___x_1562_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1562_, 1);
v___x_1564_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_1561_);
v___x_1565_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_1497_, v___x_1498_, v_useNamesForExplicitOnly_1499_, v_lctx_1502_, v_binderName_1558_, v___x_1564_, v_s_1505_, v_a_1509_, v_a_1510_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v_fst_1567_; lean_object* v_snd_1568_; lean_object* v___x_1569_; lean_object* v_type_1570_; lean_object* v_type_1571_; uint8_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v_fst_1567_ = lean_ctor_get(v_a_1566_, 0);
lean_inc(v_fst_1567_);
v_snd_1568_ = lean_ctor_get(v_a_1566_, 1);
lean_inc(v_snd_1568_);
lean_dec(v_a_1566_);
v___x_1569_ = lean_array_get_size(v_fvars_1503_);
v_type_1570_ = lean_expr_instantiate_rev_range(v_binderType_1559_, v_j_1504_, v___x_1569_, v_fvars_1503_);
lean_dec_ref(v_binderType_1559_);
v_type_1571_ = l_Lean_Expr_headBeta(v_type_1570_);
v___x_1572_ = 0;
lean_inc(v_a_1563_);
v___x_1573_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_1502_, v_a_1563_, v_fst_1567_, v_type_1571_, v_binderInfo_1561_, v___x_1572_);
v___x_1574_ = l_Lean_mkFVar(v_a_1563_);
v___x_1575_ = lean_array_push(v_fvars_1503_, v___x_1574_);
v_i_1501_ = v_n_1521_;
v_lctx_1502_ = v___x_1573_;
v_fvars_1503_ = v___x_1575_;
v_s_1505_ = v_snd_1568_;
v_type_1506_ = v_body_1560_;
goto _start;
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec(v_a_1563_);
lean_dec_ref(v_body_1560_);
lean_dec_ref(v_binderType_1559_);
lean_dec(v_n_1521_);
lean_dec(v_j_1504_);
lean_dec_ref(v_fvars_1503_);
lean_dec_ref(v_lctx_1502_);
lean_dec(v_mvarId_1500_);
v_a_1577_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1565_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1565_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref(v_body_1560_);
lean_dec_ref(v_binderType_1559_);
lean_dec(v_binderName_1558_);
lean_dec(v_n_1521_);
lean_dec(v_s_1505_);
lean_dec(v_j_1504_);
lean_dec_ref(v_fvars_1503_);
lean_dec_ref(v_lctx_1502_);
lean_dec(v_mvarId_1500_);
v_a_1585_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1562_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1562_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
default: 
{
lean_object* v___x_1593_; lean_object* v_type_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___f_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1593_ = lean_array_get_size(v_fvars_1503_);
v_type_1594_ = lean_expr_instantiate_rev_range(v_type_1506_, v_j_1504_, v___x_1593_, v_fvars_1503_);
lean_dec_ref(v_type_1506_);
v___x_1595_ = lean_box(v_preserveBinderNames_1497_);
v___x_1596_ = lean_box(v___x_1498_);
v___x_1597_ = lean_box(v_useNamesForExplicitOnly_1499_);
lean_inc_ref(v_fvars_1503_);
lean_inc_ref(v_lctx_1502_);
v___f_1598_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed), 15, 10);
lean_closure_set(v___f_1598_, 0, v_type_1594_);
lean_closure_set(v___f_1598_, 1, v_mvarId_1500_);
lean_closure_set(v___f_1598_, 2, v_n_1521_);
lean_closure_set(v___f_1598_, 3, v___x_1595_);
lean_closure_set(v___f_1598_, 4, v___x_1596_);
lean_closure_set(v___f_1598_, 5, v___x_1597_);
lean_closure_set(v___f_1598_, 6, v_lctx_1502_);
lean_closure_set(v___f_1598_, 7, v_fvars_1503_);
lean_closure_set(v___f_1598_, 8, v___x_1593_);
lean_closure_set(v___f_1598_, 9, v_s_1505_);
v___x_1599_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed), 9, 4);
lean_closure_set(v___x_1599_, 0, lean_box(0));
lean_closure_set(v___x_1599_, 1, v_fvars_1503_);
lean_closure_set(v___x_1599_, 2, v_j_1504_);
lean_closure_set(v___x_1599_, 3, v___f_1598_);
v___x_1600_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1502_, v___x_1599_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
return v___x_1600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(lean_object* v_type_1601_, lean_object* v_mvarId_1602_, lean_object* v_n_1603_, uint8_t v_preserveBinderNames_1604_, uint8_t v___x_1605_, uint8_t v_useNamesForExplicitOnly_1606_, lean_object* v_lctx_1607_, lean_object* v_fvars_1608_, lean_object* v___x_1609_, lean_object* v_s_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_type_1601_, v___y_1612_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1618_; uint8_t v___y_1620_; uint8_t v___x_1641_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v___x_1618_ = l_Lean_Expr_cleanupAnnotations(v_a_1617_);
v___x_1641_ = l_Lean_Expr_isForall(v___x_1618_);
if (v___x_1641_ == 0)
{
uint8_t v___x_1642_; 
v___x_1642_ = l_Lean_Expr_isLet(v___x_1618_);
v___y_1620_ = v___x_1642_;
goto v___jp_1619_;
}
else
{
v___y_1620_ = v___x_1641_;
goto v___jp_1619_;
}
v___jp_1619_:
{
if (v___y_1620_ == 0)
{
lean_object* v___x_1621_; 
lean_inc(v___y_1614_);
lean_inc_ref(v___y_1613_);
lean_inc(v___y_1612_);
lean_inc_ref(v___y_1611_);
v___x_1621_ = lean_whnf(v___x_1618_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; uint8_t v___x_1623_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v___x_1623_ = l_Lean_Expr_isForall(v_a_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
lean_dec(v_a_1622_);
lean_dec(v_s_1610_);
lean_dec(v___x_1609_);
lean_dec_ref(v_fvars_1608_);
lean_dec_ref(v_lctx_1607_);
v___x_1624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
v___x_1625_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4);
v___x_1626_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1624_, v_mvarId_1602_, v___x_1625_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
return v___x_1626_;
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1627_ = lean_unsigned_to_nat(1u);
v___x_1628_ = lean_nat_add(v_n_1603_, v___x_1627_);
v___x_1629_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1604_, v___x_1605_, v_useNamesForExplicitOnly_1606_, v_mvarId_1602_, v___x_1628_, v_lctx_1607_, v_fvars_1608_, v___x_1609_, v_s_1610_, v_a_1622_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
return v___x_1629_;
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v_s_1610_);
lean_dec(v___x_1609_);
lean_dec_ref(v_fvars_1608_);
lean_dec_ref(v_lctx_1607_);
lean_dec(v_mvarId_1602_);
v_a_1630_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1621_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1621_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1638_ = lean_unsigned_to_nat(1u);
v___x_1639_ = lean_nat_add(v_n_1603_, v___x_1638_);
v___x_1640_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1604_, v___x_1605_, v_useNamesForExplicitOnly_1606_, v_mvarId_1602_, v___x_1639_, v_lctx_1607_, v_fvars_1608_, v___x_1609_, v_s_1610_, v___x_1618_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
return v___x_1640_;
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v_s_1610_);
lean_dec(v___x_1609_);
lean_dec_ref(v_fvars_1608_);
lean_dec_ref(v_lctx_1607_);
lean_dec(v_mvarId_1602_);
v_a_1643_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1616_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1616_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___boxed(lean_object* v_preserveBinderNames_1651_, lean_object* v___x_1652_, lean_object* v_useNamesForExplicitOnly_1653_, lean_object* v_mvarId_1654_, lean_object* v_i_1655_, lean_object* v_lctx_1656_, lean_object* v_fvars_1657_, lean_object* v_j_1658_, lean_object* v_s_1659_, lean_object* v_type_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1666_; uint8_t v___x_4290__boxed_1667_; uint8_t v_useNamesForExplicitOnly_boxed_1668_; lean_object* v_res_1669_; 
v_preserveBinderNames_boxed_1666_ = lean_unbox(v_preserveBinderNames_1651_);
v___x_4290__boxed_1667_ = lean_unbox(v___x_1652_);
v_useNamesForExplicitOnly_boxed_1668_ = lean_unbox(v_useNamesForExplicitOnly_1653_);
v_res_1669_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_boxed_1666_, v___x_4290__boxed_1667_, v_useNamesForExplicitOnly_boxed_1668_, v_mvarId_1654_, v_i_1655_, v_lctx_1656_, v_fvars_1657_, v_j_1658_, v_s_1659_, v_type_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___lam__0(lean_object* v_mvarId_1670_, lean_object* v___x_1671_, lean_object* v___x_1672_, uint8_t v_preserveBinderNames_1673_, uint8_t v___x_1674_, uint8_t v_useNamesForExplicitOnly_1675_, lean_object* v_n_1676_, lean_object* v_givenNames_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v___x_1683_; 
lean_inc(v_mvarId_1670_);
v___x_1683_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1670_, v___x_1671_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v___x_1684_; 
lean_dec_ref_known(v___x_1683_, 1);
lean_inc(v_mvarId_1670_);
v___x_1684_ = l_Lean_MVarId_getType(v_mvarId_1670_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v_lctx_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1685_);
lean_dec_ref_known(v___x_1684_, 1);
v_lctx_1686_ = lean_ctor_get(v___y_1678_, 2);
lean_inc_ref(v_lctx_1686_);
v___x_1687_ = lean_mk_empty_array_with_capacity(v___x_1672_);
v___x_1688_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1673_, v___x_1674_, v_useNamesForExplicitOnly_1675_, v_mvarId_1670_, v_n_1676_, v_lctx_1686_, v___x_1687_, v___x_1672_, v_givenNames_1677_, v_a_1685_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec_ref(v___y_1678_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1708_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1708_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1708_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v_fst_1693_; lean_object* v_snd_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1707_; 
v_fst_1693_ = lean_ctor_get(v_a_1689_, 0);
v_snd_1694_ = lean_ctor_get(v_a_1689_, 1);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_a_1689_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1696_ = v_a_1689_;
v_isShared_1697_ = v_isSharedCheck_1707_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_snd_1694_);
lean_inc(v_fst_1693_);
lean_dec(v_a_1689_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1707_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
size_t v_sz_1698_; size_t v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1702_; 
v_sz_1698_ = lean_array_size(v_fst_1693_);
v___x_1699_ = ((size_t)0ULL);
v___x_1700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(v_sz_1698_, v___x_1699_, v_fst_1693_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1700_);
v___x_1702_ = v___x_1696_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_snd_1694_);
v___x_1702_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1704_; 
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1702_);
v___x_1704_ = v___x_1691_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
v_a_1709_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1688_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1688_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec_ref(v___y_1678_);
lean_dec(v_givenNames_1677_);
lean_dec(v_n_1676_);
lean_dec(v___x_1672_);
lean_dec(v_mvarId_1670_);
v_a_1717_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1684_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1684_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec_ref(v___y_1678_);
lean_dec(v_givenNames_1677_);
lean_dec(v_n_1676_);
lean_dec(v___x_1672_);
lean_dec(v_mvarId_1670_);
v_a_1725_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1683_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1683_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___lam__0___boxed(lean_object* v_mvarId_1733_, lean_object* v___x_1734_, lean_object* v___x_1735_, lean_object* v_preserveBinderNames_1736_, lean_object* v___x_1737_, lean_object* v_useNamesForExplicitOnly_1738_, lean_object* v_n_1739_, lean_object* v_givenNames_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1746_; uint8_t v___x_4520__boxed_1747_; uint8_t v_useNamesForExplicitOnly_boxed_1748_; lean_object* v_res_1749_; 
v_preserveBinderNames_boxed_1746_ = lean_unbox(v_preserveBinderNames_1736_);
v___x_4520__boxed_1747_ = lean_unbox(v___x_1737_);
v_useNamesForExplicitOnly_boxed_1748_ = lean_unbox(v_useNamesForExplicitOnly_1738_);
v_res_1749_ = l_Lean_Meta_introNCore___lam__0(v_mvarId_1733_, v___x_1734_, v___x_1735_, v_preserveBinderNames_boxed_1746_, v___x_4520__boxed_1747_, v_useNamesForExplicitOnly_boxed_1748_, v_n_1739_, v_givenNames_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore(lean_object* v_mvarId_1752_, lean_object* v_n_1753_, lean_object* v_givenNames_1754_, uint8_t v_useNamesForExplicitOnly_1755_, uint8_t v_preserveBinderNames_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = lean_unsigned_to_nat(0u);
v___x_1763_ = lean_nat_dec_eq(v_n_1753_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v_options_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___f_1771_; lean_object* v___x_1772_; 
v_options_1764_ = lean_ctor_get(v_a_1759_, 2);
v___x_1765_ = l_Lean_Meta_tactic_hygienic;
v___x_1766_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v_options_1764_, v___x_1765_);
v___x_1767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
v___x_1768_ = lean_box(v_preserveBinderNames_1756_);
v___x_1769_ = lean_box(v___x_1766_);
v___x_1770_ = lean_box(v_useNamesForExplicitOnly_1755_);
lean_inc(v_mvarId_1752_);
v___f_1771_ = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1771_, 0, v_mvarId_1752_);
lean_closure_set(v___f_1771_, 1, v___x_1767_);
lean_closure_set(v___f_1771_, 2, v___x_1762_);
lean_closure_set(v___f_1771_, 3, v___x_1768_);
lean_closure_set(v___f_1771_, 4, v___x_1769_);
lean_closure_set(v___f_1771_, 5, v___x_1770_);
lean_closure_set(v___f_1771_, 6, v_n_1753_);
lean_closure_set(v___f_1771_, 7, v_givenNames_1754_);
v___x_1772_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_1752_, v___f_1771_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
return v___x_1772_;
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_dec(v_givenNames_1754_);
lean_dec(v_n_1753_);
v___x_1773_ = ((lean_object*)(l_Lean_Meta_introNCore___closed__0));
v___x_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
lean_ctor_set(v___x_1774_, 1, v_mvarId_1752_);
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___boxed(lean_object* v_mvarId_1776_, lean_object* v_n_1777_, lean_object* v_givenNames_1778_, lean_object* v_useNamesForExplicitOnly_1779_, lean_object* v_preserveBinderNames_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
uint8_t v_useNamesForExplicitOnly_boxed_1786_; uint8_t v_preserveBinderNames_boxed_1787_; lean_object* v_res_1788_; 
v_useNamesForExplicitOnly_boxed_1786_ = lean_unbox(v_useNamesForExplicitOnly_1779_);
v_preserveBinderNames_boxed_1787_ = lean_unbox(v_preserveBinderNames_1780_);
v_res_1788_ = l_Lean_Meta_introNCore(v_mvarId_1776_, v_n_1777_, v_givenNames_1778_, v_useNamesForExplicitOnly_boxed_1786_, v_preserveBinderNames_boxed_1787_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(lean_object* v_00_u03b1_1789_, lean_object* v_lctx_1790_, lean_object* v_x_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1790_, v_x_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1798_, lean_object* v_lctx_1799_, lean_object* v_x_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(v_00_u03b1_1798_, v_lctx_1799_, v_x_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(lean_object* v_e_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_1807_, v___y_1809_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___boxed(lean_object* v_e_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(v_e_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(lean_object* v_mvarId_1821_, lean_object* v_val_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1821_, v_val_1822_, v___y_1824_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___boxed(lean_object* v_mvarId_1829_, lean_object* v_val_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(v_mvarId_1829_, v_val_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1837_, lean_object* v_fvars_1838_, lean_object* v_j_1839_, lean_object* v_x_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1838_, v_j_1839_, v_x_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1847_, lean_object* v_fvars_1848_, lean_object* v_j_1849_, lean_object* v_x_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(v_00_u03b1_1847_, v_fvars_1848_, v_j_1849_, v_x_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1860_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___boxed(lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1869_, lean_object* v_x_1870_, lean_object* v_x_1871_, lean_object* v_x_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(v_x_1870_, v_x_1871_, v_x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1874_, lean_object* v_x_1875_, size_t v_x_1876_, size_t v_x_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1875_, v_x_1876_, v_x_1877_, v_x_1878_, v_x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1881_, lean_object* v_x_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_){
_start:
{
size_t v_x_4771__boxed_1887_; size_t v_x_4772__boxed_1888_; lean_object* v_res_1889_; 
v_x_4771__boxed_1887_ = lean_unbox_usize(v_x_1883_);
lean_dec(v_x_1883_);
v_x_4772__boxed_1888_ = lean_unbox_usize(v_x_1884_);
lean_dec(v_x_1884_);
v_res_1889_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1881_, v_x_1882_, v_x_4771__boxed_1887_, v_x_4772__boxed_1888_, v_x_1885_, v_x_1886_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11(lean_object* v_00_u03b2_1890_, lean_object* v_n_1891_, lean_object* v_k_1892_, lean_object* v_v_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(v_n_1891_, v_k_1892_, v_v_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(lean_object* v_00_u03b2_1895_, size_t v_depth_1896_, lean_object* v_keys_1897_, lean_object* v_vals_1898_, lean_object* v_heq_1899_, lean_object* v_i_1900_, lean_object* v_entries_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_1896_, v_keys_1897_, v_vals_1898_, v_i_1900_, v_entries_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_1903_, lean_object* v_depth_1904_, lean_object* v_keys_1905_, lean_object* v_vals_1906_, lean_object* v_heq_1907_, lean_object* v_i_1908_, lean_object* v_entries_1909_){
_start:
{
size_t v_depth_boxed_1910_; lean_object* v_res_1911_; 
v_depth_boxed_1910_ = lean_unbox_usize(v_depth_1904_);
lean_dec(v_depth_1904_);
v_res_1911_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(v_00_u03b2_1903_, v_depth_boxed_1910_, v_keys_1905_, v_vals_1906_, v_heq_1907_, v_i_1908_, v_entries_1909_);
lean_dec_ref(v_vals_1906_);
lean_dec_ref(v_keys_1905_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1912_, lean_object* v_x_1913_, lean_object* v_x_1914_, lean_object* v_x_1915_, lean_object* v_x_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(v_x_1913_, v_x_1914_, v_x_1915_, v_x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introN(lean_object* v_mvarId_1918_, lean_object* v_n_1919_, lean_object* v_givenNames_1920_, uint8_t v_useNamesForExplicitOnly_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
uint8_t v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = 0;
v___x_1928_ = l_Lean_Meta_introNCore(v_mvarId_1918_, v_n_1919_, v_givenNames_1920_, v_useNamesForExplicitOnly_1921_, v___x_1927_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introN___boxed(lean_object* v_mvarId_1929_, lean_object* v_n_1930_, lean_object* v_givenNames_1931_, lean_object* v_useNamesForExplicitOnly_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
uint8_t v_useNamesForExplicitOnly_boxed_1938_; lean_object* v_res_1939_; 
v_useNamesForExplicitOnly_boxed_1938_ = lean_unbox(v_useNamesForExplicitOnly_1932_);
v_res_1939_ = l_Lean_MVarId_introN(v_mvarId_1929_, v_n_1930_, v_givenNames_1931_, v_useNamesForExplicitOnly_boxed_1938_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introNP(lean_object* v_mvarId_1940_, lean_object* v_n_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v___x_1947_; uint8_t v___x_1948_; uint8_t v___x_1949_; lean_object* v___x_1950_; 
v___x_1947_ = lean_box(0);
v___x_1948_ = 0;
v___x_1949_ = 1;
v___x_1950_ = l_Lean_Meta_introNCore(v_mvarId_1940_, v_n_1941_, v___x_1947_, v___x_1948_, v___x_1949_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introNP___boxed(lean_object* v_mvarId_1951_, lean_object* v_n_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_MVarId_introNP(v_mvarId_1951_, v_n_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro(lean_object* v_mvarId_1959_, lean_object* v_name_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; 
v___x_1966_ = lean_unsigned_to_nat(1u);
v___x_1967_ = lean_box(0);
v___x_1968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1968_, 0, v_name_1960_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = 0;
v___x_1970_ = l_Lean_Meta_introNCore(v_mvarId_1959_, v___x_1966_, v___x_1968_, v___x_1969_, v___x_1969_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1990_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_1990_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1990_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_fst_1975_; lean_object* v_snd_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1989_; 
v_fst_1975_ = lean_ctor_get(v_a_1971_, 0);
v_snd_1976_ = lean_ctor_get(v_a_1971_, 1);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_a_1971_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1978_ = v_a_1971_;
v_isShared_1979_ = v_isSharedCheck_1989_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_snd_1976_);
lean_inc(v_fst_1975_);
lean_dec(v_a_1971_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1989_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1980_ = lean_box(0);
v___x_1981_ = lean_unsigned_to_nat(0u);
v___x_1982_ = lean_array_get(v___x_1980_, v_fst_1975_, v___x_1981_);
lean_dec(v_fst_1975_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1982_);
v___x_1984_ = v___x_1978_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_snd_1976_);
v___x_1984_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1986_; 
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1984_);
v___x_1986_ = v___x_1973_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
v_a_1991_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1970_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1970_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro___boxed(lean_object* v_mvarId_1999_, lean_object* v_name_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_MVarId_intro(v_mvarId_1999_, v_name_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core(lean_object* v_mvarId_2007_, uint8_t v_preserveBinderNames_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; lean_object* v___x_2017_; 
v___x_2014_ = lean_unsigned_to_nat(1u);
v___x_2015_ = lean_box(0);
v___x_2016_ = 0;
v___x_2017_ = l_Lean_Meta_introNCore(v_mvarId_2007_, v___x_2014_, v___x_2015_, v___x_2016_, v_preserveBinderNames_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2037_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2037_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2037_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v_fst_2022_; lean_object* v_snd_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2036_; 
v_fst_2022_ = lean_ctor_get(v_a_2018_, 0);
v_snd_2023_ = lean_ctor_get(v_a_2018_, 1);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_a_2018_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2025_ = v_a_2018_;
v_isShared_2026_ = v_isSharedCheck_2036_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_snd_2023_);
lean_inc(v_fst_2022_);
lean_dec(v_a_2018_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2036_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2027_ = lean_box(0);
v___x_2028_ = lean_unsigned_to_nat(0u);
v___x_2029_ = lean_array_get(v___x_2027_, v_fst_2022_, v___x_2028_);
lean_dec(v_fst_2022_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2029_);
v___x_2031_ = v___x_2025_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_snd_2023_);
v___x_2031_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2033_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2031_);
v___x_2033_ = v___x_2020_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
v_a_2038_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2017_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2017_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core___boxed(lean_object* v_mvarId_2046_, lean_object* v_preserveBinderNames_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
uint8_t v_preserveBinderNames_boxed_2053_; lean_object* v_res_2054_; 
v_preserveBinderNames_boxed_2053_ = lean_unbox(v_preserveBinderNames_2047_);
v_res_2054_ = l_Lean_Meta_intro1Core(v_mvarId_2046_, v_preserveBinderNames_boxed_2053_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1(lean_object* v_mvarId_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
uint8_t v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = 0;
v___x_2062_ = l_Lean_Meta_intro1Core(v_mvarId_2055_, v___x_2061_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___boxed(lean_object* v_mvarId_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_MVarId_intro1(v_mvarId_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1P(lean_object* v_mvarId_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
uint8_t v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = 1;
v___x_2077_ = l_Lean_Meta_intro1Core(v_mvarId_2070_, v___x_2076_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1P___boxed(lean_object* v_mvarId_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_MVarId_intro1P(v_mvarId_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(lean_object* v_msgData_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___x_2091_; lean_object* v_env_2092_; lean_object* v___x_2093_; lean_object* v_mctx_2094_; lean_object* v_lctx_2095_; lean_object* v_options_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2091_ = lean_st_ref_get(v___y_2089_);
v_env_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc_ref(v_env_2092_);
lean_dec(v___x_2091_);
v___x_2093_ = lean_st_ref_get(v___y_2087_);
v_mctx_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc_ref(v_mctx_2094_);
lean_dec(v___x_2093_);
v_lctx_2095_ = lean_ctor_get(v___y_2086_, 2);
v_options_2096_ = lean_ctor_get(v___y_2088_, 2);
lean_inc_ref(v_options_2096_);
lean_inc_ref(v_lctx_2095_);
v___x_2097_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2097_, 0, v_env_2092_);
lean_ctor_set(v___x_2097_, 1, v_mctx_2094_);
lean_ctor_set(v___x_2097_, 2, v_lctx_2095_);
lean_ctor_set(v___x_2097_, 3, v_options_2096_);
v___x_2098_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v_msgData_2085_);
v___x_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0___boxed(lean_object* v_msgData_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msgData_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(lean_object* v_msg_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_ref_2113_; lean_object* v___x_2114_; lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2123_; 
v_ref_2113_ = lean_ctor_get(v___y_2110_, 5);
v___x_2114_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msg_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2123_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2123_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
lean_inc(v_ref_2113_);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v_ref_2113_);
lean_ctor_set(v___x_2119_, 1, v_a_2115_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set_tag(v___x_2117_, 1);
lean_ctor_set(v___x_2117_, 0, v___x_2119_);
v___x_2121_ = v___x_2117_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg___boxed(lean_object* v_msg_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v_msg_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
return v_res_2130_;
}
}
static lean_object* _init_l_Lean_MVarId_intro1___00__lam__0___closed__1(void){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = ((lean_object*)(l_Lean_MVarId_intro1___00__lam__0___closed__0));
v___x_2133_ = l_Lean_stringToMessageData(v___x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__lam__0(lean_object* v_mvarId_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; 
lean_inc(v_mvarId_2134_);
v___x_2140_ = l_Lean_MVarId_getType_x27(v_mvarId_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
if (lean_obj_tag(v_a_2141_) == 7)
{
lean_object* v_binderName_2142_; lean_object* v_binderType_2143_; lean_object* v_body_2144_; uint8_t v_binderInfo_2145_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; uint8_t v___x_2182_; 
v_binderName_2142_ = lean_ctor_get(v_a_2141_, 0);
lean_inc(v_binderName_2142_);
v_binderType_2143_ = lean_ctor_get(v_a_2141_, 1);
lean_inc_ref(v_binderType_2143_);
v_body_2144_ = lean_ctor_get(v_a_2141_, 2);
lean_inc_ref(v_body_2144_);
v_binderInfo_2145_ = lean_ctor_get_uint8(v_a_2141_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_2141_, 3);
v___x_2182_ = l_Lean_Expr_hasLooseBVars(v_body_2144_);
if (v___x_2182_ == 0)
{
v___y_2147_ = v___y_2135_;
v___y_2148_ = v___y_2136_;
v___y_2149_ = v___y_2137_;
v___y_2150_ = v___y_2138_;
goto v___jp_2146_;
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec_ref(v_body_2144_);
lean_dec_ref(v_binderType_2143_);
lean_dec(v_binderName_2142_);
v___x_2183_ = lean_obj_once(&l_Lean_MVarId_intro1___00__lam__0___closed__1, &l_Lean_MVarId_intro1___00__lam__0___closed__1_once, _init_l_Lean_MVarId_intro1___00__lam__0___closed__1);
v___x_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2184_, 0, v_mvarId_2134_);
v___x_2185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2183_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v___x_2185_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2186_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2186_);
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
v___jp_2146_:
{
lean_object* v___x_2151_; 
lean_inc(v_mvarId_2134_);
v___x_2151_ = l_Lean_MVarId_getTag(v_mvarId_2134_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2153_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2151_, 1);
v___x_2153_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_body_2144_, v_a_2152_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2164_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc_n(v_a_2154_, 2);
lean_dec_ref_known(v___x_2153_, 1);
v___x_2155_ = l_Lean_Expr_lam___override(v_binderName_2142_, v_binderType_2143_, v_a_2154_, v_binderInfo_2145_);
v___x_2156_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_2134_, v___x_2155_, v___y_2148_);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; 
v_unused_2165_ = lean_ctor_get(v___x_2156_, 0);
lean_dec(v_unused_2165_);
v___x_2158_ = v___x_2156_;
v_isShared_2159_ = v_isSharedCheck_2164_;
goto v_resetjp_2157_;
}
else
{
lean_dec(v___x_2156_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2164_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2160_ = l_Lean_Expr_mvarId_x21(v_a_2154_);
lean_dec(v_a_2154_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2160_);
v___x_2162_ = v___x_2158_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec_ref(v_binderType_2143_);
lean_dec(v_binderName_2142_);
lean_dec(v_mvarId_2134_);
v_a_2166_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2153_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2153_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec_ref(v_body_2144_);
lean_dec_ref(v_binderType_2143_);
lean_dec(v_binderName_2142_);
lean_dec(v_mvarId_2134_);
v_a_2174_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2151_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2151_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
else
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_dec(v_a_2141_);
v___x_2195_ = lean_obj_once(&l_Lean_MVarId_intro1___00__lam__0___closed__1, &l_Lean_MVarId_intro1___00__lam__0___closed__1_once, _init_l_Lean_MVarId_intro1___00__lam__0___closed__1);
v___x_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2196_, 0, v_mvarId_2134_);
v___x_2197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v___x_2197_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
return v___x_2198_;
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec(v_mvarId_2134_);
v_a_2199_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2140_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2140_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__lam__0___boxed(lean_object* v_mvarId_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Lean_MVarId_intro1___00__lam__0(v_mvarId_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1__(lean_object* v_mvarId_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v___f_2220_; lean_object* v___x_2221_; 
lean_inc(v_mvarId_2214_);
v___f_2220_ = lean_alloc_closure((void*)(l_Lean_MVarId_intro1___00__lam__0___boxed), 6, 1);
lean_closure_set(v___f_2220_, 0, v_mvarId_2214_);
v___x_2221_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_2214_, v___f_2220_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__boxed(lean_object* v_mvarId_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_MVarId_intro1__(v_mvarId_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(lean_object* v_00_u03b1_2229_, lean_object* v_msg_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v_msg_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___boxed(lean_object* v_00_u03b1_2237_, lean_object* v_msg_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(v_00_u03b1_2237_, v_msg_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntrosSize(lean_object* v_x_2245_){
_start:
{
switch(lean_obj_tag(v_x_2245_))
{
case 7:
{
lean_object* v_body_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v_body_2246_ = lean_ctor_get(v_x_2245_, 2);
v___x_2247_ = l_Lean_Meta_getIntrosSize(v_body_2246_);
v___x_2248_ = lean_unsigned_to_nat(1u);
v___x_2249_ = lean_nat_add(v___x_2247_, v___x_2248_);
lean_dec(v___x_2247_);
return v___x_2249_;
}
case 8:
{
lean_object* v_body_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v_body_2250_ = lean_ctor_get(v_x_2245_, 3);
v___x_2251_ = l_Lean_Meta_getIntrosSize(v_body_2250_);
v___x_2252_ = lean_unsigned_to_nat(1u);
v___x_2253_ = lean_nat_add(v___x_2251_, v___x_2252_);
lean_dec(v___x_2251_);
return v___x_2253_;
}
case 10:
{
lean_object* v_expr_2254_; 
v_expr_2254_ = lean_ctor_get(v_x_2245_, 1);
v_x_2245_ = v_expr_2254_;
goto _start;
}
default: 
{
lean_object* v___x_2256_; 
v___x_2256_ = lean_unsigned_to_nat(0u);
return v___x_2256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntrosSize___boxed(lean_object* v_x_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_Meta_getIntrosSize(v_x_2257_);
lean_dec_ref(v_x_2257_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intros(lean_object* v_mvarId_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v___x_2265_; 
lean_inc(v_mvarId_2259_);
v___x_2265_ = l_Lean_MVarId_getType(v_mvarId_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2267_; lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2282_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v___x_2265_, 1);
v___x_2267_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_a_2266_, v_a_2261_);
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2270_ = v___x_2267_;
v_isShared_2271_ = v_isSharedCheck_2282_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2267_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2282_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2272_ = l_Lean_Meta_getIntrosSize(v_a_2268_);
lean_dec(v_a_2268_);
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = lean_nat_dec_eq(v___x_2272_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
lean_del_object(v___x_2270_);
v___x_2275_ = lean_box(0);
v___x_2276_ = l_Lean_Meta_introNCore(v_mvarId_2259_, v___x_2272_, v___x_2275_, v___x_2274_, v___x_2274_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
return v___x_2276_;
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2280_; 
lean_dec(v___x_2272_);
v___x_2277_ = ((lean_object*)(l_Lean_Meta_introNCore___closed__0));
v___x_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v_mvarId_2259_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 0, v___x_2278_);
v___x_2280_ = v___x_2270_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec(v_mvarId_2259_);
v_a_2283_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2265_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2265_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intros___boxed(lean_object* v_mvarId_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_MVarId_intros(v_mvarId_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
return v_res_2297_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_tactic_hygienic = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_tactic_hygienic);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Intro(builtin);
}
#ifdef __cplusplus
}
#endif
