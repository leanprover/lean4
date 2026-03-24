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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "hygienic"};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(106, 53, 183, 57, 182, 192, 14, 150)}};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "make sure tactics are hygienic"};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 82, 89, 96, 183, 68, 254, 125)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(179, 184, 241, 48, 181, 222, 216, 48)}};
static const lean_object* l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tactic_hygienic;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2;
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
lean_dec_ref(v___x_11_);
v___x_13_ = l_Lean_Expr_headBeta(v_type_2_);
v___x_14_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_13_, v_a_12_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v_a_15_; uint8_t v___x_16_; uint8_t v___x_17_; lean_object* v___x_18_; 
v_a_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc(v_a_15_);
lean_dec_ref(v___x_14_);
v___x_16_ = 0;
v___x_17_ = 1;
lean_inc(v_a_15_);
v___x_18_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3_, v_a_15_, v___x_16_, v_isZero_4_, v___x_16_, v_isZero_4_, v___x_17_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_1533__overap_20_; lean_object* v___x_21_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_a_19_);
lean_dec_ref(v___x_18_);
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
lean_object* v___x_128_; lean_object* v_toApplicative_129_; lean_object* v_toFunctor_130_; lean_object* v_toSeq_131_; lean_object* v_toSeqLeft_132_; lean_object* v_toSeqRight_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_303_; 
v___x_128_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
v_toApplicative_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc_ref(v_toApplicative_129_);
v_toFunctor_130_ = lean_ctor_get(v_toApplicative_129_, 0);
v_toSeq_131_ = lean_ctor_get(v_toApplicative_129_, 2);
v_toSeqLeft_132_ = lean_ctor_get(v_toApplicative_129_, 3);
v_toSeqRight_133_ = lean_ctor_get(v_toApplicative_129_, 4);
v_isSharedCheck_303_ = !lean_is_exclusive(v_toApplicative_129_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; 
v_unused_304_ = lean_ctor_get(v_toApplicative_129_, 1);
lean_dec(v_unused_304_);
v___x_135_ = v_toApplicative_129_;
v_isShared_136_ = v_isSharedCheck_303_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_toSeqRight_133_);
lean_inc(v_toSeqLeft_132_);
lean_inc(v_toSeq_131_);
lean_inc(v_toFunctor_130_);
lean_dec(v_toApplicative_129_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_303_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___x_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___x_146_; 
v___f_137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2));
v___f_138_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3));
lean_inc_ref(v_toFunctor_130_);
v___f_139_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_139_, 0, v_toFunctor_130_);
v___f_140_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_140_, 0, v_toFunctor_130_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v___f_139_);
lean_ctor_set(v___x_141_, 1, v___f_140_);
v___f_142_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_142_, 0, v_toSeqRight_133_);
v___f_143_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_143_, 0, v_toSeqLeft_132_);
v___f_144_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_144_, 0, v_toSeq_131_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 4, v___f_142_);
lean_ctor_set(v___x_135_, 3, v___f_143_);
lean_ctor_set(v___x_135_, 2, v___f_144_);
lean_ctor_set(v___x_135_, 1, v___f_137_);
lean_ctor_set(v___x_135_, 0, v___x_141_);
v___x_146_ = v___x_135_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v___f_137_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v___f_144_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v___f_143_);
lean_ctor_set(v_reuseFailAlloc_302_, 4, v___f_142_);
v___x_146_ = v_reuseFailAlloc_302_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v_toApplicative_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_300_; 
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___f_138_);
v___x_148_ = l_StateRefT_x27_instMonad___redArg(v___x_147_);
v___x_149_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_149_, 0, lean_box(0));
lean_closure_set(v___x_149_, 1, lean_box(0));
lean_closure_set(v___x_149_, 2, v___x_148_);
v___x_150_ = l_instMonadControlTOfPure___redArg(v___x_149_);
v_toApplicative_151_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; 
v_unused_301_ = lean_ctor_get(v___x_128_, 1);
lean_dec(v_unused_301_);
v___x_153_ = v___x_128_;
v_isShared_154_ = v_isSharedCheck_300_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_toApplicative_151_);
lean_dec(v___x_128_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_300_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v_toFunctor_155_; lean_object* v_toSeq_156_; lean_object* v_toSeqLeft_157_; lean_object* v_toSeqRight_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_298_; 
v_toFunctor_155_ = lean_ctor_get(v_toApplicative_151_, 0);
v_toSeq_156_ = lean_ctor_get(v_toApplicative_151_, 2);
v_toSeqLeft_157_ = lean_ctor_get(v_toApplicative_151_, 3);
v_toSeqRight_158_ = lean_ctor_get(v_toApplicative_151_, 4);
v_isSharedCheck_298_ = !lean_is_exclusive(v_toApplicative_151_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; 
v_unused_299_ = lean_ctor_get(v_toApplicative_151_, 1);
lean_dec(v_unused_299_);
v___x_160_ = v_toApplicative_151_;
v_isShared_161_ = v_isSharedCheck_298_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_toSeqRight_158_);
lean_inc(v_toSeqLeft_157_);
lean_inc(v_toSeq_156_);
lean_inc(v_toFunctor_155_);
lean_dec(v_toApplicative_151_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_298_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___x_164_; lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___x_169_; 
lean_inc_ref(v_toFunctor_155_);
v___f_162_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_162_, 0, v_toFunctor_155_);
v___f_163_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_163_, 0, v_toFunctor_155_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v___f_162_);
lean_ctor_set(v___x_164_, 1, v___f_163_);
v___f_165_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_165_, 0, v_toSeqRight_158_);
v___f_166_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_166_, 0, v_toSeqLeft_157_);
v___f_167_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_167_, 0, v_toSeq_156_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 4, v___f_165_);
lean_ctor_set(v___x_160_, 3, v___f_166_);
lean_ctor_set(v___x_160_, 2, v___f_167_);
lean_ctor_set(v___x_160_, 1, v___f_137_);
lean_ctor_set(v___x_160_, 0, v___x_164_);
v___x_169_ = v___x_160_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___f_137_);
lean_ctor_set(v_reuseFailAlloc_297_, 2, v___f_167_);
lean_ctor_set(v_reuseFailAlloc_297_, 3, v___f_166_);
lean_ctor_set(v_reuseFailAlloc_297_, 4, v___f_165_);
v___x_169_ = v_reuseFailAlloc_297_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_171_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v___f_138_);
lean_ctor_set(v___x_153_, 0, v___x_169_);
v___x_171_ = v___x_153_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v___f_138_);
v___x_171_ = v_reuseFailAlloc_296_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_172_; lean_object* v_toApplicative_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_294_; 
v___x_172_ = l_StateRefT_x27_instMonad___redArg(v___x_171_);
v_toApplicative_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v___x_172_, 1);
lean_dec(v_unused_295_);
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_294_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_toApplicative_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_294_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v_toFunctor_177_; lean_object* v_toSeq_178_; lean_object* v_toSeqLeft_179_; lean_object* v_toSeqRight_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_292_; 
v_toFunctor_177_ = lean_ctor_get(v_toApplicative_173_, 0);
v_toSeq_178_ = lean_ctor_get(v_toApplicative_173_, 2);
v_toSeqLeft_179_ = lean_ctor_get(v_toApplicative_173_, 3);
v_toSeqRight_180_ = lean_ctor_get(v_toApplicative_173_, 4);
v_isSharedCheck_292_ = !lean_is_exclusive(v_toApplicative_173_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; 
v_unused_293_ = lean_ctor_get(v_toApplicative_173_, 1);
lean_dec(v_unused_293_);
v___x_182_ = v_toApplicative_173_;
v_isShared_183_ = v_isSharedCheck_292_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_toSeqRight_180_);
lean_inc(v_toSeqLeft_179_);
lean_inc(v_toSeq_178_);
lean_inc(v_toFunctor_177_);
lean_dec(v_toApplicative_173_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_292_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___f_184_; lean_object* v___f_185_; lean_object* v___f_186_; lean_object* v___f_187_; lean_object* v___x_188_; lean_object* v___f_189_; lean_object* v___f_190_; lean_object* v___f_191_; lean_object* v___x_193_; 
v___f_184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4));
v___f_185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5));
lean_inc_ref(v_toFunctor_177_);
v___f_186_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_186_, 0, v_toFunctor_177_);
v___f_187_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_187_, 0, v_toFunctor_177_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___f_186_);
lean_ctor_set(v___x_188_, 1, v___f_187_);
v___f_189_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_189_, 0, v_toSeqRight_180_);
v___f_190_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_190_, 0, v_toSeqLeft_179_);
v___f_191_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_191_, 0, v_toSeq_178_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 4, v___f_189_);
lean_ctor_set(v___x_182_, 3, v___f_190_);
lean_ctor_set(v___x_182_, 2, v___f_191_);
lean_ctor_set(v___x_182_, 1, v___f_184_);
lean_ctor_set(v___x_182_, 0, v___x_188_);
v___x_193_ = v___x_182_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v___f_184_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v___f_191_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v___f_190_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v___f_189_);
v___x_193_ = v_reuseFailAlloc_291_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_195_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___f_185_);
lean_ctor_set(v___x_175_, 0, v___x_193_);
v___x_195_ = v___x_175_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v___f_185_);
v___x_195_ = v_reuseFailAlloc_290_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v_zero_198_; uint8_t v_isZero_199_; 
v___x_196_ = l_Lean_Meta_instMonadMCtxMetaM;
v___x_197_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9);
v_zero_198_ = lean_unsigned_to_nat(0u);
v_isZero_199_ = lean_nat_dec_eq(v_i_117_, v_zero_198_);
if (v_isZero_199_ == 1)
{
lean_object* v___x_200_; lean_object* v_type_201_; lean_object* v___x_202_; lean_object* v___f_203_; lean_object* v___x_204_; lean_object* v___x_1284__overap_205_; lean_object* v___x_206_; 
lean_dec(v_s_121_);
lean_dec(v_i_117_);
lean_dec_ref(v_mkName_116_);
v___x_200_ = lean_array_get_size(v_fvars_119_);
v_type_201_ = lean_expr_instantiate_rev_range(v_type_122_, v_j_120_, v___x_200_, v_fvars_119_);
lean_dec_ref(v_type_122_);
v___x_202_ = lean_box(v_isZero_199_);
lean_inc_ref(v_fvars_119_);
v___f_203_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_203_, 0, v_mvarId_115_);
lean_closure_set(v___f_203_, 1, v_type_201_);
lean_closure_set(v___f_203_, 2, v_fvars_119_);
lean_closure_set(v___f_203_, 3, v___x_202_);
lean_closure_set(v___f_203_, 4, v___x_196_);
lean_inc_ref(v___x_195_);
lean_inc_ref(v___x_150_);
v___x_204_ = l_Lean_Meta_withNewLocalInstances___redArg(v___x_150_, v___x_195_, v_fvars_119_, v_j_120_, v___f_203_);
v___x_1284__overap_205_ = l_Lean_Meta_withLCtx_x27___redArg(v___x_150_, v___x_195_, v_lctx_118_, v___x_204_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
v___x_206_ = lean_apply_5(v___x_1284__overap_205_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
return v___x_206_;
}
else
{
lean_object* v_one_207_; lean_object* v_n_208_; 
v_one_207_ = lean_unsigned_to_nat(1u);
v_n_208_ = lean_nat_sub(v_i_117_, v_one_207_);
lean_dec(v_i_117_);
switch(lean_obj_tag(v_type_122_))
{
case 8:
{
lean_object* v_declName_209_; lean_object* v_type_210_; lean_object* v_value_211_; lean_object* v_body_212_; lean_object* v___x_1314__overap_213_; lean_object* v___x_214_; 
lean_dec_ref(v___x_150_);
v_declName_209_ = lean_ctor_get(v_type_122_, 0);
lean_inc(v_declName_209_);
v_type_210_ = lean_ctor_get(v_type_122_, 1);
lean_inc_ref(v_type_210_);
v_value_211_ = lean_ctor_get(v_type_122_, 2);
lean_inc_ref(v_value_211_);
v_body_212_ = lean_ctor_get(v_type_122_, 3);
lean_inc_ref(v_body_212_);
lean_dec_ref(v_type_122_);
v___x_1314__overap_213_ = l_Lean_mkFreshFVarId___redArg(v___x_195_, v___x_197_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
v___x_214_ = lean_apply_5(v___x_1314__overap_213_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_a_215_);
lean_dec_ref(v___x_214_);
v___x_216_ = 1;
v___x_217_ = lean_box(v___x_216_);
lean_inc_ref(v_mkName_116_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
lean_inc_ref(v_lctx_118_);
v___x_218_ = lean_apply_9(v_mkName_116_, v_lctx_118_, v_declName_209_, v___x_217_, v_s_121_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v_fst_220_; lean_object* v_snd_221_; lean_object* v___x_222_; lean_object* v_type_223_; lean_object* v_type_224_; lean_object* v_val_225_; uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref(v___x_218_);
v_fst_220_ = lean_ctor_get(v_a_219_, 0);
lean_inc(v_fst_220_);
v_snd_221_ = lean_ctor_get(v_a_219_, 1);
lean_inc(v_snd_221_);
lean_dec(v_a_219_);
v___x_222_ = lean_array_get_size(v_fvars_119_);
v_type_223_ = lean_expr_instantiate_rev_range(v_type_210_, v_j_120_, v___x_222_, v_fvars_119_);
lean_dec_ref(v_type_210_);
v_type_224_ = l_Lean_Expr_headBeta(v_type_223_);
v_val_225_ = lean_expr_instantiate_rev_range(v_value_211_, v_j_120_, v___x_222_, v_fvars_119_);
lean_dec_ref(v_value_211_);
v___x_226_ = 0;
lean_inc(v_a_215_);
v___x_227_ = l_Lean_LocalContext_mkLetDecl(v_lctx_118_, v_a_215_, v_fst_220_, v_type_224_, v_val_225_, v_isZero_199_, v___x_226_);
v___x_228_ = l_Lean_mkFVar(v_a_215_);
v___x_229_ = lean_array_push(v_fvars_119_, v___x_228_);
v_i_117_ = v_n_208_;
v_lctx_118_ = v___x_227_;
v_fvars_119_ = v___x_229_;
v_s_121_ = v_snd_221_;
v_type_122_ = v_body_212_;
goto _start;
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec(v_a_215_);
lean_dec_ref(v_body_212_);
lean_dec_ref(v_value_211_);
lean_dec_ref(v_type_210_);
lean_dec(v_n_208_);
lean_dec(v_j_120_);
lean_dec_ref(v_fvars_119_);
lean_dec_ref(v_lctx_118_);
lean_dec_ref(v_mkName_116_);
lean_dec(v_mvarId_115_);
v_a_231_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_218_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_218_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec_ref(v_body_212_);
lean_dec_ref(v_value_211_);
lean_dec_ref(v_type_210_);
lean_dec(v_declName_209_);
lean_dec(v_n_208_);
lean_dec(v_s_121_);
lean_dec(v_j_120_);
lean_dec_ref(v_fvars_119_);
lean_dec_ref(v_lctx_118_);
lean_dec_ref(v_mkName_116_);
lean_dec(v_mvarId_115_);
v_a_239_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_214_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_214_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
case 7:
{
lean_object* v_binderName_247_; lean_object* v_binderType_248_; lean_object* v_body_249_; uint8_t v_binderInfo_250_; lean_object* v___x_1363__overap_251_; lean_object* v___x_252_; 
lean_dec_ref(v___x_150_);
v_binderName_247_ = lean_ctor_get(v_type_122_, 0);
lean_inc(v_binderName_247_);
v_binderType_248_ = lean_ctor_get(v_type_122_, 1);
lean_inc_ref(v_binderType_248_);
v_body_249_ = lean_ctor_get(v_type_122_, 2);
lean_inc_ref(v_body_249_);
v_binderInfo_250_ = lean_ctor_get_uint8(v_type_122_, sizeof(void*)*3 + 8);
lean_dec_ref(v_type_122_);
v___x_1363__overap_251_ = l_Lean_mkFreshFVarId___redArg(v___x_195_, v___x_197_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
v___x_252_ = lean_apply_5(v___x_1363__overap_251_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; uint8_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref(v___x_252_);
v___x_254_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_250_);
v___x_255_ = lean_box(v___x_254_);
lean_inc_ref(v_mkName_116_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
lean_inc_ref(v_lctx_118_);
v___x_256_ = lean_apply_9(v_mkName_116_, v_lctx_118_, v_binderName_247_, v___x_255_, v_s_121_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v_fst_258_; lean_object* v_snd_259_; lean_object* v___x_260_; lean_object* v_type_261_; lean_object* v_type_262_; uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_257_);
lean_dec_ref(v___x_256_);
v_fst_258_ = lean_ctor_get(v_a_257_, 0);
lean_inc(v_fst_258_);
v_snd_259_ = lean_ctor_get(v_a_257_, 1);
lean_inc(v_snd_259_);
lean_dec(v_a_257_);
v___x_260_ = lean_array_get_size(v_fvars_119_);
v_type_261_ = lean_expr_instantiate_rev_range(v_binderType_248_, v_j_120_, v___x_260_, v_fvars_119_);
lean_dec_ref(v_binderType_248_);
v_type_262_ = l_Lean_Expr_headBeta(v_type_261_);
v___x_263_ = 0;
lean_inc(v_a_253_);
v___x_264_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_118_, v_a_253_, v_fst_258_, v_type_262_, v_binderInfo_250_, v___x_263_);
v___x_265_ = l_Lean_mkFVar(v_a_253_);
v___x_266_ = lean_array_push(v_fvars_119_, v___x_265_);
v_i_117_ = v_n_208_;
v_lctx_118_ = v___x_264_;
v_fvars_119_ = v___x_266_;
v_s_121_ = v_snd_259_;
v_type_122_ = v_body_249_;
goto _start;
}
else
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
lean_dec(v_a_253_);
lean_dec_ref(v_body_249_);
lean_dec_ref(v_binderType_248_);
lean_dec(v_n_208_);
lean_dec(v_j_120_);
lean_dec_ref(v_fvars_119_);
lean_dec_ref(v_lctx_118_);
lean_dec_ref(v_mkName_116_);
lean_dec(v_mvarId_115_);
v_a_268_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_256_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_256_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref(v_body_249_);
lean_dec_ref(v_binderType_248_);
lean_dec(v_binderName_247_);
lean_dec(v_n_208_);
lean_dec(v_s_121_);
lean_dec(v_j_120_);
lean_dec_ref(v_fvars_119_);
lean_dec_ref(v_lctx_118_);
lean_dec_ref(v_mkName_116_);
lean_dec(v_mvarId_115_);
v_a_276_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_252_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_252_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
default: 
{
lean_object* v___x_284_; lean_object* v_type_285_; lean_object* v___f_286_; lean_object* v___x_287_; lean_object* v___x_1437__overap_288_; lean_object* v___x_289_; 
v___x_284_ = lean_array_get_size(v_fvars_119_);
v_type_285_ = lean_expr_instantiate_rev_range(v_type_122_, v_j_120_, v___x_284_, v_fvars_119_);
lean_dec_ref(v_type_122_);
lean_inc_ref(v_fvars_119_);
lean_inc_ref(v_lctx_118_);
lean_inc_ref(v___x_195_);
v___f_286_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___boxed), 15, 10);
lean_closure_set(v___f_286_, 0, v___x_195_);
lean_closure_set(v___f_286_, 1, v___x_196_);
lean_closure_set(v___f_286_, 2, v_type_285_);
lean_closure_set(v___f_286_, 3, v_mvarId_115_);
lean_closure_set(v___f_286_, 4, v_n_208_);
lean_closure_set(v___f_286_, 5, v_mkName_116_);
lean_closure_set(v___f_286_, 6, v_lctx_118_);
lean_closure_set(v___f_286_, 7, v_fvars_119_);
lean_closure_set(v___f_286_, 8, v___x_284_);
lean_closure_set(v___f_286_, 9, v_s_121_);
lean_inc_ref(v___x_195_);
lean_inc_ref(v___x_150_);
v___x_287_ = l_Lean_Meta_withNewLocalInstances___redArg(v___x_150_, v___x_195_, v_fvars_119_, v_j_120_, v___f_286_);
v___x_1437__overap_288_ = l_Lean_Meta_withLCtx_x27___redArg(v___x_150_, v___x_195_, v_lctx_118_, v___x_287_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
v___x_289_ = lean_apply_5(v___x_1437__overap_288_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
return v___x_289_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1(lean_object* v___x_305_, lean_object* v___x_306_, lean_object* v_type_307_, lean_object* v_mvarId_308_, lean_object* v_n_309_, lean_object* v_mkName_310_, lean_object* v_lctx_311_, lean_object* v_fvars_312_, lean_object* v___x_313_, lean_object* v_s_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___x_1560__overap_320_; lean_object* v___x_321_; 
v___x_1560__overap_320_ = l_Lean_instantiateMVars___redArg(v___x_305_, v___x_306_, v_type_307_);
lean_inc(v___y_318_);
lean_inc_ref(v___y_317_);
lean_inc(v___y_316_);
lean_inc_ref(v___y_315_);
v___x_321_ = lean_apply_5(v___x_1560__overap_320_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, lean_box(0));
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_323_; uint8_t v___y_325_; uint8_t v___x_346_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref(v___x_321_);
v___x_323_ = l_Lean_Expr_cleanupAnnotations(v_a_322_);
v___x_346_ = l_Lean_Expr_isForall(v___x_323_);
if (v___x_346_ == 0)
{
uint8_t v___x_347_; 
v___x_347_ = l_Lean_Expr_isLet(v___x_323_);
v___y_325_ = v___x_347_;
goto v___jp_324_;
}
else
{
v___y_325_ = v___x_346_;
goto v___jp_324_;
}
v___jp_324_:
{
if (v___y_325_ == 0)
{
lean_object* v___x_326_; 
lean_inc(v___y_318_);
lean_inc_ref(v___y_317_);
lean_inc(v___y_316_);
lean_inc_ref(v___y_315_);
v___x_326_ = lean_whnf(v___x_323_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; uint8_t v___x_328_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_327_);
lean_dec_ref(v___x_326_);
v___x_328_ = l_Lean_Expr_isForall(v_a_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_a_327_);
lean_dec(v_s_314_);
lean_dec(v___x_313_);
lean_dec_ref(v_fvars_312_);
lean_dec_ref(v_lctx_311_);
lean_dec_ref(v_mkName_310_);
v___x_329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
v___x_330_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4);
v___x_331_ = l_Lean_Meta_throwTacticEx___redArg(v___x_329_, v_mvarId_308_, v___x_330_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = lean_nat_add(v_n_309_, v___x_332_);
v___x_334_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_308_, v_mkName_310_, v___x_333_, v_lctx_311_, v_fvars_312_, v___x_313_, v_s_314_, v_a_327_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
return v___x_334_;
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v_s_314_);
lean_dec(v___x_313_);
lean_dec_ref(v_fvars_312_);
lean_dec_ref(v_lctx_311_);
lean_dec_ref(v_mkName_310_);
lean_dec(v_mvarId_308_);
v_a_335_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_326_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_326_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = lean_nat_add(v_n_309_, v___x_343_);
v___x_345_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_308_, v_mkName_310_, v___x_344_, v_lctx_311_, v_fvars_312_, v___x_313_, v_s_314_, v___x_323_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
return v___x_345_;
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v_s_314_);
lean_dec(v___x_313_);
lean_dec_ref(v_fvars_312_);
lean_dec_ref(v_lctx_311_);
lean_dec_ref(v_mkName_310_);
lean_dec(v_mvarId_308_);
v_a_348_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_321_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_321_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___boxed(lean_object* v_mvarId_356_, lean_object* v_mkName_357_, lean_object* v_i_358_, lean_object* v_lctx_359_, lean_object* v_fvars_360_, lean_object* v_j_361_, lean_object* v_s_362_, lean_object* v_type_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_356_, v_mkName_357_, v_i_358_, v_lctx_359_, v_fvars_360_, v_j_361_, v_s_362_, v_type_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(lean_object* v_00_u03c3_370_, lean_object* v_mvarId_371_, lean_object* v_mkName_372_, lean_object* v_i_373_, lean_object* v_lctx_374_, lean_object* v_fvars_375_, lean_object* v_j_376_, lean_object* v_s_377_, lean_object* v_type_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_371_, v_mkName_372_, v_i_373_, v_lctx_374_, v_fvars_375_, v_j_376_, v_s_377_, v_type_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___boxed(lean_object* v_00_u03c3_385_, lean_object* v_mvarId_386_, lean_object* v_mkName_387_, lean_object* v_i_388_, lean_object* v_lctx_389_, lean_object* v_fvars_390_, lean_object* v_j_391_, lean_object* v_s_392_, lean_object* v_type_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(v_00_u03c3_385_, v_mvarId_386_, v_mkName_387_, v_i_388_, v_lctx_389_, v_fvars_390_, v_j_391_, v_s_392_, v_type_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0(lean_object* v_mvarId_421_, lean_object* v___x_422_, lean_object* v_mkName_423_, lean_object* v_n_424_, lean_object* v_s_425_, lean_object* v___f_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_432_; 
lean_inc(v_mvarId_421_);
v___x_432_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_421_, v___x_422_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v___x_433_; 
lean_dec_ref(v___x_432_);
lean_inc(v_mvarId_421_);
v___x_433_ = l_Lean_MVarId_getType(v_mvarId_421_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v_lctx_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref(v___x_433_);
v_lctx_435_ = lean_ctor_get(v___y_427_, 2);
lean_inc_ref(v_lctx_435_);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__0));
v___x_438_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_421_, v_mkName_423_, v_n_424_, v_lctx_435_, v___x_437_, v___x_436_, v_s_425_, v_a_434_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec_ref(v___y_427_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_459_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_459_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_459_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_459_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v_fst_443_; lean_object* v_snd_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_458_; 
v_fst_443_ = lean_ctor_get(v_a_439_, 0);
v_snd_444_ = lean_ctor_get(v_a_439_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_a_439_);
if (v_isSharedCheck_458_ == 0)
{
v___x_446_ = v_a_439_;
v_isShared_447_ = v_isSharedCheck_458_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_snd_444_);
lean_inc(v_fst_443_);
lean_dec(v_a_439_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_458_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; size_t v_sz_449_; size_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__10));
v_sz_449_ = lean_array_size(v_fst_443_);
v___x_450_ = ((size_t)0ULL);
v___x_451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_448_, v___f_426_, v_sz_449_, v___x_450_, v_fst_443_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_451_);
v___x_453_ = v___x_446_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_snd_444_);
v___x_453_ = v_reuseFailAlloc_457_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_455_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_453_);
v___x_455_ = v___x_441_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec_ref(v___f_426_);
v_a_460_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_438_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_438_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec_ref(v___y_427_);
lean_dec_ref(v___f_426_);
lean_dec(v_s_425_);
lean_dec(v_n_424_);
lean_dec_ref(v_mkName_423_);
lean_dec(v_mvarId_421_);
v_a_468_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_433_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_433_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec_ref(v___y_427_);
lean_dec_ref(v___f_426_);
lean_dec(v_s_425_);
lean_dec(v_n_424_);
lean_dec_ref(v_mkName_423_);
lean_dec(v_mvarId_421_);
v_a_476_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_432_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_432_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed(lean_object* v_mvarId_484_, lean_object* v___x_485_, lean_object* v_mkName_486_, lean_object* v_n_487_, lean_object* v_s_488_, lean_object* v___f_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0(v_mvarId_484_, v___x_485_, v_mkName_486_, v_n_487_, v_s_488_, v___f_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg(lean_object* v_mvarId_497_, lean_object* v_n_498_, lean_object* v_mkName_499_, lean_object* v_s_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___x_506_; lean_object* v_toApplicative_507_; lean_object* v_toFunctor_508_; lean_object* v_toSeq_509_; lean_object* v_toSeqLeft_510_; lean_object* v_toSeqRight_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_592_; 
v___x_506_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
v_toApplicative_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc_ref(v_toApplicative_507_);
v_toFunctor_508_ = lean_ctor_get(v_toApplicative_507_, 0);
v_toSeq_509_ = lean_ctor_get(v_toApplicative_507_, 2);
v_toSeqLeft_510_ = lean_ctor_get(v_toApplicative_507_, 3);
v_toSeqRight_511_ = lean_ctor_get(v_toApplicative_507_, 4);
v_isSharedCheck_592_ = !lean_is_exclusive(v_toApplicative_507_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; 
v_unused_593_ = lean_ctor_get(v_toApplicative_507_, 1);
lean_dec(v_unused_593_);
v___x_513_ = v_toApplicative_507_;
v_isShared_514_ = v_isSharedCheck_592_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_toSeqRight_511_);
lean_inc(v_toSeqLeft_510_);
lean_inc(v_toSeq_509_);
lean_inc(v_toFunctor_508_);
lean_dec(v_toApplicative_507_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_592_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___f_515_; lean_object* v___f_516_; lean_object* v___f_517_; lean_object* v___f_518_; lean_object* v___x_519_; lean_object* v___f_520_; lean_object* v___f_521_; lean_object* v___f_522_; lean_object* v___x_524_; 
v___f_515_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2));
v___f_516_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3));
lean_inc_ref(v_toFunctor_508_);
v___f_517_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_517_, 0, v_toFunctor_508_);
v___f_518_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_518_, 0, v_toFunctor_508_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v___f_517_);
lean_ctor_set(v___x_519_, 1, v___f_518_);
v___f_520_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_520_, 0, v_toSeqRight_511_);
v___f_521_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_521_, 0, v_toSeqLeft_510_);
v___f_522_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_522_, 0, v_toSeq_509_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 4, v___f_520_);
lean_ctor_set(v___x_513_, 3, v___f_521_);
lean_ctor_set(v___x_513_, 2, v___f_522_);
lean_ctor_set(v___x_513_, 1, v___f_515_);
lean_ctor_set(v___x_513_, 0, v___x_519_);
v___x_524_ = v___x_513_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v___f_515_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v___f_522_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v___f_521_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v___f_520_);
v___x_524_ = v_reuseFailAlloc_591_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v_toApplicative_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_589_; 
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v___f_516_);
v___x_526_ = l_StateRefT_x27_instMonad___redArg(v___x_525_);
v___x_527_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_527_, 0, lean_box(0));
lean_closure_set(v___x_527_, 1, lean_box(0));
lean_closure_set(v___x_527_, 2, v___x_526_);
v___x_528_ = l_instMonadControlTOfPure___redArg(v___x_527_);
v_toApplicative_529_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; 
v_unused_590_ = lean_ctor_get(v___x_506_, 1);
lean_dec(v_unused_590_);
v___x_531_ = v___x_506_;
v_isShared_532_ = v_isSharedCheck_589_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_toApplicative_529_);
lean_dec(v___x_506_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_589_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v_toFunctor_533_; lean_object* v_toSeq_534_; lean_object* v_toSeqLeft_535_; lean_object* v_toSeqRight_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_587_; 
v_toFunctor_533_ = lean_ctor_get(v_toApplicative_529_, 0);
v_toSeq_534_ = lean_ctor_get(v_toApplicative_529_, 2);
v_toSeqLeft_535_ = lean_ctor_get(v_toApplicative_529_, 3);
v_toSeqRight_536_ = lean_ctor_get(v_toApplicative_529_, 4);
v_isSharedCheck_587_ = !lean_is_exclusive(v_toApplicative_529_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v_toApplicative_529_, 1);
lean_dec(v_unused_588_);
v___x_538_ = v_toApplicative_529_;
v_isShared_539_ = v_isSharedCheck_587_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_toSeqRight_536_);
lean_inc(v_toSeqLeft_535_);
lean_inc(v_toSeq_534_);
lean_inc(v_toFunctor_533_);
lean_dec(v_toApplicative_529_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_587_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___f_540_; lean_object* v___f_541_; lean_object* v___x_542_; lean_object* v___f_543_; lean_object* v___f_544_; lean_object* v___f_545_; lean_object* v___x_547_; 
lean_inc_ref(v_toFunctor_533_);
v___f_540_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_540_, 0, v_toFunctor_533_);
v___f_541_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_541_, 0, v_toFunctor_533_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___f_540_);
lean_ctor_set(v___x_542_, 1, v___f_541_);
v___f_543_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_543_, 0, v_toSeqRight_536_);
v___f_544_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_544_, 0, v_toSeqLeft_535_);
v___f_545_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_545_, 0, v_toSeq_534_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v___f_543_);
lean_ctor_set(v___x_538_, 3, v___f_544_);
lean_ctor_set(v___x_538_, 2, v___f_545_);
lean_ctor_set(v___x_538_, 1, v___f_515_);
lean_ctor_set(v___x_538_, 0, v___x_542_);
v___x_547_ = v___x_538_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v___f_515_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v___f_545_);
lean_ctor_set(v_reuseFailAlloc_586_, 3, v___f_544_);
lean_ctor_set(v_reuseFailAlloc_586_, 4, v___f_543_);
v___x_547_ = v_reuseFailAlloc_586_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_549_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 1, v___f_516_);
lean_ctor_set(v___x_531_, 0, v___x_547_);
v___x_549_ = v___x_531_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v___f_516_);
v___x_549_ = v_reuseFailAlloc_585_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; lean_object* v_toApplicative_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_583_; 
v___x_550_ = l_StateRefT_x27_instMonad___redArg(v___x_549_);
v_toApplicative_551_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_583_ == 0)
{
lean_object* v_unused_584_; 
v_unused_584_ = lean_ctor_get(v___x_550_, 1);
lean_dec(v_unused_584_);
v___x_553_ = v___x_550_;
v_isShared_554_ = v_isSharedCheck_583_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_toApplicative_551_);
lean_dec(v___x_550_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_583_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_toFunctor_555_; lean_object* v_toSeq_556_; lean_object* v_toSeqLeft_557_; lean_object* v_toSeqRight_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_581_; 
v_toFunctor_555_ = lean_ctor_get(v_toApplicative_551_, 0);
v_toSeq_556_ = lean_ctor_get(v_toApplicative_551_, 2);
v_toSeqLeft_557_ = lean_ctor_get(v_toApplicative_551_, 3);
v_toSeqRight_558_ = lean_ctor_get(v_toApplicative_551_, 4);
v_isSharedCheck_581_ = !lean_is_exclusive(v_toApplicative_551_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v_toApplicative_551_, 1);
lean_dec(v_unused_582_);
v___x_560_ = v_toApplicative_551_;
v_isShared_561_ = v_isSharedCheck_581_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_toSeqRight_558_);
lean_inc(v_toSeqLeft_557_);
lean_inc(v_toSeq_556_);
lean_inc(v_toFunctor_555_);
lean_dec(v_toApplicative_551_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_581_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___f_562_; lean_object* v___f_563_; lean_object* v___f_564_; lean_object* v___f_565_; lean_object* v___f_566_; lean_object* v___x_567_; lean_object* v___f_568_; lean_object* v___f_569_; lean_object* v___f_570_; lean_object* v___x_572_; 
v___f_562_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0));
v___f_563_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4));
v___f_564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5));
lean_inc_ref(v_toFunctor_555_);
v___f_565_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_565_, 0, v_toFunctor_555_);
v___f_566_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_566_, 0, v_toFunctor_555_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v___f_565_);
lean_ctor_set(v___x_567_, 1, v___f_566_);
v___f_568_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_568_, 0, v_toSeqRight_558_);
v___f_569_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_569_, 0, v_toSeqLeft_557_);
v___f_570_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_570_, 0, v_toSeq_556_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 4, v___f_568_);
lean_ctor_set(v___x_560_, 3, v___f_569_);
lean_ctor_set(v___x_560_, 2, v___f_570_);
lean_ctor_set(v___x_560_, 1, v___f_563_);
lean_ctor_set(v___x_560_, 0, v___x_567_);
v___x_572_ = v___x_560_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___f_563_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v___f_570_);
lean_ctor_set(v_reuseFailAlloc_580_, 3, v___f_569_);
lean_ctor_set(v_reuseFailAlloc_580_, 4, v___f_568_);
v___x_572_ = v_reuseFailAlloc_580_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_574_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 1, v___f_564_);
lean_ctor_set(v___x_553_, 0, v___x_572_);
v___x_574_ = v___x_553_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v___f_564_);
v___x_574_ = v_reuseFailAlloc_579_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; lean_object* v___f_576_; lean_object* v___x_43__overap_577_; lean_object* v___x_578_; 
v___x_575_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
lean_inc(v_mvarId_497_);
v___f_576_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_576_, 0, v_mvarId_497_);
lean_closure_set(v___f_576_, 1, v___x_575_);
lean_closure_set(v___f_576_, 2, v_mkName_499_);
lean_closure_set(v___f_576_, 3, v_n_498_);
lean_closure_set(v___f_576_, 4, v_s_500_);
lean_closure_set(v___f_576_, 5, v___f_562_);
v___x_43__overap_577_ = l_Lean_MVarId_withContext___redArg(v___x_528_, v___x_574_, v_mvarId_497_, v___f_576_);
lean_inc(v_a_504_);
lean_inc_ref(v_a_503_);
lean_inc(v_a_502_);
lean_inc_ref(v_a_501_);
v___x_578_ = lean_apply_5(v___x_43__overap_577_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, lean_box(0));
return v___x_578_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___boxed(lean_object* v_mvarId_594_, lean_object* v_n_595_, lean_object* v_mkName_596_, lean_object* v_s_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg(v_mvarId_594_, v_n_595_, v_mkName_596_, v_s_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(lean_object* v_00_u03c3_604_, lean_object* v_mvarId_605_, lean_object* v_n_606_, lean_object* v_mkName_607_, lean_object* v_s_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___x_614_; lean_object* v_toApplicative_615_; lean_object* v_toFunctor_616_; lean_object* v_toSeq_617_; lean_object* v_toSeqLeft_618_; lean_object* v_toSeqRight_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_700_; 
v___x_614_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
v_toApplicative_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc_ref(v_toApplicative_615_);
v_toFunctor_616_ = lean_ctor_get(v_toApplicative_615_, 0);
v_toSeq_617_ = lean_ctor_get(v_toApplicative_615_, 2);
v_toSeqLeft_618_ = lean_ctor_get(v_toApplicative_615_, 3);
v_toSeqRight_619_ = lean_ctor_get(v_toApplicative_615_, 4);
v_isSharedCheck_700_ = !lean_is_exclusive(v_toApplicative_615_);
if (v_isSharedCheck_700_ == 0)
{
lean_object* v_unused_701_; 
v_unused_701_ = lean_ctor_get(v_toApplicative_615_, 1);
lean_dec(v_unused_701_);
v___x_621_ = v_toApplicative_615_;
v_isShared_622_ = v_isSharedCheck_700_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_toSeqRight_619_);
lean_inc(v_toSeqLeft_618_);
lean_inc(v_toSeq_617_);
lean_inc(v_toFunctor_616_);
lean_dec(v_toApplicative_615_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_700_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___f_623_; lean_object* v___f_624_; lean_object* v___f_625_; lean_object* v___f_626_; lean_object* v___x_627_; lean_object* v___f_628_; lean_object* v___f_629_; lean_object* v___f_630_; lean_object* v___x_632_; 
v___f_623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2));
v___f_624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3));
lean_inc_ref(v_toFunctor_616_);
v___f_625_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_625_, 0, v_toFunctor_616_);
v___f_626_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_626_, 0, v_toFunctor_616_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___f_625_);
lean_ctor_set(v___x_627_, 1, v___f_626_);
v___f_628_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_628_, 0, v_toSeqRight_619_);
v___f_629_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_629_, 0, v_toSeqLeft_618_);
v___f_630_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_630_, 0, v_toSeq_617_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 4, v___f_628_);
lean_ctor_set(v___x_621_, 3, v___f_629_);
lean_ctor_set(v___x_621_, 2, v___f_630_);
lean_ctor_set(v___x_621_, 1, v___f_623_);
lean_ctor_set(v___x_621_, 0, v___x_627_);
v___x_632_ = v___x_621_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v___f_623_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v___f_630_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v___f_629_);
lean_ctor_set(v_reuseFailAlloc_699_, 4, v___f_628_);
v___x_632_ = v_reuseFailAlloc_699_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v_toApplicative_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_697_; 
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___f_624_);
v___x_634_ = l_StateRefT_x27_instMonad___redArg(v___x_633_);
v___x_635_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_635_, 0, lean_box(0));
lean_closure_set(v___x_635_, 1, lean_box(0));
lean_closure_set(v___x_635_, 2, v___x_634_);
v___x_636_ = l_instMonadControlTOfPure___redArg(v___x_635_);
v_toApplicative_637_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v___x_614_, 1);
lean_dec(v_unused_698_);
v___x_639_ = v___x_614_;
v_isShared_640_ = v_isSharedCheck_697_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_toApplicative_637_);
lean_dec(v___x_614_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_697_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_toFunctor_641_; lean_object* v_toSeq_642_; lean_object* v_toSeqLeft_643_; lean_object* v_toSeqRight_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_695_; 
v_toFunctor_641_ = lean_ctor_get(v_toApplicative_637_, 0);
v_toSeq_642_ = lean_ctor_get(v_toApplicative_637_, 2);
v_toSeqLeft_643_ = lean_ctor_get(v_toApplicative_637_, 3);
v_toSeqRight_644_ = lean_ctor_get(v_toApplicative_637_, 4);
v_isSharedCheck_695_ = !lean_is_exclusive(v_toApplicative_637_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v_toApplicative_637_, 1);
lean_dec(v_unused_696_);
v___x_646_ = v_toApplicative_637_;
v_isShared_647_ = v_isSharedCheck_695_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_toSeqRight_644_);
lean_inc(v_toSeqLeft_643_);
lean_inc(v_toSeq_642_);
lean_inc(v_toFunctor_641_);
lean_dec(v_toApplicative_637_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_695_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___f_648_; lean_object* v___f_649_; lean_object* v___x_650_; lean_object* v___f_651_; lean_object* v___f_652_; lean_object* v___f_653_; lean_object* v___x_655_; 
lean_inc_ref(v_toFunctor_641_);
v___f_648_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_648_, 0, v_toFunctor_641_);
v___f_649_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_649_, 0, v_toFunctor_641_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v___f_648_);
lean_ctor_set(v___x_650_, 1, v___f_649_);
v___f_651_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_651_, 0, v_toSeqRight_644_);
v___f_652_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_652_, 0, v_toSeqLeft_643_);
v___f_653_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_653_, 0, v_toSeq_642_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 4, v___f_651_);
lean_ctor_set(v___x_646_, 3, v___f_652_);
lean_ctor_set(v___x_646_, 2, v___f_653_);
lean_ctor_set(v___x_646_, 1, v___f_623_);
lean_ctor_set(v___x_646_, 0, v___x_650_);
v___x_655_ = v___x_646_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v___f_623_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v___f_653_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v___f_652_);
lean_ctor_set(v_reuseFailAlloc_694_, 4, v___f_651_);
v___x_655_ = v_reuseFailAlloc_694_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_657_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v___f_624_);
lean_ctor_set(v___x_639_, 0, v___x_655_);
v___x_657_ = v___x_639_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___f_624_);
v___x_657_ = v_reuseFailAlloc_693_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; lean_object* v_toApplicative_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_691_; 
v___x_658_ = l_StateRefT_x27_instMonad___redArg(v___x_657_);
v_toApplicative_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; 
v_unused_692_ = lean_ctor_get(v___x_658_, 1);
lean_dec(v_unused_692_);
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_691_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_toApplicative_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_691_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_toFunctor_663_; lean_object* v_toSeq_664_; lean_object* v_toSeqLeft_665_; lean_object* v_toSeqRight_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_689_; 
v_toFunctor_663_ = lean_ctor_get(v_toApplicative_659_, 0);
v_toSeq_664_ = lean_ctor_get(v_toApplicative_659_, 2);
v_toSeqLeft_665_ = lean_ctor_get(v_toApplicative_659_, 3);
v_toSeqRight_666_ = lean_ctor_get(v_toApplicative_659_, 4);
v_isSharedCheck_689_ = !lean_is_exclusive(v_toApplicative_659_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v_toApplicative_659_, 1);
lean_dec(v_unused_690_);
v___x_668_ = v_toApplicative_659_;
v_isShared_669_ = v_isSharedCheck_689_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_toSeqRight_666_);
lean_inc(v_toSeqLeft_665_);
lean_inc(v_toSeq_664_);
lean_inc(v_toFunctor_663_);
lean_dec(v_toApplicative_659_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_689_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___f_670_; lean_object* v___f_671_; lean_object* v___f_672_; lean_object* v___f_673_; lean_object* v___f_674_; lean_object* v___x_675_; lean_object* v___f_676_; lean_object* v___f_677_; lean_object* v___f_678_; lean_object* v___x_680_; 
v___f_670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0));
v___f_671_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4));
v___f_672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5));
lean_inc_ref(v_toFunctor_663_);
v___f_673_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_673_, 0, v_toFunctor_663_);
v___f_674_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_674_, 0, v_toFunctor_663_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v___f_673_);
lean_ctor_set(v___x_675_, 1, v___f_674_);
v___f_676_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_676_, 0, v_toSeqRight_666_);
v___f_677_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_677_, 0, v_toSeqLeft_665_);
v___f_678_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_678_, 0, v_toSeq_664_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 4, v___f_676_);
lean_ctor_set(v___x_668_, 3, v___f_677_);
lean_ctor_set(v___x_668_, 2, v___f_678_);
lean_ctor_set(v___x_668_, 1, v___f_671_);
lean_ctor_set(v___x_668_, 0, v___x_675_);
v___x_680_ = v___x_668_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v___f_671_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v___f_678_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v___f_677_);
lean_ctor_set(v_reuseFailAlloc_688_, 4, v___f_676_);
v___x_680_ = v_reuseFailAlloc_688_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_682_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v___f_672_);
lean_ctor_set(v___x_661_, 0, v___x_680_);
v___x_682_ = v___x_661_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___f_672_);
v___x_682_ = v_reuseFailAlloc_687_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; lean_object* v___f_684_; lean_object* v___x_617__overap_685_; lean_object* v___x_686_; 
v___x_683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
lean_inc(v_mvarId_605_);
v___f_684_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_684_, 0, v_mvarId_605_);
lean_closure_set(v___f_684_, 1, v___x_683_);
lean_closure_set(v___f_684_, 2, v_mkName_607_);
lean_closure_set(v___f_684_, 3, v_n_606_);
lean_closure_set(v___f_684_, 4, v_s_608_);
lean_closure_set(v___f_684_, 5, v___f_670_);
v___x_617__overap_685_ = l_Lean_MVarId_withContext___redArg(v___x_636_, v___x_682_, v_mvarId_605_, v___f_684_);
lean_inc(v_a_612_);
lean_inc_ref(v_a_611_);
lean_inc(v_a_610_);
lean_inc_ref(v_a_609_);
v___x_686_ = lean_apply_5(v___x_617__overap_685_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, lean_box(0));
return v___x_686_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___boxed(lean_object* v_00_u03c3_702_, lean_object* v_mvarId_703_, lean_object* v_n_704_, lean_object* v_mkName_705_, lean_object* v_s_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(v_00_u03c3_702_, v_mvarId_703_, v_n_704_, v_mkName_705_, v_s_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(lean_object* v_name_713_, lean_object* v_decl_714_, lean_object* v_ref_715_){
_start:
{
lean_object* v_defValue_717_; lean_object* v_descr_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_745_; 
v_defValue_717_ = lean_ctor_get(v_decl_714_, 0);
v_descr_718_ = lean_ctor_get(v_decl_714_, 1);
v_isSharedCheck_745_ = !lean_is_exclusive(v_decl_714_);
if (v_isSharedCheck_745_ == 0)
{
v___x_720_ = v_decl_714_;
v_isShared_721_ = v_isSharedCheck_745_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_descr_718_);
lean_inc(v_defValue_717_);
lean_dec(v_decl_714_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_745_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; uint8_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_722_ = lean_alloc_ctor(1, 0, 1);
v___x_723_ = lean_unbox(v_defValue_717_);
lean_ctor_set_uint8(v___x_722_, 0, v___x_723_);
lean_inc(v_name_713_);
v___x_724_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_724_, 0, v_name_713_);
lean_ctor_set(v___x_724_, 1, v_ref_715_);
lean_ctor_set(v___x_724_, 2, v___x_722_);
lean_ctor_set(v___x_724_, 3, v_descr_718_);
lean_inc(v_name_713_);
v___x_725_ = lean_register_option(v_name_713_, v___x_724_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_735_; 
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; 
v_unused_736_ = lean_ctor_get(v___x_725_, 0);
lean_dec(v_unused_736_);
v___x_727_ = v___x_725_;
v_isShared_728_ = v_isSharedCheck_735_;
goto v_resetjp_726_;
}
else
{
lean_dec(v___x_725_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_735_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v_defValue_717_);
lean_ctor_set(v___x_720_, 0, v_name_713_);
v___x_730_ = v___x_720_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_name_713_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_defValue_717_);
v___x_730_ = v_reuseFailAlloc_734_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_732_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_730_);
v___x_732_ = v___x_727_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_del_object(v___x_720_);
lean_dec(v_defValue_717_);
lean_dec(v_name_713_);
v_a_737_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_725_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_725_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_746_, lean_object* v_decl_747_, lean_object* v_ref_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(v_name_746_, v_decl_747_, v_ref_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_769_ = ((lean_object*)(l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_));
v___x_770_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_));
v___x_771_ = ((lean_object*)(l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_));
v___x_772_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(v___x_769_, v___x_770_, v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4____boxed(lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_();
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(lean_object* v_lctx_775_, lean_object* v_binderName_776_, uint8_t v_hygienic_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
if (v_hygienic_777_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = l_Lean_LocalContext_getUnusedName(v_lctx_775_, v_binderName_776_);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
else
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_Core_mkFreshUserName(v_binderName_776_, v_a_778_, v_a_779_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg___boxed(lean_object* v_lctx_784_, lean_object* v_binderName_785_, lean_object* v_hygienic_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
uint8_t v_hygienic_boxed_790_; lean_object* v_res_791_; 
v_hygienic_boxed_790_ = lean_unbox(v_hygienic_786_);
v_res_791_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_784_, v_binderName_785_, v_hygienic_boxed_790_, v_a_787_, v_a_788_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec_ref(v_lctx_784_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore(lean_object* v_lctx_792_, lean_object* v_binderName_793_, uint8_t v_hygienic_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_792_, v_binderName_793_, v_hygienic_794_, v_a_797_, v_a_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___boxed(lean_object* v_lctx_801_, lean_object* v_binderName_802_, lean_object* v_hygienic_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
uint8_t v_hygienic_boxed_809_; lean_object* v_res_810_; 
v_hygienic_boxed_809_ = lean_unbox(v_hygienic_803_);
v_res_810_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore(v_lctx_801_, v_binderName_802_, v_hygienic_boxed_809_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec_ref(v_lctx_801_);
return v_res_810_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(lean_object* v_opts_811_, lean_object* v_opt_812_){
_start:
{
lean_object* v_name_813_; lean_object* v_defValue_814_; lean_object* v_map_815_; lean_object* v___x_816_; 
v_name_813_ = lean_ctor_get(v_opt_812_, 0);
v_defValue_814_ = lean_ctor_get(v_opt_812_, 1);
v_map_815_ = lean_ctor_get(v_opts_811_, 0);
v___x_816_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_815_, v_name_813_);
if (lean_obj_tag(v___x_816_) == 0)
{
uint8_t v___x_817_; 
v___x_817_ = lean_unbox(v_defValue_814_);
return v___x_817_;
}
else
{
lean_object* v_val_818_; 
v_val_818_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_val_818_);
lean_dec_ref(v___x_816_);
if (lean_obj_tag(v_val_818_) == 1)
{
uint8_t v_v_819_; 
v_v_819_ = lean_ctor_get_uint8(v_val_818_, 0);
lean_dec_ref(v_val_818_);
return v_v_819_;
}
else
{
uint8_t v___x_820_; 
lean_dec(v_val_818_);
v___x_820_ = lean_unbox(v_defValue_814_);
return v___x_820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0___boxed(lean_object* v_opts_821_, lean_object* v_opt_822_){
_start:
{
uint8_t v_res_823_; lean_object* v_r_824_; 
v_res_823_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v_opts_821_, v_opt_822_);
lean_dec_ref(v_opt_822_);
lean_dec_ref(v_opts_821_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg(lean_object* v_binderName_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_lctx_830_; lean_object* v_options_831_; lean_object* v___x_832_; uint8_t v___x_833_; lean_object* v___x_834_; 
v_lctx_830_ = lean_ctor_get(v_a_826_, 2);
v_options_831_ = lean_ctor_get(v_a_827_, 2);
v___x_832_ = l_Lean_Meta_tactic_hygienic;
v___x_833_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v_options_831_, v___x_832_);
v___x_834_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_830_, v_binderName_825_, v___x_833_, v_a_827_, v_a_828_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg___boxed(lean_object* v_binderName_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_binderName_835_, v_a_836_, v_a_837_, v_a_838_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec_ref(v_a_836_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic(lean_object* v_binderName_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_binderName_841_, v_a_842_, v_a_844_, v_a_845_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___boxed(lean_object* v_binderName_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_Meta_mkFreshBinderNameForTactic(v_binderName_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(uint8_t v_preserveBinderNames_858_, uint8_t v_hygienic_859_, lean_object* v_lctx_860_, lean_object* v_binderName_861_, lean_object* v_rest_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_binderName_867_; lean_object* v___y_868_; lean_object* v___y_869_; uint8_t v___x_890_; 
v___x_890_ = l_Lean_Name_isAnonymous(v_binderName_861_);
if (v___x_890_ == 0)
{
v_binderName_867_ = v_binderName_861_;
v___y_868_ = v_a_863_;
v___y_869_ = v_a_864_;
goto v___jp_866_;
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; 
lean_dec(v_binderName_861_);
v___x_891_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__1));
v___x_892_ = l_Lean_Core_mkFreshUserName(v___x_891_, v_a_863_, v_a_864_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
lean_dec_ref(v___x_892_);
v_binderName_867_ = v_a_893_;
v___y_868_ = v_a_863_;
v___y_869_ = v_a_864_;
goto v___jp_866_;
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec(v_rest_862_);
v_a_894_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_892_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_892_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
v___jp_866_:
{
if (v_preserveBinderNames_858_ == 0)
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_860_, v_binderName_867_, v_hygienic_859_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_879_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_879_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_879_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_879_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v_a_871_);
lean_ctor_set(v___x_875_, 1, v_rest_862_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_875_);
v___x_877_ = v___x_873_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec(v_rest_862_);
v_a_880_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_870_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_870_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v_binderName_867_);
lean_ctor_set(v___x_888_, 1, v_rest_862_);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___boxed(lean_object* v_preserveBinderNames_902_, lean_object* v_hygienic_903_, lean_object* v_lctx_904_, lean_object* v_binderName_905_, lean_object* v_rest_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
uint8_t v_preserveBinderNames_boxed_910_; uint8_t v_hygienic_boxed_911_; lean_object* v_res_912_; 
v_preserveBinderNames_boxed_910_ = lean_unbox(v_preserveBinderNames_902_);
v_hygienic_boxed_911_ = lean_unbox(v_hygienic_903_);
v_res_912_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_boxed_910_, v_hygienic_boxed_911_, v_lctx_904_, v_binderName_905_, v_rest_906_, v_a_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec_ref(v_lctx_904_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(uint8_t v_preserveBinderNames_913_, uint8_t v_hygienic_914_, lean_object* v_lctx_915_, lean_object* v_binderName_916_, lean_object* v_rest_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_913_, v_hygienic_914_, v_lctx_915_, v_binderName_916_, v_rest_917_, v_a_920_, v_a_921_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___boxed(lean_object* v_preserveBinderNames_924_, lean_object* v_hygienic_925_, lean_object* v_lctx_926_, lean_object* v_binderName_927_, lean_object* v_rest_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
uint8_t v_preserveBinderNames_boxed_934_; uint8_t v_hygienic_boxed_935_; lean_object* v_res_936_; 
v_preserveBinderNames_boxed_934_ = lean_unbox(v_preserveBinderNames_924_);
v_hygienic_boxed_935_ = lean_unbox(v_hygienic_925_);
v_res_936_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(v_preserveBinderNames_boxed_934_, v_hygienic_boxed_935_, v_lctx_926_, v_binderName_927_, v_rest_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec_ref(v_lctx_926_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(uint8_t v_preserveBinderNames_941_, uint8_t v_hygienic_942_, uint8_t v_useNamesForExplicitOnly_943_, lean_object* v_lctx_944_, lean_object* v_binderName_945_, uint8_t v_isExplicit_946_, lean_object* v_x_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
if (lean_obj_tag(v_x_947_) == 0)
{
lean_object* v___x_951_; 
v___x_951_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_941_, v_hygienic_942_, v_lctx_944_, v_binderName_945_, v_x_947_, v_a_948_, v_a_949_);
return v___x_951_;
}
else
{
lean_object* v_head_952_; lean_object* v_tail_953_; 
v_head_952_ = lean_ctor_get(v_x_947_, 0);
v_tail_953_ = lean_ctor_get(v_x_947_, 1);
if (v_useNamesForExplicitOnly_943_ == 0)
{
lean_inc(v_tail_953_);
lean_inc(v_head_952_);
lean_dec_ref(v_x_947_);
goto v___jp_954_;
}
else
{
if (v_isExplicit_946_ == 0)
{
lean_object* v___x_960_; 
v___x_960_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_941_, v_hygienic_942_, v_lctx_944_, v_binderName_945_, v_x_947_, v_a_948_, v_a_949_);
return v___x_960_;
}
else
{
lean_inc(v_tail_953_);
lean_inc(v_head_952_);
lean_dec_ref(v_x_947_);
goto v___jp_954_;
}
}
v___jp_954_:
{
lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_955_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__1));
v___x_956_ = lean_name_eq(v_head_952_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec(v_binderName_945_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v_head_952_);
lean_ctor_set(v___x_957_, 1, v_tail_953_);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
else
{
lean_object* v___x_959_; 
lean_dec(v_head_952_);
v___x_959_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_941_, v_hygienic_942_, v_lctx_944_, v_binderName_945_, v_tail_953_, v_a_948_, v_a_949_);
return v___x_959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___boxed(lean_object* v_preserveBinderNames_961_, lean_object* v_hygienic_962_, lean_object* v_useNamesForExplicitOnly_963_, lean_object* v_lctx_964_, lean_object* v_binderName_965_, lean_object* v_isExplicit_966_, lean_object* v_x_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
uint8_t v_preserveBinderNames_boxed_971_; uint8_t v_hygienic_boxed_972_; uint8_t v_useNamesForExplicitOnly_boxed_973_; uint8_t v_isExplicit_boxed_974_; lean_object* v_res_975_; 
v_preserveBinderNames_boxed_971_ = lean_unbox(v_preserveBinderNames_961_);
v_hygienic_boxed_972_ = lean_unbox(v_hygienic_962_);
v_useNamesForExplicitOnly_boxed_973_ = lean_unbox(v_useNamesForExplicitOnly_963_);
v_isExplicit_boxed_974_ = lean_unbox(v_isExplicit_966_);
v_res_975_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_boxed_971_, v_hygienic_boxed_972_, v_useNamesForExplicitOnly_boxed_973_, v_lctx_964_, v_binderName_965_, v_isExplicit_boxed_974_, v_x_967_, v_a_968_, v_a_969_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
lean_dec_ref(v_lctx_964_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(uint8_t v_preserveBinderNames_976_, uint8_t v_hygienic_977_, uint8_t v_useNamesForExplicitOnly_978_, lean_object* v_lctx_979_, lean_object* v_binderName_980_, uint8_t v_isExplicit_981_, lean_object* v_x_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_976_, v_hygienic_977_, v_useNamesForExplicitOnly_978_, v_lctx_979_, v_binderName_980_, v_isExplicit_981_, v_x_982_, v_a_985_, v_a_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___boxed(lean_object* v_preserveBinderNames_989_, lean_object* v_hygienic_990_, lean_object* v_useNamesForExplicitOnly_991_, lean_object* v_lctx_992_, lean_object* v_binderName_993_, lean_object* v_isExplicit_994_, lean_object* v_x_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1001_; uint8_t v_hygienic_boxed_1002_; uint8_t v_useNamesForExplicitOnly_boxed_1003_; uint8_t v_isExplicit_boxed_1004_; lean_object* v_res_1005_; 
v_preserveBinderNames_boxed_1001_ = lean_unbox(v_preserveBinderNames_989_);
v_hygienic_boxed_1002_ = lean_unbox(v_hygienic_990_);
v_useNamesForExplicitOnly_boxed_1003_ = lean_unbox(v_useNamesForExplicitOnly_991_);
v_isExplicit_boxed_1004_ = lean_unbox(v_isExplicit_994_);
v_res_1005_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(v_preserveBinderNames_boxed_1001_, v_hygienic_boxed_1002_, v_useNamesForExplicitOnly_boxed_1003_, v_lctx_992_, v_binderName_993_, v_isExplicit_boxed_1004_, v_x_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec_ref(v_lctx_992_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(lean_object* v_mvarId_1006_, lean_object* v_x_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1006_, v_x_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
v_a_1022_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1013_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1013_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg___boxed(lean_object* v_mvarId_1030_, lean_object* v_x_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_1030_, v_x_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(lean_object* v_00_u03b1_1038_, lean_object* v_mvarId_1039_, lean_object* v_x_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_1039_, v_x_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___boxed(lean_object* v_00_u03b1_1047_, lean_object* v_mvarId_1048_, lean_object* v_x_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(v_00_u03b1_1047_, v_mvarId_1048_, v_x_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(size_t v_sz_1056_, size_t v_i_1057_, lean_object* v_bs_1058_){
_start:
{
uint8_t v___x_1059_; 
v___x_1059_ = lean_usize_dec_lt(v_i_1057_, v_sz_1056_);
if (v___x_1059_ == 0)
{
return v_bs_1058_;
}
else
{
lean_object* v_v_1060_; lean_object* v___x_1061_; lean_object* v_bs_x27_1062_; lean_object* v___x_1063_; size_t v___x_1064_; size_t v___x_1065_; lean_object* v___x_1066_; 
v_v_1060_ = lean_array_uget(v_bs_1058_, v_i_1057_);
v___x_1061_ = lean_unsigned_to_nat(0u);
v_bs_x27_1062_ = lean_array_uset(v_bs_1058_, v_i_1057_, v___x_1061_);
v___x_1063_ = l_Lean_Expr_fvarId_x21(v_v_1060_);
lean_dec(v_v_1060_);
v___x_1064_ = ((size_t)1ULL);
v___x_1065_ = lean_usize_add(v_i_1057_, v___x_1064_);
v___x_1066_ = lean_array_uset(v_bs_x27_1062_, v_i_1057_, v___x_1063_);
v_i_1057_ = v___x_1065_;
v_bs_1058_ = v___x_1066_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1___boxed(lean_object* v_sz_1068_, lean_object* v_i_1069_, lean_object* v_bs_1070_){
_start:
{
size_t v_sz_boxed_1071_; size_t v_i_boxed_1072_; lean_object* v_res_1073_; 
v_sz_boxed_1071_ = lean_unbox_usize(v_sz_1068_);
lean_dec(v_sz_1068_);
v_i_boxed_1072_ = lean_unbox_usize(v_i_1069_);
lean_dec(v_i_1069_);
v_res_1073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(v_sz_boxed_1071_, v_i_boxed_1072_, v_bs_1070_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(lean_object* v_e_1074_, lean_object* v___y_1075_){
_start:
{
uint8_t v___x_1077_; 
v___x_1077_ = l_Lean_Expr_hasMVar(v_e_1074_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_e_1074_);
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; lean_object* v_mctx_1080_; lean_object* v___x_1081_; lean_object* v_fst_1082_; lean_object* v_snd_1083_; lean_object* v___x_1084_; lean_object* v_cache_1085_; lean_object* v_zetaDeltaFVarIds_1086_; lean_object* v_postponed_1087_; lean_object* v_diag_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1097_; 
v___x_1079_ = lean_st_ref_get(v___y_1075_);
v_mctx_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc_ref(v_mctx_1080_);
lean_dec(v___x_1079_);
v___x_1081_ = l_Lean_instantiateMVarsCore(v_mctx_1080_, v_e_1074_);
v_fst_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_fst_1082_);
v_snd_1083_ = lean_ctor_get(v___x_1081_, 1);
lean_inc(v_snd_1083_);
lean_dec_ref(v___x_1081_);
v___x_1084_ = lean_st_ref_take(v___y_1075_);
v_cache_1085_ = lean_ctor_get(v___x_1084_, 1);
v_zetaDeltaFVarIds_1086_ = lean_ctor_get(v___x_1084_, 2);
v_postponed_1087_ = lean_ctor_get(v___x_1084_, 3);
v_diag_1088_ = lean_ctor_get(v___x_1084_, 4);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; 
v_unused_1098_ = lean_ctor_get(v___x_1084_, 0);
lean_dec(v_unused_1098_);
v___x_1090_ = v___x_1084_;
v_isShared_1091_ = v_isSharedCheck_1097_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_diag_1088_);
lean_inc(v_postponed_1087_);
lean_inc(v_zetaDeltaFVarIds_1086_);
lean_inc(v_cache_1085_);
lean_dec(v___x_1084_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1097_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v_snd_1083_);
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_snd_1083_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_cache_1085_);
lean_ctor_set(v_reuseFailAlloc_1096_, 2, v_zetaDeltaFVarIds_1086_);
lean_ctor_set(v_reuseFailAlloc_1096_, 3, v_postponed_1087_);
lean_ctor_set(v_reuseFailAlloc_1096_, 4, v_diag_1088_);
v___x_1093_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_st_ref_set(v___y_1075_, v___x_1093_);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_fst_1082_);
return v___x_1095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg___boxed(lean_object* v_e_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_1099_, v___y_1100_);
lean_dec(v___y_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; lean_object* v_ngen_1106_; lean_object* v_namePrefix_1107_; lean_object* v_idx_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1137_; 
v___x_1105_ = lean_st_ref_get(v___y_1103_);
v_ngen_1106_ = lean_ctor_get(v___x_1105_, 2);
lean_inc_ref(v_ngen_1106_);
lean_dec(v___x_1105_);
v_namePrefix_1107_ = lean_ctor_get(v_ngen_1106_, 0);
v_idx_1108_ = lean_ctor_get(v_ngen_1106_, 1);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_ngen_1106_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1110_ = v_ngen_1106_;
v_isShared_1111_ = v_isSharedCheck_1137_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_idx_1108_);
lean_inc(v_namePrefix_1107_);
lean_dec(v_ngen_1106_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1137_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v_env_1113_; lean_object* v_nextMacroScope_1114_; lean_object* v_auxDeclNGen_1115_; lean_object* v_traceState_1116_; lean_object* v_cache_1117_; lean_object* v_messages_1118_; lean_object* v_infoState_1119_; lean_object* v_snapshotTasks_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1135_; 
v___x_1112_ = lean_st_ref_take(v___y_1103_);
v_env_1113_ = lean_ctor_get(v___x_1112_, 0);
v_nextMacroScope_1114_ = lean_ctor_get(v___x_1112_, 1);
v_auxDeclNGen_1115_ = lean_ctor_get(v___x_1112_, 3);
v_traceState_1116_ = lean_ctor_get(v___x_1112_, 4);
v_cache_1117_ = lean_ctor_get(v___x_1112_, 5);
v_messages_1118_ = lean_ctor_get(v___x_1112_, 6);
v_infoState_1119_ = lean_ctor_get(v___x_1112_, 7);
v_snapshotTasks_1120_ = lean_ctor_get(v___x_1112_, 8);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; 
v_unused_1136_ = lean_ctor_get(v___x_1112_, 2);
lean_dec(v_unused_1136_);
v___x_1122_ = v___x_1112_;
v_isShared_1123_ = v_isSharedCheck_1135_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_snapshotTasks_1120_);
lean_inc(v_infoState_1119_);
lean_inc(v_messages_1118_);
lean_inc(v_cache_1117_);
lean_inc(v_traceState_1116_);
lean_inc(v_auxDeclNGen_1115_);
lean_inc(v_nextMacroScope_1114_);
lean_inc(v_env_1113_);
lean_dec(v___x_1112_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1135_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v_r_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
lean_inc(v_idx_1108_);
lean_inc(v_namePrefix_1107_);
v_r_1124_ = l_Lean_Name_num___override(v_namePrefix_1107_, v_idx_1108_);
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = lean_nat_add(v_idx_1108_, v___x_1125_);
lean_dec(v_idx_1108_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 1, v___x_1126_);
v___x_1128_ = v___x_1110_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_namePrefix_1107_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v___x_1130_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 2, v___x_1128_);
v___x_1130_ = v___x_1122_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_env_1113_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_nextMacroScope_1114_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1133_, 3, v_auxDeclNGen_1115_);
lean_ctor_set(v_reuseFailAlloc_1133_, 4, v_traceState_1116_);
lean_ctor_set(v_reuseFailAlloc_1133_, 5, v_cache_1117_);
lean_ctor_set(v_reuseFailAlloc_1133_, 6, v_messages_1118_);
lean_ctor_set(v_reuseFailAlloc_1133_, 7, v_infoState_1119_);
lean_ctor_set(v_reuseFailAlloc_1133_, 8, v_snapshotTasks_1120_);
v___x_1130_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_st_ref_set(v___y_1103_, v___x_1130_);
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_r_1124_);
return v___x_1132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1138_);
lean_dec(v___y_1138_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
v___x_1146_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1144_);
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3___boxed(lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(lean_object* v_fvars_1161_, lean_object* v_j_1162_, lean_object* v_x_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp(lean_box(0), v_fvars_1161_, v_j_1162_, v_x_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1169_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1169_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
v_a_1178_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1169_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1169_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_fvars_1186_, lean_object* v_j_1187_, lean_object* v_x_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1186_, v_j_1187_, v_x_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(lean_object* v_fvars_1195_, lean_object* v_j_1196_, lean_object* v_x_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1195_, v_j_1196_, v_x_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
v_a_1212_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1203_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1203_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg___boxed(lean_object* v_fvars_1220_, lean_object* v_j_1221_, lean_object* v_x_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(v_fvars_1220_, v_j_1221_, v_x_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1(lean_object* v_00_u03b1_1229_, lean_object* v_fvars_1230_, lean_object* v_j_1231_, lean_object* v_x_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(v_fvars_1230_, v_j_1231_, v_x_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1239_, lean_object* v_fvars_1240_, lean_object* v_j_1241_, lean_object* v_x_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1(v_00_u03b1_1239_, v_fvars_1240_, v_j_1241_, v_x_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(lean_object* v_x_1249_, lean_object* v_x_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_){
_start:
{
lean_object* v_ks_1253_; lean_object* v_vs_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1278_; 
v_ks_1253_ = lean_ctor_get(v_x_1249_, 0);
v_vs_1254_ = lean_ctor_get(v_x_1249_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_x_1249_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1256_ = v_x_1249_;
v_isShared_1257_ = v_isSharedCheck_1278_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_vs_1254_);
lean_inc(v_ks_1253_);
lean_dec(v_x_1249_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1278_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1258_ = lean_array_get_size(v_ks_1253_);
v___x_1259_ = lean_nat_dec_lt(v_x_1250_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1263_; 
lean_dec(v_x_1250_);
v___x_1260_ = lean_array_push(v_ks_1253_, v_x_1251_);
v___x_1261_ = lean_array_push(v_vs_1254_, v_x_1252_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v___x_1261_);
lean_ctor_set(v___x_1256_, 0, v___x_1260_);
v___x_1263_ = v___x_1256_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
else
{
lean_object* v_k_x27_1265_; uint8_t v___x_1266_; 
v_k_x27_1265_ = lean_array_fget_borrowed(v_ks_1253_, v_x_1250_);
v___x_1266_ = l_Lean_instBEqMVarId_beq(v_x_1251_, v_k_x27_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1268_; 
if (v_isShared_1257_ == 0)
{
v___x_1268_ = v___x_1256_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_ks_1253_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_vs_1254_);
v___x_1268_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_unsigned_to_nat(1u);
v___x_1270_ = lean_nat_add(v_x_1250_, v___x_1269_);
lean_dec(v_x_1250_);
v_x_1249_ = v___x_1268_;
v_x_1250_ = v___x_1270_;
goto _start;
}
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1273_ = lean_array_fset(v_ks_1253_, v_x_1250_, v_x_1251_);
v___x_1274_ = lean_array_fset(v_vs_1254_, v_x_1250_, v_x_1252_);
lean_dec(v_x_1250_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v___x_1274_);
lean_ctor_set(v___x_1256_, 0, v___x_1273_);
v___x_1276_ = v___x_1256_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(lean_object* v_n_1279_, lean_object* v_k_1280_, lean_object* v_v_1281_){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_unsigned_to_nat(0u);
v___x_1283_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(v_n_1279_, v___x_1282_, v_k_1280_, v_v_1281_);
return v___x_1283_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0(void){
_start:
{
size_t v___x_1284_; size_t v___x_1285_; size_t v___x_1286_; 
v___x_1284_ = ((size_t)5ULL);
v___x_1285_ = ((size_t)1ULL);
v___x_1286_ = lean_usize_shift_left(v___x_1285_, v___x_1284_);
return v___x_1286_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_1287_; size_t v___x_1288_; size_t v___x_1289_; 
v___x_1287_ = ((size_t)1ULL);
v___x_1288_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0);
v___x_1289_ = lean_usize_sub(v___x_1288_, v___x_1287_);
return v___x_1289_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_1291_, size_t v_x_1292_, size_t v_x_1293_, lean_object* v_x_1294_, lean_object* v_x_1295_){
_start:
{
if (lean_obj_tag(v_x_1291_) == 0)
{
lean_object* v_es_1296_; size_t v___x_1297_; size_t v___x_1298_; size_t v___x_1299_; size_t v___x_1300_; lean_object* v_j_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v_es_1296_ = lean_ctor_get(v_x_1291_, 0);
v___x_1297_ = ((size_t)5ULL);
v___x_1298_ = ((size_t)1ULL);
v___x_1299_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1);
v___x_1300_ = lean_usize_land(v_x_1292_, v___x_1299_);
v_j_1301_ = lean_usize_to_nat(v___x_1300_);
v___x_1302_ = lean_array_get_size(v_es_1296_);
v___x_1303_ = lean_nat_dec_lt(v_j_1301_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_dec(v_j_1301_);
lean_dec(v_x_1295_);
lean_dec(v_x_1294_);
return v_x_1291_;
}
else
{
lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1340_; 
lean_inc_ref(v_es_1296_);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_x_1291_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v_x_1291_, 0);
lean_dec(v_unused_1341_);
v___x_1305_ = v_x_1291_;
v_isShared_1306_ = v_isSharedCheck_1340_;
goto v_resetjp_1304_;
}
else
{
lean_dec(v_x_1291_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1340_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v_v_1307_; lean_object* v___x_1308_; lean_object* v_xs_x27_1309_; lean_object* v___y_1311_; 
v_v_1307_ = lean_array_fget(v_es_1296_, v_j_1301_);
v___x_1308_ = lean_box(0);
v_xs_x27_1309_ = lean_array_fset(v_es_1296_, v_j_1301_, v___x_1308_);
switch(lean_obj_tag(v_v_1307_))
{
case 0:
{
lean_object* v_key_1316_; lean_object* v_val_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1327_; 
v_key_1316_ = lean_ctor_get(v_v_1307_, 0);
v_val_1317_ = lean_ctor_get(v_v_1307_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_v_1307_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1319_ = v_v_1307_;
v_isShared_1320_ = v_isSharedCheck_1327_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_val_1317_);
lean_inc(v_key_1316_);
lean_dec(v_v_1307_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1327_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
uint8_t v___x_1321_; 
v___x_1321_ = l_Lean_instBEqMVarId_beq(v_x_1294_, v_key_1316_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_del_object(v___x_1319_);
v___x_1322_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1316_, v_val_1317_, v_x_1294_, v_x_1295_);
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
v___y_1311_ = v___x_1323_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1325_; 
lean_dec(v_val_1317_);
lean_dec(v_key_1316_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 1, v_x_1295_);
lean_ctor_set(v___x_1319_, 0, v_x_1294_);
v___x_1325_ = v___x_1319_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_x_1294_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_x_1295_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
v___y_1311_ = v___x_1325_;
goto v___jp_1310_;
}
}
}
}
case 1:
{
lean_object* v_node_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1338_; 
v_node_1328_ = lean_ctor_get(v_v_1307_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_v_1307_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1330_ = v_v_1307_;
v_isShared_1331_ = v_isSharedCheck_1338_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_node_1328_);
lean_dec(v_v_1307_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1338_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
size_t v___x_1332_; size_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1332_ = lean_usize_shift_right(v_x_1292_, v___x_1297_);
v___x_1333_ = lean_usize_add(v_x_1293_, v___x_1298_);
v___x_1334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_node_1328_, v___x_1332_, v___x_1333_, v_x_1294_, v_x_1295_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1334_);
v___x_1336_ = v___x_1330_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
v___y_1311_ = v___x_1336_;
goto v___jp_1310_;
}
}
}
default: 
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_x_1294_);
lean_ctor_set(v___x_1339_, 1, v_x_1295_);
v___y_1311_ = v___x_1339_;
goto v___jp_1310_;
}
}
v___jp_1310_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = lean_array_fset(v_xs_x27_1309_, v_j_1301_, v___y_1311_);
lean_dec(v_j_1301_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v___x_1312_);
v___x_1314_ = v___x_1305_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
else
{
lean_object* v_ks_1342_; lean_object* v_vs_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1363_; 
v_ks_1342_ = lean_ctor_get(v_x_1291_, 0);
v_vs_1343_ = lean_ctor_get(v_x_1291_, 1);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_x_1291_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1345_ = v_x_1291_;
v_isShared_1346_ = v_isSharedCheck_1363_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_vs_1343_);
lean_inc(v_ks_1342_);
lean_dec(v_x_1291_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1363_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_ks_1342_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_vs_1343_);
v___x_1348_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v_newNode_1349_; uint8_t v___y_1351_; size_t v___x_1357_; uint8_t v___x_1358_; 
v_newNode_1349_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(v___x_1348_, v_x_1294_, v_x_1295_);
v___x_1357_ = ((size_t)7ULL);
v___x_1358_ = lean_usize_dec_le(v___x_1357_, v_x_1293_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1359_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1349_);
v___x_1360_ = lean_unsigned_to_nat(4u);
v___x_1361_ = lean_nat_dec_lt(v___x_1359_, v___x_1360_);
lean_dec(v___x_1359_);
v___y_1351_ = v___x_1361_;
goto v___jp_1350_;
}
else
{
v___y_1351_ = v___x_1358_;
goto v___jp_1350_;
}
v___jp_1350_:
{
if (v___y_1351_ == 0)
{
lean_object* v_ks_1352_; lean_object* v_vs_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_ks_1352_ = lean_ctor_get(v_newNode_1349_, 0);
lean_inc_ref(v_ks_1352_);
v_vs_1353_ = lean_ctor_get(v_newNode_1349_, 1);
lean_inc_ref(v_vs_1353_);
lean_dec_ref(v_newNode_1349_);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2);
v___x_1356_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_x_1293_, v_ks_1352_, v_vs_1353_, v___x_1354_, v___x_1355_);
lean_dec_ref(v_vs_1353_);
lean_dec_ref(v_ks_1352_);
return v___x_1356_;
}
else
{
return v_newNode_1349_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(size_t v_depth_1364_, lean_object* v_keys_1365_, lean_object* v_vals_1366_, lean_object* v_i_1367_, lean_object* v_entries_1368_){
_start:
{
lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1369_ = lean_array_get_size(v_keys_1365_);
v___x_1370_ = lean_nat_dec_lt(v_i_1367_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_dec(v_i_1367_);
return v_entries_1368_;
}
else
{
lean_object* v_k_1371_; lean_object* v_v_1372_; uint64_t v___x_1373_; size_t v_h_1374_; size_t v___x_1375_; lean_object* v___x_1376_; size_t v___x_1377_; size_t v___x_1378_; size_t v___x_1379_; size_t v_h_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_k_1371_ = lean_array_fget_borrowed(v_keys_1365_, v_i_1367_);
v_v_1372_ = lean_array_fget_borrowed(v_vals_1366_, v_i_1367_);
v___x_1373_ = l_Lean_instHashableMVarId_hash(v_k_1371_);
v_h_1374_ = lean_uint64_to_usize(v___x_1373_);
v___x_1375_ = ((size_t)5ULL);
v___x_1376_ = lean_unsigned_to_nat(1u);
v___x_1377_ = ((size_t)1ULL);
v___x_1378_ = lean_usize_sub(v_depth_1364_, v___x_1377_);
v___x_1379_ = lean_usize_mul(v___x_1375_, v___x_1378_);
v_h_1380_ = lean_usize_shift_right(v_h_1374_, v___x_1379_);
v___x_1381_ = lean_nat_add(v_i_1367_, v___x_1376_);
lean_dec(v_i_1367_);
lean_inc(v_v_1372_);
lean_inc(v_k_1371_);
v___x_1382_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_entries_1368_, v_h_1380_, v_depth_1364_, v_k_1371_, v_v_1372_);
v_i_1367_ = v___x_1381_;
v_entries_1368_ = v___x_1382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_depth_1384_, lean_object* v_keys_1385_, lean_object* v_vals_1386_, lean_object* v_i_1387_, lean_object* v_entries_1388_){
_start:
{
size_t v_depth_boxed_1389_; lean_object* v_res_1390_; 
v_depth_boxed_1389_ = lean_unbox_usize(v_depth_1384_);
lean_dec(v_depth_1384_);
v_res_1390_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_boxed_1389_, v_keys_1385_, v_vals_1386_, v_i_1387_, v_entries_1388_);
lean_dec_ref(v_vals_1386_);
lean_dec_ref(v_keys_1385_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_x_1391_, lean_object* v_x_1392_, lean_object* v_x_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
size_t v_x_3902__boxed_1396_; size_t v_x_3903__boxed_1397_; lean_object* v_res_1398_; 
v_x_3902__boxed_1396_ = lean_unbox_usize(v_x_1392_);
lean_dec(v_x_1392_);
v_x_3903__boxed_1397_ = lean_unbox_usize(v_x_1393_);
lean_dec(v_x_1393_);
v_res_1398_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1391_, v_x_3902__boxed_1396_, v_x_3903__boxed_1397_, v_x_1394_, v_x_1395_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
uint64_t v___x_1402_; size_t v___x_1403_; size_t v___x_1404_; lean_object* v___x_1405_; 
v___x_1402_ = l_Lean_instHashableMVarId_hash(v_x_1400_);
v___x_1403_ = lean_uint64_to_usize(v___x_1402_);
v___x_1404_ = ((size_t)1ULL);
v___x_1405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1399_, v___x_1403_, v___x_1404_, v_x_1400_, v_x_1401_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(lean_object* v_mvarId_1406_, lean_object* v_val_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; lean_object* v_mctx_1411_; lean_object* v_cache_1412_; lean_object* v_zetaDeltaFVarIds_1413_; lean_object* v_postponed_1414_; lean_object* v_diag_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1442_; 
v___x_1410_ = lean_st_ref_take(v___y_1408_);
v_mctx_1411_ = lean_ctor_get(v___x_1410_, 0);
v_cache_1412_ = lean_ctor_get(v___x_1410_, 1);
v_zetaDeltaFVarIds_1413_ = lean_ctor_get(v___x_1410_, 2);
v_postponed_1414_ = lean_ctor_get(v___x_1410_, 3);
v_diag_1415_ = lean_ctor_get(v___x_1410_, 4);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1417_ = v___x_1410_;
v_isShared_1418_ = v_isSharedCheck_1442_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_diag_1415_);
lean_inc(v_postponed_1414_);
lean_inc(v_zetaDeltaFVarIds_1413_);
lean_inc(v_cache_1412_);
lean_inc(v_mctx_1411_);
lean_dec(v___x_1410_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1442_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_depth_1419_; lean_object* v_levelAssignDepth_1420_; lean_object* v_mvarCounter_1421_; lean_object* v_lDepth_1422_; lean_object* v_decls_1423_; lean_object* v_userNames_1424_; lean_object* v_lAssignment_1425_; lean_object* v_eAssignment_1426_; lean_object* v_dAssignment_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1441_; 
v_depth_1419_ = lean_ctor_get(v_mctx_1411_, 0);
v_levelAssignDepth_1420_ = lean_ctor_get(v_mctx_1411_, 1);
v_mvarCounter_1421_ = lean_ctor_get(v_mctx_1411_, 2);
v_lDepth_1422_ = lean_ctor_get(v_mctx_1411_, 3);
v_decls_1423_ = lean_ctor_get(v_mctx_1411_, 4);
v_userNames_1424_ = lean_ctor_get(v_mctx_1411_, 5);
v_lAssignment_1425_ = lean_ctor_get(v_mctx_1411_, 6);
v_eAssignment_1426_ = lean_ctor_get(v_mctx_1411_, 7);
v_dAssignment_1427_ = lean_ctor_get(v_mctx_1411_, 8);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_mctx_1411_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1429_ = v_mctx_1411_;
v_isShared_1430_ = v_isSharedCheck_1441_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_dAssignment_1427_);
lean_inc(v_eAssignment_1426_);
lean_inc(v_lAssignment_1425_);
lean_inc(v_userNames_1424_);
lean_inc(v_decls_1423_);
lean_inc(v_lDepth_1422_);
lean_inc(v_mvarCounter_1421_);
lean_inc(v_levelAssignDepth_1420_);
lean_inc(v_depth_1419_);
lean_dec(v_mctx_1411_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1441_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1431_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(v_eAssignment_1426_, v_mvarId_1406_, v_val_1407_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 7, v___x_1431_);
v___x_1433_ = v___x_1429_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_depth_1419_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_levelAssignDepth_1420_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_mvarCounter_1421_);
lean_ctor_set(v_reuseFailAlloc_1440_, 3, v_lDepth_1422_);
lean_ctor_set(v_reuseFailAlloc_1440_, 4, v_decls_1423_);
lean_ctor_set(v_reuseFailAlloc_1440_, 5, v_userNames_1424_);
lean_ctor_set(v_reuseFailAlloc_1440_, 6, v_lAssignment_1425_);
lean_ctor_set(v_reuseFailAlloc_1440_, 7, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1440_, 8, v_dAssignment_1427_);
v___x_1433_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1435_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1433_);
v___x_1435_ = v___x_1417_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_cache_1412_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v_zetaDeltaFVarIds_1413_);
lean_ctor_set(v_reuseFailAlloc_1439_, 3, v_postponed_1414_);
lean_ctor_set(v_reuseFailAlloc_1439_, 4, v_diag_1415_);
v___x_1435_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = lean_st_ref_set(v___y_1408_, v___x_1435_);
v___x_1437_ = lean_box(0);
v___x_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
return v___x_1438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg___boxed(lean_object* v_mvarId_1443_, lean_object* v_val_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1443_, v_val_1444_, v___y_1445_);
lean_dec(v___y_1445_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(lean_object* v_mvarId_1448_, lean_object* v_type_1449_, lean_object* v_fvars_1450_, uint8_t v_isZero_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1457_; 
lean_inc(v_mvarId_1448_);
v___x_1457_ = l_Lean_MVarId_getTag(v_mvarId_1448_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref(v___x_1457_);
v___x_1459_ = l_Lean_Expr_headBeta(v_type_1449_);
v___x_1460_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1459_, v_a_1458_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; uint8_t v___x_1462_; uint8_t v___x_1463_; lean_object* v___x_1464_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref(v___x_1460_);
v___x_1462_ = 0;
v___x_1463_ = 1;
lean_inc(v_a_1461_);
v___x_1464_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1450_, v_a_1461_, v___x_1462_, v_isZero_1451_, v___x_1462_, v_isZero_1451_, v___x_1463_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1466_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1465_);
lean_dec_ref(v___x_1464_);
v___x_1466_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1448_, v_a_1465_, v___y_1453_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1475_; 
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1475_ == 0)
{
lean_object* v_unused_1476_; 
v_unused_1476_ = lean_ctor_get(v___x_1466_, 0);
lean_dec(v_unused_1476_);
v___x_1468_ = v___x_1466_;
v_isShared_1469_ = v_isSharedCheck_1475_;
goto v_resetjp_1467_;
}
else
{
lean_dec(v___x_1466_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1475_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1470_ = l_Lean_Expr_mvarId_x21(v_a_1461_);
lean_dec(v_a_1461_);
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v_fvars_1450_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1471_);
v___x_1473_ = v___x_1468_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec(v_a_1461_);
lean_dec_ref(v_fvars_1450_);
v_a_1477_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1466_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1466_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_a_1461_);
lean_dec_ref(v_fvars_1450_);
lean_dec(v_mvarId_1448_);
v_a_1485_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1464_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1464_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_dec_ref(v_fvars_1450_);
lean_dec(v_mvarId_1448_);
v_a_1493_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1460_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1460_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec_ref(v_fvars_1450_);
lean_dec_ref(v_type_1449_);
lean_dec(v_mvarId_1448_);
v_a_1501_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1457_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1457_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0___boxed(lean_object* v_mvarId_1509_, lean_object* v_type_1510_, lean_object* v_fvars_1511_, lean_object* v_isZero_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
uint8_t v_isZero_boxed_1518_; lean_object* v_res_1519_; 
v_isZero_boxed_1518_ = lean_unbox(v_isZero_1512_);
v_res_1519_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(v_mvarId_1509_, v_type_1510_, v_fvars_1511_, v_isZero_boxed_1518_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(lean_object* v_lctx_1520_, lean_object* v_x_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_keyedConfig_1527_; uint8_t v_trackZetaDelta_1528_; lean_object* v_zetaDeltaSet_1529_; lean_object* v_localInstances_1530_; lean_object* v_defEqCtx_x3f_1531_; lean_object* v_synthPendingDepth_1532_; lean_object* v_canUnfold_x3f_1533_; uint8_t v_univApprox_1534_; uint8_t v_inTypeClassResolution_1535_; uint8_t v_cacheInferType_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_keyedConfig_1527_ = lean_ctor_get(v___y_1522_, 0);
v_trackZetaDelta_1528_ = lean_ctor_get_uint8(v___y_1522_, sizeof(void*)*7);
v_zetaDeltaSet_1529_ = lean_ctor_get(v___y_1522_, 1);
v_localInstances_1530_ = lean_ctor_get(v___y_1522_, 3);
v_defEqCtx_x3f_1531_ = lean_ctor_get(v___y_1522_, 4);
v_synthPendingDepth_1532_ = lean_ctor_get(v___y_1522_, 5);
v_canUnfold_x3f_1533_ = lean_ctor_get(v___y_1522_, 6);
v_univApprox_1534_ = lean_ctor_get_uint8(v___y_1522_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1535_ = lean_ctor_get_uint8(v___y_1522_, sizeof(void*)*7 + 2);
v_cacheInferType_1536_ = lean_ctor_get_uint8(v___y_1522_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_1533_);
lean_inc(v_synthPendingDepth_1532_);
lean_inc(v_defEqCtx_x3f_1531_);
lean_inc_ref(v_localInstances_1530_);
lean_inc(v_zetaDeltaSet_1529_);
lean_inc_ref(v_keyedConfig_1527_);
v___x_1537_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1537_, 0, v_keyedConfig_1527_);
lean_ctor_set(v___x_1537_, 1, v_zetaDeltaSet_1529_);
lean_ctor_set(v___x_1537_, 2, v_lctx_1520_);
lean_ctor_set(v___x_1537_, 3, v_localInstances_1530_);
lean_ctor_set(v___x_1537_, 4, v_defEqCtx_x3f_1531_);
lean_ctor_set(v___x_1537_, 5, v_synthPendingDepth_1532_);
lean_ctor_set(v___x_1537_, 6, v_canUnfold_x3f_1533_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*7, v_trackZetaDelta_1528_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*7 + 1, v_univApprox_1534_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1535_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*7 + 3, v_cacheInferType_1536_);
lean_inc(v___y_1525_);
lean_inc_ref(v___y_1524_);
lean_inc(v___y_1523_);
v___x_1538_ = lean_apply_5(v_x_1521_, v___x_1537_, v___y_1523_, v___y_1524_, v___y_1525_, lean_box(0));
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg___boxed(lean_object* v_lctx_1539_, lean_object* v_x_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1539_, v_x_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed(lean_object* v_type_1547_, lean_object* v_mvarId_1548_, lean_object* v_n_1549_, lean_object* v_preserveBinderNames_1550_, lean_object* v___x_1551_, lean_object* v_useNamesForExplicitOnly_1552_, lean_object* v_lctx_1553_, lean_object* v_fvars_1554_, lean_object* v___x_1555_, lean_object* v_s_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1562_; uint8_t v___x_4269__boxed_1563_; uint8_t v_useNamesForExplicitOnly_boxed_1564_; lean_object* v_res_1565_; 
v_preserveBinderNames_boxed_1562_ = lean_unbox(v_preserveBinderNames_1550_);
v___x_4269__boxed_1563_ = lean_unbox(v___x_1551_);
v_useNamesForExplicitOnly_boxed_1564_ = lean_unbox(v_useNamesForExplicitOnly_1552_);
v_res_1565_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(v_type_1547_, v_mvarId_1548_, v_n_1549_, v_preserveBinderNames_boxed_1562_, v___x_4269__boxed_1563_, v_useNamesForExplicitOnly_boxed_1564_, v_lctx_1553_, v_fvars_1554_, v___x_1555_, v_s_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v_n_1549_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(uint8_t v_preserveBinderNames_1566_, uint8_t v___x_1567_, uint8_t v_useNamesForExplicitOnly_1568_, lean_object* v_mvarId_1569_, lean_object* v_i_1570_, lean_object* v_lctx_1571_, lean_object* v_fvars_1572_, lean_object* v_j_1573_, lean_object* v_s_1574_, lean_object* v_type_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v_zero_1581_; uint8_t v_isZero_1582_; 
v_zero_1581_ = lean_unsigned_to_nat(0u);
v_isZero_1582_ = lean_nat_dec_eq(v_i_1570_, v_zero_1581_);
if (v_isZero_1582_ == 1)
{
lean_object* v___x_1583_; lean_object* v_type_1584_; lean_object* v___x_1585_; lean_object* v___f_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_dec(v_s_1574_);
lean_dec(v_i_1570_);
v___x_1583_ = lean_array_get_size(v_fvars_1572_);
v_type_1584_ = lean_expr_instantiate_rev_range(v_type_1575_, v_j_1573_, v___x_1583_, v_fvars_1572_);
lean_dec_ref(v_type_1575_);
v___x_1585_ = lean_box(v_isZero_1582_);
lean_inc_ref(v_fvars_1572_);
v___f_1586_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1586_, 0, v_mvarId_1569_);
lean_closure_set(v___f_1586_, 1, v_type_1584_);
lean_closure_set(v___f_1586_, 2, v_fvars_1572_);
lean_closure_set(v___f_1586_, 3, v___x_1585_);
v___x_1587_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed), 9, 4);
lean_closure_set(v___x_1587_, 0, lean_box(0));
lean_closure_set(v___x_1587_, 1, v_fvars_1572_);
lean_closure_set(v___x_1587_, 2, v_j_1573_);
lean_closure_set(v___x_1587_, 3, v___f_1586_);
v___x_1588_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1571_, v___x_1587_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
return v___x_1588_;
}
else
{
lean_object* v_one_1589_; lean_object* v_n_1590_; 
v_one_1589_ = lean_unsigned_to_nat(1u);
v_n_1590_ = lean_nat_sub(v_i_1570_, v_one_1589_);
lean_dec(v_i_1570_);
switch(lean_obj_tag(v_type_1575_))
{
case 8:
{
lean_object* v_declName_1591_; lean_object* v_type_1592_; lean_object* v_value_1593_; lean_object* v_body_1594_; lean_object* v___x_1595_; 
v_declName_1591_ = lean_ctor_get(v_type_1575_, 0);
lean_inc(v_declName_1591_);
v_type_1592_ = lean_ctor_get(v_type_1575_, 1);
lean_inc_ref(v_type_1592_);
v_value_1593_ = lean_ctor_get(v_type_1575_, 2);
lean_inc_ref(v_value_1593_);
v_body_1594_ = lean_ctor_get(v_type_1575_, 3);
lean_inc_ref(v_body_1594_);
lean_dec_ref(v_type_1575_);
v___x_1595_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; uint8_t v___x_1597_; lean_object* v___x_1598_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref(v___x_1595_);
v___x_1597_ = 1;
v___x_1598_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_1566_, v___x_1567_, v_useNamesForExplicitOnly_1568_, v_lctx_1571_, v_declName_1591_, v___x_1597_, v_s_1574_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v_fst_1600_; lean_object* v_snd_1601_; lean_object* v___x_1602_; lean_object* v_type_1603_; lean_object* v_type_1604_; lean_object* v_val_1605_; uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1598_);
v_fst_1600_ = lean_ctor_get(v_a_1599_, 0);
lean_inc(v_fst_1600_);
v_snd_1601_ = lean_ctor_get(v_a_1599_, 1);
lean_inc(v_snd_1601_);
lean_dec(v_a_1599_);
v___x_1602_ = lean_array_get_size(v_fvars_1572_);
v_type_1603_ = lean_expr_instantiate_rev_range(v_type_1592_, v_j_1573_, v___x_1602_, v_fvars_1572_);
lean_dec_ref(v_type_1592_);
v_type_1604_ = l_Lean_Expr_headBeta(v_type_1603_);
v_val_1605_ = lean_expr_instantiate_rev_range(v_value_1593_, v_j_1573_, v___x_1602_, v_fvars_1572_);
lean_dec_ref(v_value_1593_);
v___x_1606_ = 0;
lean_inc(v_a_1596_);
v___x_1607_ = l_Lean_LocalContext_mkLetDecl(v_lctx_1571_, v_a_1596_, v_fst_1600_, v_type_1604_, v_val_1605_, v_isZero_1582_, v___x_1606_);
v___x_1608_ = l_Lean_mkFVar(v_a_1596_);
v___x_1609_ = lean_array_push(v_fvars_1572_, v___x_1608_);
v_i_1570_ = v_n_1590_;
v_lctx_1571_ = v___x_1607_;
v_fvars_1572_ = v___x_1609_;
v_s_1574_ = v_snd_1601_;
v_type_1575_ = v_body_1594_;
goto _start;
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec(v_a_1596_);
lean_dec_ref(v_body_1594_);
lean_dec_ref(v_value_1593_);
lean_dec_ref(v_type_1592_);
lean_dec(v_n_1590_);
lean_dec(v_j_1573_);
lean_dec_ref(v_fvars_1572_);
lean_dec_ref(v_lctx_1571_);
lean_dec(v_mvarId_1569_);
v_a_1611_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1598_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1598_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
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
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec_ref(v_body_1594_);
lean_dec_ref(v_value_1593_);
lean_dec_ref(v_type_1592_);
lean_dec(v_declName_1591_);
lean_dec(v_n_1590_);
lean_dec(v_s_1574_);
lean_dec(v_j_1573_);
lean_dec_ref(v_fvars_1572_);
lean_dec_ref(v_lctx_1571_);
lean_dec(v_mvarId_1569_);
v_a_1619_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1595_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1595_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1627_; lean_object* v_binderType_1628_; lean_object* v_body_1629_; uint8_t v_binderInfo_1630_; lean_object* v___x_1631_; 
v_binderName_1627_ = lean_ctor_get(v_type_1575_, 0);
lean_inc(v_binderName_1627_);
v_binderType_1628_ = lean_ctor_get(v_type_1575_, 1);
lean_inc_ref(v_binderType_1628_);
v_body_1629_ = lean_ctor_get(v_type_1575_, 2);
lean_inc_ref(v_body_1629_);
v_binderInfo_1630_ = lean_ctor_get_uint8(v_type_1575_, sizeof(void*)*3 + 8);
lean_dec_ref(v_type_1575_);
v___x_1631_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; uint8_t v___x_1633_; lean_object* v___x_1634_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref(v___x_1631_);
v___x_1633_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_1630_);
v___x_1634_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_1566_, v___x_1567_, v_useNamesForExplicitOnly_1568_, v_lctx_1571_, v_binderName_1627_, v___x_1633_, v_s_1574_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v_fst_1636_; lean_object* v_snd_1637_; lean_object* v___x_1638_; lean_object* v_type_1639_; lean_object* v_type_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref(v___x_1634_);
v_fst_1636_ = lean_ctor_get(v_a_1635_, 0);
lean_inc(v_fst_1636_);
v_snd_1637_ = lean_ctor_get(v_a_1635_, 1);
lean_inc(v_snd_1637_);
lean_dec(v_a_1635_);
v___x_1638_ = lean_array_get_size(v_fvars_1572_);
v_type_1639_ = lean_expr_instantiate_rev_range(v_binderType_1628_, v_j_1573_, v___x_1638_, v_fvars_1572_);
lean_dec_ref(v_binderType_1628_);
v_type_1640_ = l_Lean_Expr_headBeta(v_type_1639_);
v___x_1641_ = 0;
lean_inc(v_a_1632_);
v___x_1642_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_1571_, v_a_1632_, v_fst_1636_, v_type_1640_, v_binderInfo_1630_, v___x_1641_);
v___x_1643_ = l_Lean_mkFVar(v_a_1632_);
v___x_1644_ = lean_array_push(v_fvars_1572_, v___x_1643_);
v_i_1570_ = v_n_1590_;
v_lctx_1571_ = v___x_1642_;
v_fvars_1572_ = v___x_1644_;
v_s_1574_ = v_snd_1637_;
v_type_1575_ = v_body_1629_;
goto _start;
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec(v_a_1632_);
lean_dec_ref(v_body_1629_);
lean_dec_ref(v_binderType_1628_);
lean_dec(v_n_1590_);
lean_dec(v_j_1573_);
lean_dec_ref(v_fvars_1572_);
lean_dec_ref(v_lctx_1571_);
lean_dec(v_mvarId_1569_);
v_a_1646_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1634_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1634_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec_ref(v_body_1629_);
lean_dec_ref(v_binderType_1628_);
lean_dec(v_binderName_1627_);
lean_dec(v_n_1590_);
lean_dec(v_s_1574_);
lean_dec(v_j_1573_);
lean_dec_ref(v_fvars_1572_);
lean_dec_ref(v_lctx_1571_);
lean_dec(v_mvarId_1569_);
v_a_1654_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1631_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1631_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
default: 
{
lean_object* v___x_1662_; lean_object* v_type_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___f_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1662_ = lean_array_get_size(v_fvars_1572_);
v_type_1663_ = lean_expr_instantiate_rev_range(v_type_1575_, v_j_1573_, v___x_1662_, v_fvars_1572_);
lean_dec_ref(v_type_1575_);
v___x_1664_ = lean_box(v_preserveBinderNames_1566_);
v___x_1665_ = lean_box(v___x_1567_);
v___x_1666_ = lean_box(v_useNamesForExplicitOnly_1568_);
lean_inc_ref(v_fvars_1572_);
lean_inc_ref(v_lctx_1571_);
v___f_1667_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed), 15, 10);
lean_closure_set(v___f_1667_, 0, v_type_1663_);
lean_closure_set(v___f_1667_, 1, v_mvarId_1569_);
lean_closure_set(v___f_1667_, 2, v_n_1590_);
lean_closure_set(v___f_1667_, 3, v___x_1664_);
lean_closure_set(v___f_1667_, 4, v___x_1665_);
lean_closure_set(v___f_1667_, 5, v___x_1666_);
lean_closure_set(v___f_1667_, 6, v_lctx_1571_);
lean_closure_set(v___f_1667_, 7, v_fvars_1572_);
lean_closure_set(v___f_1667_, 8, v___x_1662_);
lean_closure_set(v___f_1667_, 9, v_s_1574_);
v___x_1668_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed), 9, 4);
lean_closure_set(v___x_1668_, 0, lean_box(0));
lean_closure_set(v___x_1668_, 1, v_fvars_1572_);
lean_closure_set(v___x_1668_, 2, v_j_1573_);
lean_closure_set(v___x_1668_, 3, v___f_1667_);
v___x_1669_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1571_, v___x_1668_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
return v___x_1669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(lean_object* v_type_1670_, lean_object* v_mvarId_1671_, lean_object* v_n_1672_, uint8_t v_preserveBinderNames_1673_, uint8_t v___x_1674_, uint8_t v_useNamesForExplicitOnly_1675_, lean_object* v_lctx_1676_, lean_object* v_fvars_1677_, lean_object* v___x_1678_, lean_object* v_s_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_type_1670_, v___y_1681_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1687_; uint8_t v___y_1689_; uint8_t v___x_1710_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1686_);
lean_dec_ref(v___x_1685_);
v___x_1687_ = l_Lean_Expr_cleanupAnnotations(v_a_1686_);
v___x_1710_ = l_Lean_Expr_isForall(v___x_1687_);
if (v___x_1710_ == 0)
{
uint8_t v___x_1711_; 
v___x_1711_ = l_Lean_Expr_isLet(v___x_1687_);
v___y_1689_ = v___x_1711_;
goto v___jp_1688_;
}
else
{
v___y_1689_ = v___x_1710_;
goto v___jp_1688_;
}
v___jp_1688_:
{
if (v___y_1689_ == 0)
{
lean_object* v___x_1690_; 
lean_inc(v___y_1683_);
lean_inc_ref(v___y_1682_);
lean_inc(v___y_1681_);
lean_inc_ref(v___y_1680_);
v___x_1690_ = lean_whnf(v___x_1687_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; uint8_t v___x_1692_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref(v___x_1690_);
v___x_1692_ = l_Lean_Expr_isForall(v_a_1691_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec(v_a_1691_);
lean_dec(v_s_1679_);
lean_dec(v___x_1678_);
lean_dec_ref(v_fvars_1677_);
lean_dec_ref(v_lctx_1676_);
v___x_1693_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
v___x_1694_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4);
v___x_1695_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1693_, v_mvarId_1671_, v___x_1694_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v___x_1695_;
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1696_ = lean_unsigned_to_nat(1u);
v___x_1697_ = lean_nat_add(v_n_1672_, v___x_1696_);
v___x_1698_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1673_, v___x_1674_, v_useNamesForExplicitOnly_1675_, v_mvarId_1671_, v___x_1697_, v_lctx_1676_, v_fvars_1677_, v___x_1678_, v_s_1679_, v_a_1691_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v___x_1698_;
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v_s_1679_);
lean_dec(v___x_1678_);
lean_dec_ref(v_fvars_1677_);
lean_dec_ref(v_lctx_1676_);
lean_dec(v_mvarId_1671_);
v_a_1699_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1690_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1690_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
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
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = lean_unsigned_to_nat(1u);
v___x_1708_ = lean_nat_add(v_n_1672_, v___x_1707_);
v___x_1709_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1673_, v___x_1674_, v_useNamesForExplicitOnly_1675_, v_mvarId_1671_, v___x_1708_, v_lctx_1676_, v_fvars_1677_, v___x_1678_, v_s_1679_, v___x_1687_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v___x_1709_;
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v_s_1679_);
lean_dec(v___x_1678_);
lean_dec_ref(v_fvars_1677_);
lean_dec_ref(v_lctx_1676_);
lean_dec(v_mvarId_1671_);
v_a_1712_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1685_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1685_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___boxed(lean_object* v_preserveBinderNames_1720_, lean_object* v___x_1721_, lean_object* v_useNamesForExplicitOnly_1722_, lean_object* v_mvarId_1723_, lean_object* v_i_1724_, lean_object* v_lctx_1725_, lean_object* v_fvars_1726_, lean_object* v_j_1727_, lean_object* v_s_1728_, lean_object* v_type_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1735_; uint8_t v___x_4302__boxed_1736_; uint8_t v_useNamesForExplicitOnly_boxed_1737_; lean_object* v_res_1738_; 
v_preserveBinderNames_boxed_1735_ = lean_unbox(v_preserveBinderNames_1720_);
v___x_4302__boxed_1736_ = lean_unbox(v___x_1721_);
v_useNamesForExplicitOnly_boxed_1737_ = lean_unbox(v_useNamesForExplicitOnly_1722_);
v_res_1738_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_boxed_1735_, v___x_4302__boxed_1736_, v_useNamesForExplicitOnly_boxed_1737_, v_mvarId_1723_, v_i_1724_, v_lctx_1725_, v_fvars_1726_, v_j_1727_, v_s_1728_, v_type_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___lam__0(lean_object* v_mvarId_1739_, lean_object* v___x_1740_, lean_object* v___x_1741_, uint8_t v_preserveBinderNames_1742_, uint8_t v___x_1743_, uint8_t v_useNamesForExplicitOnly_1744_, lean_object* v_n_1745_, lean_object* v_givenNames_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1752_; 
lean_inc(v_mvarId_1739_);
v___x_1752_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1739_, v___x_1740_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v___x_1753_; 
lean_dec_ref(v___x_1752_);
lean_inc(v_mvarId_1739_);
v___x_1753_ = l_Lean_MVarId_getType(v_mvarId_1739_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v_lctx_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref(v___x_1753_);
v_lctx_1755_ = lean_ctor_get(v___y_1747_, 2);
lean_inc_ref(v_lctx_1755_);
v___x_1756_ = lean_mk_empty_array_with_capacity(v___x_1741_);
v___x_1757_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1742_, v___x_1743_, v_useNamesForExplicitOnly_1744_, v_mvarId_1739_, v_n_1745_, v_lctx_1755_, v___x_1756_, v___x_1741_, v_givenNames_1746_, v_a_1754_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v___y_1747_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1777_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1777_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1777_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v_fst_1762_; lean_object* v_snd_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1776_; 
v_fst_1762_ = lean_ctor_get(v_a_1758_, 0);
v_snd_1763_ = lean_ctor_get(v_a_1758_, 1);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_a_1758_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1765_ = v_a_1758_;
v_isShared_1766_ = v_isSharedCheck_1776_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_snd_1763_);
lean_inc(v_fst_1762_);
lean_dec(v_a_1758_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1776_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
size_t v_sz_1767_; size_t v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v_sz_1767_ = lean_array_size(v_fst_1762_);
v___x_1768_ = ((size_t)0ULL);
v___x_1769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(v_sz_1767_, v___x_1768_, v_fst_1762_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1769_);
v___x_1771_ = v___x_1765_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_snd_1763_);
v___x_1771_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1773_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1771_);
v___x_1773_ = v___x_1760_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
v_a_1778_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1757_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1757_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec_ref(v___y_1747_);
lean_dec(v_givenNames_1746_);
lean_dec(v_n_1745_);
lean_dec(v___x_1741_);
lean_dec(v_mvarId_1739_);
v_a_1786_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1753_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1753_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec_ref(v___y_1747_);
lean_dec(v_givenNames_1746_);
lean_dec(v_n_1745_);
lean_dec(v___x_1741_);
lean_dec(v_mvarId_1739_);
v_a_1794_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1752_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1752_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___lam__0___boxed(lean_object* v_mvarId_1802_, lean_object* v___x_1803_, lean_object* v___x_1804_, lean_object* v_preserveBinderNames_1805_, lean_object* v___x_1806_, lean_object* v_useNamesForExplicitOnly_1807_, lean_object* v_n_1808_, lean_object* v_givenNames_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1815_; uint8_t v___x_4532__boxed_1816_; uint8_t v_useNamesForExplicitOnly_boxed_1817_; lean_object* v_res_1818_; 
v_preserveBinderNames_boxed_1815_ = lean_unbox(v_preserveBinderNames_1805_);
v___x_4532__boxed_1816_ = lean_unbox(v___x_1806_);
v_useNamesForExplicitOnly_boxed_1817_ = lean_unbox(v_useNamesForExplicitOnly_1807_);
v_res_1818_ = l_Lean_Meta_introNCore___lam__0(v_mvarId_1802_, v___x_1803_, v___x_1804_, v_preserveBinderNames_boxed_1815_, v___x_4532__boxed_1816_, v_useNamesForExplicitOnly_boxed_1817_, v_n_1808_, v_givenNames_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore(lean_object* v_mvarId_1821_, lean_object* v_n_1822_, lean_object* v_givenNames_1823_, uint8_t v_useNamesForExplicitOnly_1824_, uint8_t v_preserveBinderNames_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1831_ = lean_unsigned_to_nat(0u);
v___x_1832_ = lean_nat_dec_eq(v_n_1822_, v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v_options_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___f_1840_; lean_object* v___x_1841_; 
v_options_1833_ = lean_ctor_get(v_a_1828_, 2);
v___x_1834_ = l_Lean_Meta_tactic_hygienic;
v___x_1835_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v_options_1833_, v___x_1834_);
v___x_1836_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
v___x_1837_ = lean_box(v_preserveBinderNames_1825_);
v___x_1838_ = lean_box(v___x_1835_);
v___x_1839_ = lean_box(v_useNamesForExplicitOnly_1824_);
lean_inc(v_mvarId_1821_);
v___f_1840_ = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1840_, 0, v_mvarId_1821_);
lean_closure_set(v___f_1840_, 1, v___x_1836_);
lean_closure_set(v___f_1840_, 2, v___x_1831_);
lean_closure_set(v___f_1840_, 3, v___x_1837_);
lean_closure_set(v___f_1840_, 4, v___x_1838_);
lean_closure_set(v___f_1840_, 5, v___x_1839_);
lean_closure_set(v___f_1840_, 6, v_n_1822_);
lean_closure_set(v___f_1840_, 7, v_givenNames_1823_);
v___x_1841_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_1821_, v___f_1840_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
return v___x_1841_;
}
else
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_dec(v_givenNames_1823_);
lean_dec(v_n_1822_);
v___x_1842_ = ((lean_object*)(l_Lean_Meta_introNCore___closed__0));
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
lean_ctor_set(v___x_1843_, 1, v_mvarId_1821_);
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
return v___x_1844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___boxed(lean_object* v_mvarId_1845_, lean_object* v_n_1846_, lean_object* v_givenNames_1847_, lean_object* v_useNamesForExplicitOnly_1848_, lean_object* v_preserveBinderNames_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
uint8_t v_useNamesForExplicitOnly_boxed_1855_; uint8_t v_preserveBinderNames_boxed_1856_; lean_object* v_res_1857_; 
v_useNamesForExplicitOnly_boxed_1855_ = lean_unbox(v_useNamesForExplicitOnly_1848_);
v_preserveBinderNames_boxed_1856_ = lean_unbox(v_preserveBinderNames_1849_);
v_res_1857_ = l_Lean_Meta_introNCore(v_mvarId_1845_, v_n_1846_, v_givenNames_1847_, v_useNamesForExplicitOnly_boxed_1855_, v_preserveBinderNames_boxed_1856_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(lean_object* v_00_u03b1_1858_, lean_object* v_lctx_1859_, lean_object* v_x_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1859_, v_x_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1867_, lean_object* v_lctx_1868_, lean_object* v_x_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(v_00_u03b1_1867_, v_lctx_1868_, v_x_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(lean_object* v_e_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_1876_, v___y_1878_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___boxed(lean_object* v_e_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(v_e_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(lean_object* v_mvarId_1890_, lean_object* v_val_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1890_, v_val_1891_, v___y_1893_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___boxed(lean_object* v_mvarId_1898_, lean_object* v_val_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(v_mvarId_1898_, v_val_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1906_, lean_object* v_fvars_1907_, lean_object* v_j_1908_, lean_object* v_x_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1907_, v_j_1908_, v_x_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1916_, lean_object* v_fvars_1917_, lean_object* v_j_1918_, lean_object* v_x_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(v_00_u03b1_1916_, v_fvars_1917_, v_j_1918_, v_x_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1929_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___boxed(lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1938_, lean_object* v_x_1939_, lean_object* v_x_1940_, lean_object* v_x_1941_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(v_x_1939_, v_x_1940_, v_x_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1943_, lean_object* v_x_1944_, size_t v_x_1945_, size_t v_x_1946_, lean_object* v_x_1947_, lean_object* v_x_1948_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1944_, v_x_1945_, v_x_1946_, v_x_1947_, v_x_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1950_, lean_object* v_x_1951_, lean_object* v_x_1952_, lean_object* v_x_1953_, lean_object* v_x_1954_, lean_object* v_x_1955_){
_start:
{
size_t v_x_4783__boxed_1956_; size_t v_x_4784__boxed_1957_; lean_object* v_res_1958_; 
v_x_4783__boxed_1956_ = lean_unbox_usize(v_x_1952_);
lean_dec(v_x_1952_);
v_x_4784__boxed_1957_ = lean_unbox_usize(v_x_1953_);
lean_dec(v_x_1953_);
v_res_1958_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1950_, v_x_1951_, v_x_4783__boxed_1956_, v_x_4784__boxed_1957_, v_x_1954_, v_x_1955_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11(lean_object* v_00_u03b2_1959_, lean_object* v_n_1960_, lean_object* v_k_1961_, lean_object* v_v_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(v_n_1960_, v_k_1961_, v_v_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(lean_object* v_00_u03b2_1964_, size_t v_depth_1965_, lean_object* v_keys_1966_, lean_object* v_vals_1967_, lean_object* v_heq_1968_, lean_object* v_i_1969_, lean_object* v_entries_1970_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_1965_, v_keys_1966_, v_vals_1967_, v_i_1969_, v_entries_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_1972_, lean_object* v_depth_1973_, lean_object* v_keys_1974_, lean_object* v_vals_1975_, lean_object* v_heq_1976_, lean_object* v_i_1977_, lean_object* v_entries_1978_){
_start:
{
size_t v_depth_boxed_1979_; lean_object* v_res_1980_; 
v_depth_boxed_1979_ = lean_unbox_usize(v_depth_1973_);
lean_dec(v_depth_1973_);
v_res_1980_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(v_00_u03b2_1972_, v_depth_boxed_1979_, v_keys_1974_, v_vals_1975_, v_heq_1976_, v_i_1977_, v_entries_1978_);
lean_dec_ref(v_vals_1975_);
lean_dec_ref(v_keys_1974_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1981_, lean_object* v_x_1982_, lean_object* v_x_1983_, lean_object* v_x_1984_, lean_object* v_x_1985_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(v_x_1982_, v_x_1983_, v_x_1984_, v_x_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introN(lean_object* v_mvarId_1987_, lean_object* v_n_1988_, lean_object* v_givenNames_1989_, uint8_t v_useNamesForExplicitOnly_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
uint8_t v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = 0;
v___x_1997_ = l_Lean_Meta_introNCore(v_mvarId_1987_, v_n_1988_, v_givenNames_1989_, v_useNamesForExplicitOnly_1990_, v___x_1996_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introN___boxed(lean_object* v_mvarId_1998_, lean_object* v_n_1999_, lean_object* v_givenNames_2000_, lean_object* v_useNamesForExplicitOnly_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
uint8_t v_useNamesForExplicitOnly_boxed_2007_; lean_object* v_res_2008_; 
v_useNamesForExplicitOnly_boxed_2007_ = lean_unbox(v_useNamesForExplicitOnly_2001_);
v_res_2008_ = l_Lean_MVarId_introN(v_mvarId_1998_, v_n_1999_, v_givenNames_2000_, v_useNamesForExplicitOnly_boxed_2007_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introNP(lean_object* v_mvarId_2009_, lean_object* v_n_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v___x_2016_; uint8_t v___x_2017_; uint8_t v___x_2018_; lean_object* v___x_2019_; 
v___x_2016_ = lean_box(0);
v___x_2017_ = 0;
v___x_2018_ = 1;
v___x_2019_ = l_Lean_Meta_introNCore(v_mvarId_2009_, v_n_2010_, v___x_2016_, v___x_2017_, v___x_2018_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introNP___boxed(lean_object* v_mvarId_2020_, lean_object* v_n_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Lean_MVarId_introNP(v_mvarId_2020_, v_n_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_);
lean_dec(v_a_2025_);
lean_dec_ref(v_a_2024_);
lean_dec(v_a_2023_);
lean_dec_ref(v_a_2022_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro(lean_object* v_mvarId_2028_, lean_object* v_name_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; uint8_t v___x_2038_; lean_object* v___x_2039_; 
v___x_2035_ = lean_unsigned_to_nat(1u);
v___x_2036_ = lean_box(0);
v___x_2037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2037_, 0, v_name_2029_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v___x_2038_ = 0;
v___x_2039_ = l_Lean_Meta_introNCore(v_mvarId_2028_, v___x_2035_, v___x_2037_, v___x_2038_, v___x_2038_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2059_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2059_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2059_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v_fst_2044_; lean_object* v_snd_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2058_; 
v_fst_2044_ = lean_ctor_get(v_a_2040_, 0);
v_snd_2045_ = lean_ctor_get(v_a_2040_, 1);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_a_2040_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2047_ = v_a_2040_;
v_isShared_2048_ = v_isSharedCheck_2058_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_snd_2045_);
lean_inc(v_fst_2044_);
lean_dec(v_a_2040_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2058_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; 
v___x_2049_ = lean_box(0);
v___x_2050_ = lean_unsigned_to_nat(0u);
v___x_2051_ = lean_array_get(v___x_2049_, v_fst_2044_, v___x_2050_);
lean_dec(v_fst_2044_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v___x_2051_);
v___x_2053_ = v___x_2047_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2051_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_snd_2045_);
v___x_2053_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2055_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2053_);
v___x_2055_ = v___x_2042_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
v_a_2060_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2039_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2039_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro___boxed(lean_object* v_mvarId_2068_, lean_object* v_name_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_MVarId_intro(v_mvarId_2068_, v_name_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core(lean_object* v_mvarId_2076_, uint8_t v_preserveBinderNames_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; lean_object* v___x_2086_; 
v___x_2083_ = lean_unsigned_to_nat(1u);
v___x_2084_ = lean_box(0);
v___x_2085_ = 0;
v___x_2086_ = l_Lean_Meta_introNCore(v_mvarId_2076_, v___x_2083_, v___x_2084_, v___x_2085_, v_preserveBinderNames_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2106_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2106_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2106_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v_fst_2091_; lean_object* v_snd_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2105_; 
v_fst_2091_ = lean_ctor_get(v_a_2087_, 0);
v_snd_2092_ = lean_ctor_get(v_a_2087_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_a_2087_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2094_ = v_a_2087_;
v_isShared_2095_ = v_isSharedCheck_2105_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_snd_2092_);
lean_inc(v_fst_2091_);
lean_dec(v_a_2087_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2105_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2096_ = lean_box(0);
v___x_2097_ = lean_unsigned_to_nat(0u);
v___x_2098_ = lean_array_get(v___x_2096_, v_fst_2091_, v___x_2097_);
lean_dec(v_fst_2091_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2098_);
v___x_2100_ = v___x_2094_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_snd_2092_);
v___x_2100_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2102_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2100_);
v___x_2102_ = v___x_2089_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
v_a_2107_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2086_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2086_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core___boxed(lean_object* v_mvarId_2115_, lean_object* v_preserveBinderNames_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
uint8_t v_preserveBinderNames_boxed_2122_; lean_object* v_res_2123_; 
v_preserveBinderNames_boxed_2122_ = lean_unbox(v_preserveBinderNames_2116_);
v_res_2123_ = l_Lean_Meta_intro1Core(v_mvarId_2115_, v_preserveBinderNames_boxed_2122_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1(lean_object* v_mvarId_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
uint8_t v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = 0;
v___x_2131_ = l_Lean_Meta_intro1Core(v_mvarId_2124_, v___x_2130_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___boxed(lean_object* v_mvarId_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_MVarId_intro1(v_mvarId_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1P(lean_object* v_mvarId_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
uint8_t v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = 1;
v___x_2146_ = l_Lean_Meta_intro1Core(v_mvarId_2139_, v___x_2145_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1P___boxed(lean_object* v_mvarId_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_MVarId_intro1P(v_mvarId_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
lean_dec(v_a_2151_);
lean_dec_ref(v_a_2150_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(lean_object* v_msgData_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; lean_object* v_env_2161_; lean_object* v___x_2162_; lean_object* v_mctx_2163_; lean_object* v_lctx_2164_; lean_object* v_options_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2160_ = lean_st_ref_get(v___y_2158_);
v_env_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc_ref(v_env_2161_);
lean_dec(v___x_2160_);
v___x_2162_ = lean_st_ref_get(v___y_2156_);
v_mctx_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc_ref(v_mctx_2163_);
lean_dec(v___x_2162_);
v_lctx_2164_ = lean_ctor_get(v___y_2155_, 2);
v_options_2165_ = lean_ctor_get(v___y_2157_, 2);
lean_inc_ref(v_options_2165_);
lean_inc_ref(v_lctx_2164_);
v___x_2166_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2166_, 0, v_env_2161_);
lean_ctor_set(v___x_2166_, 1, v_mctx_2163_);
lean_ctor_set(v___x_2166_, 2, v_lctx_2164_);
lean_ctor_set(v___x_2166_, 3, v_options_2165_);
v___x_2167_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
lean_ctor_set(v___x_2167_, 1, v_msgData_2154_);
v___x_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0___boxed(lean_object* v_msgData_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msgData_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(lean_object* v_msg_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_ref_2182_; lean_object* v___x_2183_; lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2192_; 
v_ref_2182_ = lean_ctor_get(v___y_2179_, 5);
v___x_2183_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msg_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2186_ = v___x_2183_;
v_isShared_2187_ = v_isSharedCheck_2192_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2192_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v___x_2190_; 
lean_inc(v_ref_2182_);
v___x_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2188_, 0, v_ref_2182_);
lean_ctor_set(v___x_2188_, 1, v_a_2184_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set_tag(v___x_2186_, 1);
lean_ctor_set(v___x_2186_, 0, v___x_2188_);
v___x_2190_ = v___x_2186_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg___boxed(lean_object* v_msg_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v_msg_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
return v_res_2199_;
}
}
static lean_object* _init_l_Lean_MVarId_intro1___00__lam__0___closed__1(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l_Lean_MVarId_intro1___00__lam__0___closed__0));
v___x_2202_ = l_Lean_stringToMessageData(v___x_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__lam__0(lean_object* v_mvarId_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v___x_2209_; 
lean_inc(v_mvarId_2203_);
v___x_2209_ = l_Lean_MVarId_getType_x27(v_mvarId_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref(v___x_2209_);
if (lean_obj_tag(v_a_2210_) == 7)
{
lean_object* v_binderName_2211_; lean_object* v_binderType_2212_; lean_object* v_body_2213_; uint8_t v_binderInfo_2214_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; uint8_t v___x_2251_; 
v_binderName_2211_ = lean_ctor_get(v_a_2210_, 0);
lean_inc(v_binderName_2211_);
v_binderType_2212_ = lean_ctor_get(v_a_2210_, 1);
lean_inc_ref(v_binderType_2212_);
v_body_2213_ = lean_ctor_get(v_a_2210_, 2);
lean_inc_ref(v_body_2213_);
v_binderInfo_2214_ = lean_ctor_get_uint8(v_a_2210_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_2210_);
v___x_2251_ = l_Lean_Expr_hasLooseBVars(v_body_2213_);
if (v___x_2251_ == 0)
{
v___y_2216_ = v___y_2204_;
v___y_2217_ = v___y_2205_;
v___y_2218_ = v___y_2206_;
v___y_2219_ = v___y_2207_;
goto v___jp_2215_;
}
else
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec_ref(v_body_2213_);
lean_dec_ref(v_binderType_2212_);
lean_dec(v_binderName_2211_);
v___x_2252_ = lean_obj_once(&l_Lean_MVarId_intro1___00__lam__0___closed__1, &l_Lean_MVarId_intro1___00__lam__0___closed__1_once, _init_l_Lean_MVarId_intro1___00__lam__0___closed__1);
v___x_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2253_, 0, v_mvarId_2203_);
v___x_2254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v___x_2254_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
v___jp_2215_:
{
lean_object* v___x_2220_; 
lean_inc(v_mvarId_2203_);
v___x_2220_ = l_Lean_MVarId_getTag(v_mvarId_2203_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2222_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref(v___x_2220_);
v___x_2222_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_body_2213_, v_a_2221_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2233_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
lean_dec_ref(v___x_2222_);
lean_inc(v_a_2223_);
v___x_2224_ = l_Lean_Expr_lam___override(v_binderName_2211_, v_binderType_2212_, v_a_2223_, v_binderInfo_2214_);
v___x_2225_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_2203_, v___x_2224_, v___y_2217_);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2233_ == 0)
{
lean_object* v_unused_2234_; 
v_unused_2234_ = lean_ctor_get(v___x_2225_, 0);
lean_dec(v_unused_2234_);
v___x_2227_ = v___x_2225_;
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
else
{
lean_dec(v___x_2225_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = l_Lean_Expr_mvarId_x21(v_a_2223_);
lean_dec(v_a_2223_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2229_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec_ref(v_binderType_2212_);
lean_dec(v_binderName_2211_);
lean_dec(v_mvarId_2203_);
v_a_2235_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2222_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2222_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec_ref(v_body_2213_);
lean_dec_ref(v_binderType_2212_);
lean_dec(v_binderName_2211_);
lean_dec(v_mvarId_2203_);
v_a_2243_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2220_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2220_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_dec(v_a_2210_);
v___x_2264_ = lean_obj_once(&l_Lean_MVarId_intro1___00__lam__0___closed__1, &l_Lean_MVarId_intro1___00__lam__0___closed__1_once, _init_l_Lean_MVarId_intro1___00__lam__0___closed__1);
v___x_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2265_, 0, v_mvarId_2203_);
v___x_2266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v___x_2266_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
return v___x_2267_;
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec(v_mvarId_2203_);
v_a_2268_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2209_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2209_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__lam__0___boxed(lean_object* v_mvarId_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_MVarId_intro1___00__lam__0(v_mvarId_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1__(lean_object* v_mvarId_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v___f_2289_; lean_object* v___x_2290_; 
lean_inc(v_mvarId_2283_);
v___f_2289_ = lean_alloc_closure((void*)(l_Lean_MVarId_intro1___00__lam__0___boxed), 6, 1);
lean_closure_set(v___f_2289_, 0, v_mvarId_2283_);
v___x_2290_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_2283_, v___f_2289_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__boxed(lean_object* v_mvarId_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_MVarId_intro1__(v_mvarId_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(lean_object* v_00_u03b1_2298_, lean_object* v_msg_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v_msg_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___boxed(lean_object* v_00_u03b1_2306_, lean_object* v_msg_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(v_00_u03b1_2306_, v_msg_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntrosSize(lean_object* v_x_2314_){
_start:
{
switch(lean_obj_tag(v_x_2314_))
{
case 7:
{
lean_object* v_body_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v_body_2315_ = lean_ctor_get(v_x_2314_, 2);
v___x_2316_ = l_Lean_Meta_getIntrosSize(v_body_2315_);
v___x_2317_ = lean_unsigned_to_nat(1u);
v___x_2318_ = lean_nat_add(v___x_2316_, v___x_2317_);
lean_dec(v___x_2316_);
return v___x_2318_;
}
case 8:
{
lean_object* v_body_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v_body_2319_ = lean_ctor_get(v_x_2314_, 3);
v___x_2320_ = l_Lean_Meta_getIntrosSize(v_body_2319_);
v___x_2321_ = lean_unsigned_to_nat(1u);
v___x_2322_ = lean_nat_add(v___x_2320_, v___x_2321_);
lean_dec(v___x_2320_);
return v___x_2322_;
}
case 10:
{
lean_object* v_expr_2323_; 
v_expr_2323_ = lean_ctor_get(v_x_2314_, 1);
v_x_2314_ = v_expr_2323_;
goto _start;
}
default: 
{
lean_object* v___x_2325_; 
v___x_2325_ = lean_unsigned_to_nat(0u);
return v___x_2325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntrosSize___boxed(lean_object* v_x_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_Meta_getIntrosSize(v_x_2326_);
lean_dec_ref(v_x_2326_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intros(lean_object* v_mvarId_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v___x_2334_; 
lean_inc(v_mvarId_2328_);
v___x_2334_ = l_Lean_MVarId_getType(v_mvarId_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2351_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref(v___x_2334_);
v___x_2336_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_a_2335_, v_a_2330_);
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2351_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2351_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2341_ = l_Lean_Meta_getIntrosSize(v_a_2337_);
lean_dec(v_a_2337_);
v___x_2342_ = lean_unsigned_to_nat(0u);
v___x_2343_ = lean_nat_dec_eq(v___x_2341_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_del_object(v___x_2339_);
v___x_2344_ = lean_box(0);
v___x_2345_ = l_Lean_Meta_introNCore(v_mvarId_2328_, v___x_2341_, v___x_2344_, v___x_2343_, v___x_2343_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_2345_;
}
else
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
lean_dec(v___x_2341_);
v___x_2346_ = ((lean_object*)(l_Lean_Meta_introNCore___closed__0));
v___x_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
lean_ctor_set(v___x_2347_, 1, v_mvarId_2328_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2347_);
v___x_2349_ = v___x_2339_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec(v_mvarId_2328_);
v_a_2352_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2334_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2334_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intros___boxed(lean_object* v_mvarId_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_MVarId_intros(v_mvarId_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
return v_res_2366_;
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
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_();
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
