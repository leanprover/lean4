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
lean_inc_n(v_a_15_, 2);
lean_dec_ref(v___x_14_);
v___x_16_ = 0;
v___x_17_ = 1;
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
lean_dec_ref(v_type_122_);
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
lean_dec_ref(v___x_202_);
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
lean_dec_ref(v___x_206_);
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
lean_dec_ref(v_type_122_);
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
lean_dec_ref(v___x_240_);
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
lean_dec_ref(v___x_244_);
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
lean_dec_ref(v___x_300_);
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
lean_dec_ref(v___x_305_);
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
lean_dec_ref(v___x_411_);
lean_inc(v_mvarId_400_);
v___x_412_ = l_Lean_MVarId_getType(v_mvarId_400_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v_lctx_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref(v___x_412_);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(lean_object* v_name_650_, lean_object* v_decl_651_, lean_object* v_ref_652_){
_start:
{
lean_object* v_defValue_654_; lean_object* v_descr_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_682_; 
v_defValue_654_ = lean_ctor_get(v_decl_651_, 0);
v_descr_655_ = lean_ctor_get(v_decl_651_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_decl_651_);
if (v_isSharedCheck_682_ == 0)
{
v___x_657_ = v_decl_651_;
v_isShared_658_ = v_isSharedCheck_682_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_descr_655_);
lean_inc(v_defValue_654_);
lean_dec(v_decl_651_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_682_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; uint8_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_659_ = lean_alloc_ctor(1, 0, 1);
v___x_660_ = lean_unbox(v_defValue_654_);
lean_ctor_set_uint8(v___x_659_, 0, v___x_660_);
lean_inc_n(v_name_650_, 2);
v___x_661_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_661_, 0, v_name_650_);
lean_ctor_set(v___x_661_, 1, v_ref_652_);
lean_ctor_set(v___x_661_, 2, v___x_659_);
lean_ctor_set(v___x_661_, 3, v_descr_655_);
v___x_662_ = lean_register_option(v_name_650_, v___x_661_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_672_; 
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v___x_662_, 0);
lean_dec(v_unused_673_);
v___x_664_ = v___x_662_;
v_isShared_665_ = v_isSharedCheck_672_;
goto v_resetjp_663_;
}
else
{
lean_dec(v___x_662_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_672_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v_defValue_654_);
lean_ctor_set(v___x_657_, 0, v_name_650_);
v___x_667_ = v___x_657_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_name_650_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_defValue_654_);
v___x_667_ = v_reuseFailAlloc_671_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_669_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_667_);
v___x_669_ = v___x_664_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
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
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_del_object(v___x_657_);
lean_dec(v_defValue_654_);
lean_dec(v_name_650_);
v_a_674_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_662_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_662_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_683_, lean_object* v_decl_684_, lean_object* v_ref_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(v_name_683_, v_decl_684_, v_ref_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_706_ = ((lean_object*)(l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_));
v___x_707_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_));
v___x_708_ = ((lean_object*)(l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_));
v___x_709_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(v___x_706_, v___x_707_, v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4____boxed(lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_();
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(lean_object* v_lctx_712_, lean_object* v_binderName_713_, uint8_t v_hygienic_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
if (v_hygienic_714_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = l_Lean_LocalContext_getUnusedName(v_lctx_712_, v_binderName_713_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
else
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Core_mkFreshUserName(v_binderName_713_, v_a_715_, v_a_716_);
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg___boxed(lean_object* v_lctx_721_, lean_object* v_binderName_722_, lean_object* v_hygienic_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
uint8_t v_hygienic_boxed_727_; lean_object* v_res_728_; 
v_hygienic_boxed_727_ = lean_unbox(v_hygienic_723_);
v_res_728_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_721_, v_binderName_722_, v_hygienic_boxed_727_, v_a_724_, v_a_725_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec_ref(v_lctx_721_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore(lean_object* v_lctx_729_, lean_object* v_binderName_730_, uint8_t v_hygienic_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_729_, v_binderName_730_, v_hygienic_731_, v_a_734_, v_a_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___boxed(lean_object* v_lctx_738_, lean_object* v_binderName_739_, lean_object* v_hygienic_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
uint8_t v_hygienic_boxed_746_; lean_object* v_res_747_; 
v_hygienic_boxed_746_ = lean_unbox(v_hygienic_740_);
v_res_747_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore(v_lctx_738_, v_binderName_739_, v_hygienic_boxed_746_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec_ref(v_lctx_738_);
return v_res_747_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(lean_object* v_opts_748_, lean_object* v_opt_749_){
_start:
{
lean_object* v_name_750_; lean_object* v_defValue_751_; lean_object* v_map_752_; lean_object* v___x_753_; 
v_name_750_ = lean_ctor_get(v_opt_749_, 0);
v_defValue_751_ = lean_ctor_get(v_opt_749_, 1);
v_map_752_ = lean_ctor_get(v_opts_748_, 0);
v___x_753_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_752_, v_name_750_);
if (lean_obj_tag(v___x_753_) == 0)
{
uint8_t v___x_754_; 
v___x_754_ = lean_unbox(v_defValue_751_);
return v___x_754_;
}
else
{
lean_object* v_val_755_; 
v_val_755_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_val_755_);
lean_dec_ref(v___x_753_);
if (lean_obj_tag(v_val_755_) == 1)
{
uint8_t v_v_756_; 
v_v_756_ = lean_ctor_get_uint8(v_val_755_, 0);
lean_dec_ref(v_val_755_);
return v_v_756_;
}
else
{
uint8_t v___x_757_; 
lean_dec(v_val_755_);
v___x_757_ = lean_unbox(v_defValue_751_);
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0___boxed(lean_object* v_opts_758_, lean_object* v_opt_759_){
_start:
{
uint8_t v_res_760_; lean_object* v_r_761_; 
v_res_760_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v_opts_758_, v_opt_759_);
lean_dec_ref(v_opt_759_);
lean_dec_ref(v_opts_758_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg(lean_object* v_binderName_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_lctx_767_; lean_object* v_options_768_; lean_object* v___x_769_; uint8_t v___x_770_; lean_object* v___x_771_; 
v_lctx_767_ = lean_ctor_get(v_a_763_, 2);
v_options_768_ = lean_ctor_get(v_a_764_, 2);
v___x_769_ = l_Lean_Meta_tactic_hygienic;
v___x_770_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v_options_768_, v___x_769_);
v___x_771_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_767_, v_binderName_762_, v___x_770_, v_a_764_, v_a_765_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg___boxed(lean_object* v_binderName_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_binderName_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec_ref(v_a_773_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic(lean_object* v_binderName_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_binderName_778_, v_a_779_, v_a_781_, v_a_782_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___boxed(lean_object* v_binderName_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Meta_mkFreshBinderNameForTactic(v_binderName_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(uint8_t v_preserveBinderNames_795_, uint8_t v_hygienic_796_, lean_object* v_lctx_797_, lean_object* v_binderName_798_, lean_object* v_rest_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_binderName_804_; lean_object* v___y_805_; lean_object* v___y_806_; uint8_t v___x_827_; 
v___x_827_ = l_Lean_Name_isAnonymous(v_binderName_798_);
if (v___x_827_ == 0)
{
v_binderName_804_ = v_binderName_798_;
v___y_805_ = v_a_800_;
v___y_806_ = v_a_801_;
goto v___jp_803_;
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec(v_binderName_798_);
v___x_828_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__1));
v___x_829_ = l_Lean_Core_mkFreshUserName(v___x_828_, v_a_800_, v_a_801_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref(v___x_829_);
v_binderName_804_ = v_a_830_;
v___y_805_ = v_a_800_;
v___y_806_ = v_a_801_;
goto v___jp_803_;
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v_rest_799_);
v_a_831_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_829_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_829_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
v___jp_803_:
{
if (v_preserveBinderNames_795_ == 0)
{
lean_object* v___x_807_; 
v___x_807_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_797_, v_binderName_804_, v_hygienic_796_, v___y_805_, v___y_806_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_816_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_816_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_816_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_816_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v_a_808_);
lean_ctor_set(v___x_812_, 1, v_rest_799_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_812_);
v___x_814_ = v___x_810_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec(v_rest_799_);
v_a_817_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_807_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_807_);
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
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
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
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_binderName_804_);
lean_ctor_set(v___x_825_, 1, v_rest_799_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___boxed(lean_object* v_preserveBinderNames_839_, lean_object* v_hygienic_840_, lean_object* v_lctx_841_, lean_object* v_binderName_842_, lean_object* v_rest_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
uint8_t v_preserveBinderNames_boxed_847_; uint8_t v_hygienic_boxed_848_; lean_object* v_res_849_; 
v_preserveBinderNames_boxed_847_ = lean_unbox(v_preserveBinderNames_839_);
v_hygienic_boxed_848_ = lean_unbox(v_hygienic_840_);
v_res_849_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_boxed_847_, v_hygienic_boxed_848_, v_lctx_841_, v_binderName_842_, v_rest_843_, v_a_844_, v_a_845_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec_ref(v_lctx_841_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(uint8_t v_preserveBinderNames_850_, uint8_t v_hygienic_851_, lean_object* v_lctx_852_, lean_object* v_binderName_853_, lean_object* v_rest_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_850_, v_hygienic_851_, v_lctx_852_, v_binderName_853_, v_rest_854_, v_a_857_, v_a_858_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___boxed(lean_object* v_preserveBinderNames_861_, lean_object* v_hygienic_862_, lean_object* v_lctx_863_, lean_object* v_binderName_864_, lean_object* v_rest_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
uint8_t v_preserveBinderNames_boxed_871_; uint8_t v_hygienic_boxed_872_; lean_object* v_res_873_; 
v_preserveBinderNames_boxed_871_ = lean_unbox(v_preserveBinderNames_861_);
v_hygienic_boxed_872_ = lean_unbox(v_hygienic_862_);
v_res_873_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(v_preserveBinderNames_boxed_871_, v_hygienic_boxed_872_, v_lctx_863_, v_binderName_864_, v_rest_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec_ref(v_lctx_863_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(uint8_t v_preserveBinderNames_878_, uint8_t v_hygienic_879_, uint8_t v_useNamesForExplicitOnly_880_, lean_object* v_lctx_881_, lean_object* v_binderName_882_, uint8_t v_isExplicit_883_, lean_object* v_x_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
if (lean_obj_tag(v_x_884_) == 0)
{
lean_object* v___x_888_; 
v___x_888_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_878_, v_hygienic_879_, v_lctx_881_, v_binderName_882_, v_x_884_, v_a_885_, v_a_886_);
return v___x_888_;
}
else
{
lean_object* v_head_889_; lean_object* v_tail_890_; 
v_head_889_ = lean_ctor_get(v_x_884_, 0);
v_tail_890_ = lean_ctor_get(v_x_884_, 1);
if (v_useNamesForExplicitOnly_880_ == 0)
{
lean_inc(v_tail_890_);
lean_inc(v_head_889_);
lean_dec_ref(v_x_884_);
goto v___jp_891_;
}
else
{
if (v_isExplicit_883_ == 0)
{
lean_object* v___x_897_; 
v___x_897_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_878_, v_hygienic_879_, v_lctx_881_, v_binderName_882_, v_x_884_, v_a_885_, v_a_886_);
return v___x_897_;
}
else
{
lean_inc(v_tail_890_);
lean_inc(v_head_889_);
lean_dec_ref(v_x_884_);
goto v___jp_891_;
}
}
v___jp_891_:
{
lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_892_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__1));
v___x_893_ = lean_name_eq(v_head_889_, v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec(v_binderName_882_);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v_head_889_);
lean_ctor_set(v___x_894_, 1, v_tail_890_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
else
{
lean_object* v___x_896_; 
lean_dec(v_head_889_);
v___x_896_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_878_, v_hygienic_879_, v_lctx_881_, v_binderName_882_, v_tail_890_, v_a_885_, v_a_886_);
return v___x_896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___boxed(lean_object* v_preserveBinderNames_898_, lean_object* v_hygienic_899_, lean_object* v_useNamesForExplicitOnly_900_, lean_object* v_lctx_901_, lean_object* v_binderName_902_, lean_object* v_isExplicit_903_, lean_object* v_x_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
uint8_t v_preserveBinderNames_boxed_908_; uint8_t v_hygienic_boxed_909_; uint8_t v_useNamesForExplicitOnly_boxed_910_; uint8_t v_isExplicit_boxed_911_; lean_object* v_res_912_; 
v_preserveBinderNames_boxed_908_ = lean_unbox(v_preserveBinderNames_898_);
v_hygienic_boxed_909_ = lean_unbox(v_hygienic_899_);
v_useNamesForExplicitOnly_boxed_910_ = lean_unbox(v_useNamesForExplicitOnly_900_);
v_isExplicit_boxed_911_ = lean_unbox(v_isExplicit_903_);
v_res_912_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_boxed_908_, v_hygienic_boxed_909_, v_useNamesForExplicitOnly_boxed_910_, v_lctx_901_, v_binderName_902_, v_isExplicit_boxed_911_, v_x_904_, v_a_905_, v_a_906_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec_ref(v_lctx_901_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(uint8_t v_preserveBinderNames_913_, uint8_t v_hygienic_914_, uint8_t v_useNamesForExplicitOnly_915_, lean_object* v_lctx_916_, lean_object* v_binderName_917_, uint8_t v_isExplicit_918_, lean_object* v_x_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_913_, v_hygienic_914_, v_useNamesForExplicitOnly_915_, v_lctx_916_, v_binderName_917_, v_isExplicit_918_, v_x_919_, v_a_922_, v_a_923_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___boxed(lean_object* v_preserveBinderNames_926_, lean_object* v_hygienic_927_, lean_object* v_useNamesForExplicitOnly_928_, lean_object* v_lctx_929_, lean_object* v_binderName_930_, lean_object* v_isExplicit_931_, lean_object* v_x_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
uint8_t v_preserveBinderNames_boxed_938_; uint8_t v_hygienic_boxed_939_; uint8_t v_useNamesForExplicitOnly_boxed_940_; uint8_t v_isExplicit_boxed_941_; lean_object* v_res_942_; 
v_preserveBinderNames_boxed_938_ = lean_unbox(v_preserveBinderNames_926_);
v_hygienic_boxed_939_ = lean_unbox(v_hygienic_927_);
v_useNamesForExplicitOnly_boxed_940_ = lean_unbox(v_useNamesForExplicitOnly_928_);
v_isExplicit_boxed_941_ = lean_unbox(v_isExplicit_931_);
v_res_942_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(v_preserveBinderNames_boxed_938_, v_hygienic_boxed_939_, v_useNamesForExplicitOnly_boxed_940_, v_lctx_929_, v_binderName_930_, v_isExplicit_boxed_941_, v_x_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec_ref(v_lctx_929_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(lean_object* v_mvarId_943_, lean_object* v_x_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_943_, v_x_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_950_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
v_a_959_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_950_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_950_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg___boxed(lean_object* v_mvarId_967_, lean_object* v_x_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_967_, v_x_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(lean_object* v_00_u03b1_975_, lean_object* v_mvarId_976_, lean_object* v_x_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_976_, v_x_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___boxed(lean_object* v_00_u03b1_984_, lean_object* v_mvarId_985_, lean_object* v_x_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(v_00_u03b1_984_, v_mvarId_985_, v_x_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(size_t v_sz_993_, size_t v_i_994_, lean_object* v_bs_995_){
_start:
{
uint8_t v___x_996_; 
v___x_996_ = lean_usize_dec_lt(v_i_994_, v_sz_993_);
if (v___x_996_ == 0)
{
return v_bs_995_;
}
else
{
lean_object* v_v_997_; lean_object* v___x_998_; lean_object* v_bs_x27_999_; lean_object* v___x_1000_; size_t v___x_1001_; size_t v___x_1002_; lean_object* v___x_1003_; 
v_v_997_ = lean_array_uget(v_bs_995_, v_i_994_);
v___x_998_ = lean_unsigned_to_nat(0u);
v_bs_x27_999_ = lean_array_uset(v_bs_995_, v_i_994_, v___x_998_);
v___x_1000_ = l_Lean_Expr_fvarId_x21(v_v_997_);
lean_dec(v_v_997_);
v___x_1001_ = ((size_t)1ULL);
v___x_1002_ = lean_usize_add(v_i_994_, v___x_1001_);
v___x_1003_ = lean_array_uset(v_bs_x27_999_, v_i_994_, v___x_1000_);
v_i_994_ = v___x_1002_;
v_bs_995_ = v___x_1003_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1___boxed(lean_object* v_sz_1005_, lean_object* v_i_1006_, lean_object* v_bs_1007_){
_start:
{
size_t v_sz_boxed_1008_; size_t v_i_boxed_1009_; lean_object* v_res_1010_; 
v_sz_boxed_1008_ = lean_unbox_usize(v_sz_1005_);
lean_dec(v_sz_1005_);
v_i_boxed_1009_ = lean_unbox_usize(v_i_1006_);
lean_dec(v_i_1006_);
v_res_1010_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(v_sz_boxed_1008_, v_i_boxed_1009_, v_bs_1007_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(lean_object* v_e_1011_, lean_object* v___y_1012_){
_start:
{
uint8_t v___x_1014_; 
v___x_1014_ = l_Lean_Expr_hasMVar(v_e_1011_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v_e_1011_);
return v___x_1015_;
}
else
{
lean_object* v___x_1016_; lean_object* v_mctx_1017_; lean_object* v___x_1018_; lean_object* v_fst_1019_; lean_object* v_snd_1020_; lean_object* v___x_1021_; lean_object* v_cache_1022_; lean_object* v_zetaDeltaFVarIds_1023_; lean_object* v_postponed_1024_; lean_object* v_diag_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1034_; 
v___x_1016_ = lean_st_ref_get(v___y_1012_);
v_mctx_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc_ref(v_mctx_1017_);
lean_dec(v___x_1016_);
v___x_1018_ = l_Lean_instantiateMVarsCore(v_mctx_1017_, v_e_1011_);
v_fst_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_fst_1019_);
v_snd_1020_ = lean_ctor_get(v___x_1018_, 1);
lean_inc(v_snd_1020_);
lean_dec_ref(v___x_1018_);
v___x_1021_ = lean_st_ref_take(v___y_1012_);
v_cache_1022_ = lean_ctor_get(v___x_1021_, 1);
v_zetaDeltaFVarIds_1023_ = lean_ctor_get(v___x_1021_, 2);
v_postponed_1024_ = lean_ctor_get(v___x_1021_, 3);
v_diag_1025_ = lean_ctor_get(v___x_1021_, 4);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; 
v_unused_1035_ = lean_ctor_get(v___x_1021_, 0);
lean_dec(v_unused_1035_);
v___x_1027_ = v___x_1021_;
v_isShared_1028_ = v_isSharedCheck_1034_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_diag_1025_);
lean_inc(v_postponed_1024_);
lean_inc(v_zetaDeltaFVarIds_1023_);
lean_inc(v_cache_1022_);
lean_dec(v___x_1021_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1034_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v_snd_1020_);
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_snd_1020_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_cache_1022_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v_zetaDeltaFVarIds_1023_);
lean_ctor_set(v_reuseFailAlloc_1033_, 3, v_postponed_1024_);
lean_ctor_set(v_reuseFailAlloc_1033_, 4, v_diag_1025_);
v___x_1030_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_st_ref_set(v___y_1012_, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v_fst_1019_);
return v___x_1032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg___boxed(lean_object* v_e_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_1036_, v___y_1037_);
lean_dec(v___y_1037_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; lean_object* v_ngen_1043_; lean_object* v_namePrefix_1044_; lean_object* v_idx_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1074_; 
v___x_1042_ = lean_st_ref_get(v___y_1040_);
v_ngen_1043_ = lean_ctor_get(v___x_1042_, 2);
lean_inc_ref(v_ngen_1043_);
lean_dec(v___x_1042_);
v_namePrefix_1044_ = lean_ctor_get(v_ngen_1043_, 0);
v_idx_1045_ = lean_ctor_get(v_ngen_1043_, 1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_ngen_1043_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1047_ = v_ngen_1043_;
v_isShared_1048_ = v_isSharedCheck_1074_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_idx_1045_);
lean_inc(v_namePrefix_1044_);
lean_dec(v_ngen_1043_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1074_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v_env_1050_; lean_object* v_nextMacroScope_1051_; lean_object* v_auxDeclNGen_1052_; lean_object* v_traceState_1053_; lean_object* v_cache_1054_; lean_object* v_messages_1055_; lean_object* v_infoState_1056_; lean_object* v_snapshotTasks_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1072_; 
v___x_1049_ = lean_st_ref_take(v___y_1040_);
v_env_1050_ = lean_ctor_get(v___x_1049_, 0);
v_nextMacroScope_1051_ = lean_ctor_get(v___x_1049_, 1);
v_auxDeclNGen_1052_ = lean_ctor_get(v___x_1049_, 3);
v_traceState_1053_ = lean_ctor_get(v___x_1049_, 4);
v_cache_1054_ = lean_ctor_get(v___x_1049_, 5);
v_messages_1055_ = lean_ctor_get(v___x_1049_, 6);
v_infoState_1056_ = lean_ctor_get(v___x_1049_, 7);
v_snapshotTasks_1057_ = lean_ctor_get(v___x_1049_, 8);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; 
v_unused_1073_ = lean_ctor_get(v___x_1049_, 2);
lean_dec(v_unused_1073_);
v___x_1059_ = v___x_1049_;
v_isShared_1060_ = v_isSharedCheck_1072_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_snapshotTasks_1057_);
lean_inc(v_infoState_1056_);
lean_inc(v_messages_1055_);
lean_inc(v_cache_1054_);
lean_inc(v_traceState_1053_);
lean_inc(v_auxDeclNGen_1052_);
lean_inc(v_nextMacroScope_1051_);
lean_inc(v_env_1050_);
lean_dec(v___x_1049_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1072_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v_r_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
lean_inc(v_idx_1045_);
lean_inc(v_namePrefix_1044_);
v_r_1061_ = l_Lean_Name_num___override(v_namePrefix_1044_, v_idx_1045_);
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = lean_nat_add(v_idx_1045_, v___x_1062_);
lean_dec(v_idx_1045_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 1, v___x_1063_);
v___x_1065_ = v___x_1047_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_namePrefix_1044_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1067_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 2, v___x_1065_);
v___x_1067_ = v___x_1059_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_env_1050_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_nextMacroScope_1051_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v_auxDeclNGen_1052_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v_traceState_1053_);
lean_ctor_set(v_reuseFailAlloc_1070_, 5, v_cache_1054_);
lean_ctor_set(v_reuseFailAlloc_1070_, 6, v_messages_1055_);
lean_ctor_set(v_reuseFailAlloc_1070_, 7, v_infoState_1056_);
lean_ctor_set(v_reuseFailAlloc_1070_, 8, v_snapshotTasks_1057_);
v___x_1067_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_st_ref_set(v___y_1040_, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_r_1061_);
return v___x_1069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1075_);
lean_dec(v___y_1075_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v___x_1083_; lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
v___x_1083_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1081_);
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3___boxed(lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(lean_object* v_fvars_1098_, lean_object* v_j_1099_, lean_object* v_x_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp(lean_box(0), v_fvars_1098_, v_j_1099_, v_x_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
v_a_1115_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1106_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1106_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_fvars_1123_, lean_object* v_j_1124_, lean_object* v_x_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1123_, v_j_1124_, v_x_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(lean_object* v_fvars_1132_, lean_object* v_j_1133_, lean_object* v_x_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1132_, v_j_1133_, v_x_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1140_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1140_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
v_a_1149_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1140_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1140_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg___boxed(lean_object* v_fvars_1157_, lean_object* v_j_1158_, lean_object* v_x_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(v_fvars_1157_, v_j_1158_, v_x_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1(lean_object* v_00_u03b1_1166_, lean_object* v_fvars_1167_, lean_object* v_j_1168_, lean_object* v_x_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(v_fvars_1167_, v_j_1168_, v_x_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1176_, lean_object* v_fvars_1177_, lean_object* v_j_1178_, lean_object* v_x_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1(v_00_u03b1_1176_, v_fvars_1177_, v_j_1178_, v_x_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(lean_object* v_x_1186_, lean_object* v_x_1187_, lean_object* v_x_1188_, lean_object* v_x_1189_){
_start:
{
lean_object* v_ks_1190_; lean_object* v_vs_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1215_; 
v_ks_1190_ = lean_ctor_get(v_x_1186_, 0);
v_vs_1191_ = lean_ctor_get(v_x_1186_, 1);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_x_1186_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1193_ = v_x_1186_;
v_isShared_1194_ = v_isSharedCheck_1215_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_vs_1191_);
lean_inc(v_ks_1190_);
lean_dec(v_x_1186_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1215_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = lean_array_get_size(v_ks_1190_);
v___x_1196_ = lean_nat_dec_lt(v_x_1187_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
lean_dec(v_x_1187_);
v___x_1197_ = lean_array_push(v_ks_1190_, v_x_1188_);
v___x_1198_ = lean_array_push(v_vs_1191_, v_x_1189_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v___x_1198_);
lean_ctor_set(v___x_1193_, 0, v___x_1197_);
v___x_1200_ = v___x_1193_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
else
{
lean_object* v_k_x27_1202_; uint8_t v___x_1203_; 
v_k_x27_1202_ = lean_array_fget_borrowed(v_ks_1190_, v_x_1187_);
v___x_1203_ = l_Lean_instBEqMVarId_beq(v_x_1188_, v_k_x27_1202_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1205_; 
if (v_isShared_1194_ == 0)
{
v___x_1205_ = v___x_1193_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_ks_1190_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_vs_1191_);
v___x_1205_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_unsigned_to_nat(1u);
v___x_1207_ = lean_nat_add(v_x_1187_, v___x_1206_);
lean_dec(v_x_1187_);
v_x_1186_ = v___x_1205_;
v_x_1187_ = v___x_1207_;
goto _start;
}
}
else
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1210_ = lean_array_fset(v_ks_1190_, v_x_1187_, v_x_1188_);
v___x_1211_ = lean_array_fset(v_vs_1191_, v_x_1187_, v_x_1189_);
lean_dec(v_x_1187_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v___x_1211_);
lean_ctor_set(v___x_1193_, 0, v___x_1210_);
v___x_1213_ = v___x_1193_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(lean_object* v_n_1216_, lean_object* v_k_1217_, lean_object* v_v_1218_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(v_n_1216_, v___x_1219_, v_k_1217_, v_v_1218_);
return v___x_1220_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0(void){
_start:
{
size_t v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; 
v___x_1221_ = ((size_t)5ULL);
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_shift_left(v___x_1222_, v___x_1221_);
return v___x_1223_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_1224_; size_t v___x_1225_; size_t v___x_1226_; 
v___x_1224_ = ((size_t)1ULL);
v___x_1225_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0);
v___x_1226_ = lean_usize_sub(v___x_1225_, v___x_1224_);
return v___x_1226_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_1228_, size_t v_x_1229_, size_t v_x_1230_, lean_object* v_x_1231_, lean_object* v_x_1232_){
_start:
{
if (lean_obj_tag(v_x_1228_) == 0)
{
lean_object* v_es_1233_; size_t v___x_1234_; size_t v___x_1235_; size_t v___x_1236_; size_t v___x_1237_; lean_object* v_j_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v_es_1233_ = lean_ctor_get(v_x_1228_, 0);
v___x_1234_ = ((size_t)5ULL);
v___x_1235_ = ((size_t)1ULL);
v___x_1236_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1);
v___x_1237_ = lean_usize_land(v_x_1229_, v___x_1236_);
v_j_1238_ = lean_usize_to_nat(v___x_1237_);
v___x_1239_ = lean_array_get_size(v_es_1233_);
v___x_1240_ = lean_nat_dec_lt(v_j_1238_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_dec(v_j_1238_);
lean_dec(v_x_1232_);
lean_dec(v_x_1231_);
return v_x_1228_;
}
else
{
lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1277_; 
lean_inc_ref(v_es_1233_);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_x_1228_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v_x_1228_, 0);
lean_dec(v_unused_1278_);
v___x_1242_ = v_x_1228_;
v_isShared_1243_ = v_isSharedCheck_1277_;
goto v_resetjp_1241_;
}
else
{
lean_dec(v_x_1228_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1277_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_v_1244_; lean_object* v___x_1245_; lean_object* v_xs_x27_1246_; lean_object* v___y_1248_; 
v_v_1244_ = lean_array_fget(v_es_1233_, v_j_1238_);
v___x_1245_ = lean_box(0);
v_xs_x27_1246_ = lean_array_fset(v_es_1233_, v_j_1238_, v___x_1245_);
switch(lean_obj_tag(v_v_1244_))
{
case 0:
{
lean_object* v_key_1253_; lean_object* v_val_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1264_; 
v_key_1253_ = lean_ctor_get(v_v_1244_, 0);
v_val_1254_ = lean_ctor_get(v_v_1244_, 1);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_v_1244_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1256_ = v_v_1244_;
v_isShared_1257_ = v_isSharedCheck_1264_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_val_1254_);
lean_inc(v_key_1253_);
lean_dec(v_v_1244_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1264_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
uint8_t v___x_1258_; 
v___x_1258_ = l_Lean_instBEqMVarId_beq(v_x_1231_, v_key_1253_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_del_object(v___x_1256_);
v___x_1259_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1253_, v_val_1254_, v_x_1231_, v_x_1232_);
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
v___y_1248_ = v___x_1260_;
goto v___jp_1247_;
}
else
{
lean_object* v___x_1262_; 
lean_dec(v_val_1254_);
lean_dec(v_key_1253_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v_x_1232_);
lean_ctor_set(v___x_1256_, 0, v_x_1231_);
v___x_1262_ = v___x_1256_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_x_1231_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_x_1232_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
v___y_1248_ = v___x_1262_;
goto v___jp_1247_;
}
}
}
}
case 1:
{
lean_object* v_node_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1275_; 
v_node_1265_ = lean_ctor_get(v_v_1244_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_v_1244_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1267_ = v_v_1244_;
v_isShared_1268_ = v_isSharedCheck_1275_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_node_1265_);
lean_dec(v_v_1244_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1275_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
size_t v___x_1269_; size_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1269_ = lean_usize_shift_right(v_x_1229_, v___x_1234_);
v___x_1270_ = lean_usize_add(v_x_1230_, v___x_1235_);
v___x_1271_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_node_1265_, v___x_1269_, v___x_1270_, v_x_1231_, v_x_1232_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1271_);
v___x_1273_ = v___x_1267_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
v___y_1248_ = v___x_1273_;
goto v___jp_1247_;
}
}
}
default: 
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_x_1231_);
lean_ctor_set(v___x_1276_, 1, v_x_1232_);
v___y_1248_ = v___x_1276_;
goto v___jp_1247_;
}
}
v___jp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = lean_array_fset(v_xs_x27_1246_, v_j_1238_, v___y_1248_);
lean_dec(v_j_1238_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1249_);
v___x_1251_ = v___x_1242_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
else
{
lean_object* v_ks_1279_; lean_object* v_vs_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1300_; 
v_ks_1279_ = lean_ctor_get(v_x_1228_, 0);
v_vs_1280_ = lean_ctor_get(v_x_1228_, 1);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_x_1228_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1282_ = v_x_1228_;
v_isShared_1283_ = v_isSharedCheck_1300_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_vs_1280_);
lean_inc(v_ks_1279_);
lean_dec(v_x_1228_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1300_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_ks_1279_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_vs_1280_);
v___x_1285_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v_newNode_1286_; uint8_t v___y_1288_; size_t v___x_1294_; uint8_t v___x_1295_; 
v_newNode_1286_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(v___x_1285_, v_x_1231_, v_x_1232_);
v___x_1294_ = ((size_t)7ULL);
v___x_1295_ = lean_usize_dec_le(v___x_1294_, v_x_1230_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1296_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1286_);
v___x_1297_ = lean_unsigned_to_nat(4u);
v___x_1298_ = lean_nat_dec_lt(v___x_1296_, v___x_1297_);
lean_dec(v___x_1296_);
v___y_1288_ = v___x_1298_;
goto v___jp_1287_;
}
else
{
v___y_1288_ = v___x_1295_;
goto v___jp_1287_;
}
v___jp_1287_:
{
if (v___y_1288_ == 0)
{
lean_object* v_ks_1289_; lean_object* v_vs_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v_ks_1289_ = lean_ctor_get(v_newNode_1286_, 0);
lean_inc_ref(v_ks_1289_);
v_vs_1290_ = lean_ctor_get(v_newNode_1286_, 1);
lean_inc_ref(v_vs_1290_);
lean_dec_ref(v_newNode_1286_);
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2);
v___x_1293_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_x_1230_, v_ks_1289_, v_vs_1290_, v___x_1291_, v___x_1292_);
lean_dec_ref(v_vs_1290_);
lean_dec_ref(v_ks_1289_);
return v___x_1293_;
}
else
{
return v_newNode_1286_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(size_t v_depth_1301_, lean_object* v_keys_1302_, lean_object* v_vals_1303_, lean_object* v_i_1304_, lean_object* v_entries_1305_){
_start:
{
lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1306_ = lean_array_get_size(v_keys_1302_);
v___x_1307_ = lean_nat_dec_lt(v_i_1304_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_dec(v_i_1304_);
return v_entries_1305_;
}
else
{
lean_object* v_k_1308_; lean_object* v_v_1309_; uint64_t v___x_1310_; size_t v_h_1311_; size_t v___x_1312_; lean_object* v___x_1313_; size_t v___x_1314_; size_t v___x_1315_; size_t v___x_1316_; size_t v_h_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v_k_1308_ = lean_array_fget_borrowed(v_keys_1302_, v_i_1304_);
v_v_1309_ = lean_array_fget_borrowed(v_vals_1303_, v_i_1304_);
v___x_1310_ = l_Lean_instHashableMVarId_hash(v_k_1308_);
v_h_1311_ = lean_uint64_to_usize(v___x_1310_);
v___x_1312_ = ((size_t)5ULL);
v___x_1313_ = lean_unsigned_to_nat(1u);
v___x_1314_ = ((size_t)1ULL);
v___x_1315_ = lean_usize_sub(v_depth_1301_, v___x_1314_);
v___x_1316_ = lean_usize_mul(v___x_1312_, v___x_1315_);
v_h_1317_ = lean_usize_shift_right(v_h_1311_, v___x_1316_);
v___x_1318_ = lean_nat_add(v_i_1304_, v___x_1313_);
lean_dec(v_i_1304_);
lean_inc(v_v_1309_);
lean_inc(v_k_1308_);
v___x_1319_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_entries_1305_, v_h_1317_, v_depth_1301_, v_k_1308_, v_v_1309_);
v_i_1304_ = v___x_1318_;
v_entries_1305_ = v___x_1319_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_depth_1321_, lean_object* v_keys_1322_, lean_object* v_vals_1323_, lean_object* v_i_1324_, lean_object* v_entries_1325_){
_start:
{
size_t v_depth_boxed_1326_; lean_object* v_res_1327_; 
v_depth_boxed_1326_ = lean_unbox_usize(v_depth_1321_);
lean_dec(v_depth_1321_);
v_res_1327_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_boxed_1326_, v_keys_1322_, v_vals_1323_, v_i_1324_, v_entries_1325_);
lean_dec_ref(v_vals_1323_);
lean_dec_ref(v_keys_1322_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_x_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_, lean_object* v_x_1332_){
_start:
{
size_t v_x_3902__boxed_1333_; size_t v_x_3903__boxed_1334_; lean_object* v_res_1335_; 
v_x_3902__boxed_1333_ = lean_unbox_usize(v_x_1329_);
lean_dec(v_x_1329_);
v_x_3903__boxed_1334_ = lean_unbox_usize(v_x_1330_);
lean_dec(v_x_1330_);
v_res_1335_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1328_, v_x_3902__boxed_1333_, v_x_3903__boxed_1334_, v_x_1331_, v_x_1332_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1336_, lean_object* v_x_1337_, lean_object* v_x_1338_){
_start:
{
uint64_t v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; lean_object* v___x_1342_; 
v___x_1339_ = l_Lean_instHashableMVarId_hash(v_x_1337_);
v___x_1340_ = lean_uint64_to_usize(v___x_1339_);
v___x_1341_ = ((size_t)1ULL);
v___x_1342_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1336_, v___x_1340_, v___x_1341_, v_x_1337_, v_x_1338_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(lean_object* v_mvarId_1343_, lean_object* v_val_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; lean_object* v_mctx_1348_; lean_object* v_cache_1349_; lean_object* v_zetaDeltaFVarIds_1350_; lean_object* v_postponed_1351_; lean_object* v_diag_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1379_; 
v___x_1347_ = lean_st_ref_take(v___y_1345_);
v_mctx_1348_ = lean_ctor_get(v___x_1347_, 0);
v_cache_1349_ = lean_ctor_get(v___x_1347_, 1);
v_zetaDeltaFVarIds_1350_ = lean_ctor_get(v___x_1347_, 2);
v_postponed_1351_ = lean_ctor_get(v___x_1347_, 3);
v_diag_1352_ = lean_ctor_get(v___x_1347_, 4);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1354_ = v___x_1347_;
v_isShared_1355_ = v_isSharedCheck_1379_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_diag_1352_);
lean_inc(v_postponed_1351_);
lean_inc(v_zetaDeltaFVarIds_1350_);
lean_inc(v_cache_1349_);
lean_inc(v_mctx_1348_);
lean_dec(v___x_1347_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1379_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v_depth_1356_; lean_object* v_levelAssignDepth_1357_; lean_object* v_mvarCounter_1358_; lean_object* v_lDepth_1359_; lean_object* v_decls_1360_; lean_object* v_userNames_1361_; lean_object* v_lAssignment_1362_; lean_object* v_eAssignment_1363_; lean_object* v_dAssignment_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1378_; 
v_depth_1356_ = lean_ctor_get(v_mctx_1348_, 0);
v_levelAssignDepth_1357_ = lean_ctor_get(v_mctx_1348_, 1);
v_mvarCounter_1358_ = lean_ctor_get(v_mctx_1348_, 2);
v_lDepth_1359_ = lean_ctor_get(v_mctx_1348_, 3);
v_decls_1360_ = lean_ctor_get(v_mctx_1348_, 4);
v_userNames_1361_ = lean_ctor_get(v_mctx_1348_, 5);
v_lAssignment_1362_ = lean_ctor_get(v_mctx_1348_, 6);
v_eAssignment_1363_ = lean_ctor_get(v_mctx_1348_, 7);
v_dAssignment_1364_ = lean_ctor_get(v_mctx_1348_, 8);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_mctx_1348_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1366_ = v_mctx_1348_;
v_isShared_1367_ = v_isSharedCheck_1378_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_dAssignment_1364_);
lean_inc(v_eAssignment_1363_);
lean_inc(v_lAssignment_1362_);
lean_inc(v_userNames_1361_);
lean_inc(v_decls_1360_);
lean_inc(v_lDepth_1359_);
lean_inc(v_mvarCounter_1358_);
lean_inc(v_levelAssignDepth_1357_);
lean_inc(v_depth_1356_);
lean_dec(v_mctx_1348_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1378_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1368_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(v_eAssignment_1363_, v_mvarId_1343_, v_val_1344_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 7, v___x_1368_);
v___x_1370_ = v___x_1366_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_depth_1356_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_levelAssignDepth_1357_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_mvarCounter_1358_);
lean_ctor_set(v_reuseFailAlloc_1377_, 3, v_lDepth_1359_);
lean_ctor_set(v_reuseFailAlloc_1377_, 4, v_decls_1360_);
lean_ctor_set(v_reuseFailAlloc_1377_, 5, v_userNames_1361_);
lean_ctor_set(v_reuseFailAlloc_1377_, 6, v_lAssignment_1362_);
lean_ctor_set(v_reuseFailAlloc_1377_, 7, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1377_, 8, v_dAssignment_1364_);
v___x_1370_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1372_; 
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1370_);
v___x_1372_ = v___x_1354_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_cache_1349_);
lean_ctor_set(v_reuseFailAlloc_1376_, 2, v_zetaDeltaFVarIds_1350_);
lean_ctor_set(v_reuseFailAlloc_1376_, 3, v_postponed_1351_);
lean_ctor_set(v_reuseFailAlloc_1376_, 4, v_diag_1352_);
v___x_1372_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1373_ = lean_st_ref_set(v___y_1345_, v___x_1372_);
v___x_1374_ = lean_box(0);
v___x_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
return v___x_1375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg___boxed(lean_object* v_mvarId_1380_, lean_object* v_val_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1380_, v_val_1381_, v___y_1382_);
lean_dec(v___y_1382_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(lean_object* v_mvarId_1385_, lean_object* v_type_1386_, lean_object* v_fvars_1387_, uint8_t v_isZero_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v___x_1394_; 
lean_inc(v_mvarId_1385_);
v___x_1394_ = l_Lean_MVarId_getTag(v_mvarId_1385_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref(v___x_1394_);
v___x_1396_ = l_Lean_Expr_headBeta(v_type_1386_);
v___x_1397_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1396_, v_a_1395_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; uint8_t v___x_1399_; uint8_t v___x_1400_; lean_object* v___x_1401_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc_n(v_a_1398_, 2);
lean_dec_ref(v___x_1397_);
v___x_1399_ = 0;
v___x_1400_ = 1;
v___x_1401_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1387_, v_a_1398_, v___x_1399_, v_isZero_1388_, v___x_1399_, v_isZero_1388_, v___x_1400_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1403_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref(v___x_1401_);
v___x_1403_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1385_, v_a_1402_, v___y_1390_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1412_; 
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v___x_1403_, 0);
lean_dec(v_unused_1413_);
v___x_1405_ = v___x_1403_;
v_isShared_1406_ = v_isSharedCheck_1412_;
goto v_resetjp_1404_;
}
else
{
lean_dec(v___x_1403_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1412_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1407_ = l_Lean_Expr_mvarId_x21(v_a_1398_);
lean_dec(v_a_1398_);
v___x_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1408_, 0, v_fvars_1387_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1408_);
v___x_1410_ = v___x_1405_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec(v_a_1398_);
lean_dec_ref(v_fvars_1387_);
v_a_1414_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1403_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1403_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec(v_a_1398_);
lean_dec_ref(v_fvars_1387_);
lean_dec(v_mvarId_1385_);
v_a_1422_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1401_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1401_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref(v_fvars_1387_);
lean_dec(v_mvarId_1385_);
v_a_1430_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1397_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1397_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v_fvars_1387_);
lean_dec_ref(v_type_1386_);
lean_dec(v_mvarId_1385_);
v_a_1438_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1394_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1394_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0___boxed(lean_object* v_mvarId_1446_, lean_object* v_type_1447_, lean_object* v_fvars_1448_, lean_object* v_isZero_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
uint8_t v_isZero_boxed_1455_; lean_object* v_res_1456_; 
v_isZero_boxed_1455_ = lean_unbox(v_isZero_1449_);
v_res_1456_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(v_mvarId_1446_, v_type_1447_, v_fvars_1448_, v_isZero_boxed_1455_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(lean_object* v_lctx_1457_, lean_object* v_x_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_keyedConfig_1464_; uint8_t v_trackZetaDelta_1465_; lean_object* v_zetaDeltaSet_1466_; lean_object* v_localInstances_1467_; lean_object* v_defEqCtx_x3f_1468_; lean_object* v_synthPendingDepth_1469_; lean_object* v_canUnfold_x3f_1470_; uint8_t v_univApprox_1471_; uint8_t v_inTypeClassResolution_1472_; uint8_t v_cacheInferType_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_keyedConfig_1464_ = lean_ctor_get(v___y_1459_, 0);
v_trackZetaDelta_1465_ = lean_ctor_get_uint8(v___y_1459_, sizeof(void*)*7);
v_zetaDeltaSet_1466_ = lean_ctor_get(v___y_1459_, 1);
v_localInstances_1467_ = lean_ctor_get(v___y_1459_, 3);
v_defEqCtx_x3f_1468_ = lean_ctor_get(v___y_1459_, 4);
v_synthPendingDepth_1469_ = lean_ctor_get(v___y_1459_, 5);
v_canUnfold_x3f_1470_ = lean_ctor_get(v___y_1459_, 6);
v_univApprox_1471_ = lean_ctor_get_uint8(v___y_1459_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1472_ = lean_ctor_get_uint8(v___y_1459_, sizeof(void*)*7 + 2);
v_cacheInferType_1473_ = lean_ctor_get_uint8(v___y_1459_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_1470_);
lean_inc(v_synthPendingDepth_1469_);
lean_inc(v_defEqCtx_x3f_1468_);
lean_inc_ref(v_localInstances_1467_);
lean_inc(v_zetaDeltaSet_1466_);
lean_inc_ref(v_keyedConfig_1464_);
v___x_1474_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1474_, 0, v_keyedConfig_1464_);
lean_ctor_set(v___x_1474_, 1, v_zetaDeltaSet_1466_);
lean_ctor_set(v___x_1474_, 2, v_lctx_1457_);
lean_ctor_set(v___x_1474_, 3, v_localInstances_1467_);
lean_ctor_set(v___x_1474_, 4, v_defEqCtx_x3f_1468_);
lean_ctor_set(v___x_1474_, 5, v_synthPendingDepth_1469_);
lean_ctor_set(v___x_1474_, 6, v_canUnfold_x3f_1470_);
lean_ctor_set_uint8(v___x_1474_, sizeof(void*)*7, v_trackZetaDelta_1465_);
lean_ctor_set_uint8(v___x_1474_, sizeof(void*)*7 + 1, v_univApprox_1471_);
lean_ctor_set_uint8(v___x_1474_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1472_);
lean_ctor_set_uint8(v___x_1474_, sizeof(void*)*7 + 3, v_cacheInferType_1473_);
lean_inc(v___y_1462_);
lean_inc_ref(v___y_1461_);
lean_inc(v___y_1460_);
v___x_1475_ = lean_apply_5(v_x_1458_, v___x_1474_, v___y_1460_, v___y_1461_, v___y_1462_, lean_box(0));
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg___boxed(lean_object* v_lctx_1476_, lean_object* v_x_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1476_, v_x_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed(lean_object* v_type_1484_, lean_object* v_mvarId_1485_, lean_object* v_n_1486_, lean_object* v_preserveBinderNames_1487_, lean_object* v___x_1488_, lean_object* v_useNamesForExplicitOnly_1489_, lean_object* v_lctx_1490_, lean_object* v_fvars_1491_, lean_object* v___x_1492_, lean_object* v_s_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1499_; uint8_t v___x_4269__boxed_1500_; uint8_t v_useNamesForExplicitOnly_boxed_1501_; lean_object* v_res_1502_; 
v_preserveBinderNames_boxed_1499_ = lean_unbox(v_preserveBinderNames_1487_);
v___x_4269__boxed_1500_ = lean_unbox(v___x_1488_);
v_useNamesForExplicitOnly_boxed_1501_ = lean_unbox(v_useNamesForExplicitOnly_1489_);
v_res_1502_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(v_type_1484_, v_mvarId_1485_, v_n_1486_, v_preserveBinderNames_boxed_1499_, v___x_4269__boxed_1500_, v_useNamesForExplicitOnly_boxed_1501_, v_lctx_1490_, v_fvars_1491_, v___x_1492_, v_s_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v_n_1486_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(uint8_t v_preserveBinderNames_1503_, uint8_t v___x_1504_, uint8_t v_useNamesForExplicitOnly_1505_, lean_object* v_mvarId_1506_, lean_object* v_i_1507_, lean_object* v_lctx_1508_, lean_object* v_fvars_1509_, lean_object* v_j_1510_, lean_object* v_s_1511_, lean_object* v_type_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_zero_1518_; uint8_t v_isZero_1519_; 
v_zero_1518_ = lean_unsigned_to_nat(0u);
v_isZero_1519_ = lean_nat_dec_eq(v_i_1507_, v_zero_1518_);
if (v_isZero_1519_ == 1)
{
lean_object* v___x_1520_; lean_object* v_type_1521_; lean_object* v___x_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec(v_s_1511_);
lean_dec(v_i_1507_);
v___x_1520_ = lean_array_get_size(v_fvars_1509_);
v_type_1521_ = lean_expr_instantiate_rev_range(v_type_1512_, v_j_1510_, v___x_1520_, v_fvars_1509_);
lean_dec_ref(v_type_1512_);
v___x_1522_ = lean_box(v_isZero_1519_);
lean_inc_ref(v_fvars_1509_);
v___f_1523_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1523_, 0, v_mvarId_1506_);
lean_closure_set(v___f_1523_, 1, v_type_1521_);
lean_closure_set(v___f_1523_, 2, v_fvars_1509_);
lean_closure_set(v___f_1523_, 3, v___x_1522_);
v___x_1524_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed), 9, 4);
lean_closure_set(v___x_1524_, 0, lean_box(0));
lean_closure_set(v___x_1524_, 1, v_fvars_1509_);
lean_closure_set(v___x_1524_, 2, v_j_1510_);
lean_closure_set(v___x_1524_, 3, v___f_1523_);
v___x_1525_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1508_, v___x_1524_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
return v___x_1525_;
}
else
{
lean_object* v_one_1526_; lean_object* v_n_1527_; 
v_one_1526_ = lean_unsigned_to_nat(1u);
v_n_1527_ = lean_nat_sub(v_i_1507_, v_one_1526_);
lean_dec(v_i_1507_);
switch(lean_obj_tag(v_type_1512_))
{
case 8:
{
lean_object* v_declName_1528_; lean_object* v_type_1529_; lean_object* v_value_1530_; lean_object* v_body_1531_; lean_object* v___x_1532_; 
v_declName_1528_ = lean_ctor_get(v_type_1512_, 0);
lean_inc(v_declName_1528_);
v_type_1529_ = lean_ctor_get(v_type_1512_, 1);
lean_inc_ref(v_type_1529_);
v_value_1530_ = lean_ctor_get(v_type_1512_, 2);
lean_inc_ref(v_value_1530_);
v_body_1531_ = lean_ctor_get(v_type_1512_, 3);
lean_inc_ref(v_body_1531_);
lean_dec_ref(v_type_1512_);
v___x_1532_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref(v___x_1532_);
v___x_1534_ = 1;
v___x_1535_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_1503_, v___x_1504_, v_useNamesForExplicitOnly_1505_, v_lctx_1508_, v_declName_1528_, v___x_1534_, v_s_1511_, v_a_1515_, v_a_1516_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v_fst_1537_; lean_object* v_snd_1538_; lean_object* v___x_1539_; lean_object* v_type_1540_; lean_object* v_type_1541_; lean_object* v_val_1542_; uint8_t v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref(v___x_1535_);
v_fst_1537_ = lean_ctor_get(v_a_1536_, 0);
lean_inc(v_fst_1537_);
v_snd_1538_ = lean_ctor_get(v_a_1536_, 1);
lean_inc(v_snd_1538_);
lean_dec(v_a_1536_);
v___x_1539_ = lean_array_get_size(v_fvars_1509_);
v_type_1540_ = lean_expr_instantiate_rev_range(v_type_1529_, v_j_1510_, v___x_1539_, v_fvars_1509_);
lean_dec_ref(v_type_1529_);
v_type_1541_ = l_Lean_Expr_headBeta(v_type_1540_);
v_val_1542_ = lean_expr_instantiate_rev_range(v_value_1530_, v_j_1510_, v___x_1539_, v_fvars_1509_);
lean_dec_ref(v_value_1530_);
v___x_1543_ = 0;
lean_inc(v_a_1533_);
v___x_1544_ = l_Lean_LocalContext_mkLetDecl(v_lctx_1508_, v_a_1533_, v_fst_1537_, v_type_1541_, v_val_1542_, v_isZero_1519_, v___x_1543_);
v___x_1545_ = l_Lean_mkFVar(v_a_1533_);
v___x_1546_ = lean_array_push(v_fvars_1509_, v___x_1545_);
v_i_1507_ = v_n_1527_;
v_lctx_1508_ = v___x_1544_;
v_fvars_1509_ = v___x_1546_;
v_s_1511_ = v_snd_1538_;
v_type_1512_ = v_body_1531_;
goto _start;
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec(v_a_1533_);
lean_dec_ref(v_body_1531_);
lean_dec_ref(v_value_1530_);
lean_dec_ref(v_type_1529_);
lean_dec(v_n_1527_);
lean_dec(v_j_1510_);
lean_dec_ref(v_fvars_1509_);
lean_dec_ref(v_lctx_1508_);
lean_dec(v_mvarId_1506_);
v_a_1548_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1535_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1535_);
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
lean_dec_ref(v_body_1531_);
lean_dec_ref(v_value_1530_);
lean_dec_ref(v_type_1529_);
lean_dec(v_declName_1528_);
lean_dec(v_n_1527_);
lean_dec(v_s_1511_);
lean_dec(v_j_1510_);
lean_dec_ref(v_fvars_1509_);
lean_dec_ref(v_lctx_1508_);
lean_dec(v_mvarId_1506_);
v_a_1556_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1532_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1532_);
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
case 7:
{
lean_object* v_binderName_1564_; lean_object* v_binderType_1565_; lean_object* v_body_1566_; uint8_t v_binderInfo_1567_; lean_object* v___x_1568_; 
v_binderName_1564_ = lean_ctor_get(v_type_1512_, 0);
lean_inc(v_binderName_1564_);
v_binderType_1565_ = lean_ctor_get(v_type_1512_, 1);
lean_inc_ref(v_binderType_1565_);
v_body_1566_ = lean_ctor_get(v_type_1512_, 2);
lean_inc_ref(v_body_1566_);
v_binderInfo_1567_ = lean_ctor_get_uint8(v_type_1512_, sizeof(void*)*3 + 8);
lean_dec_ref(v_type_1512_);
v___x_1568_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref(v___x_1568_);
v___x_1570_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_1567_);
v___x_1571_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_1503_, v___x_1504_, v_useNamesForExplicitOnly_1505_, v_lctx_1508_, v_binderName_1564_, v___x_1570_, v_s_1511_, v_a_1515_, v_a_1516_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v_fst_1573_; lean_object* v_snd_1574_; lean_object* v___x_1575_; lean_object* v_type_1576_; lean_object* v_type_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref(v___x_1571_);
v_fst_1573_ = lean_ctor_get(v_a_1572_, 0);
lean_inc(v_fst_1573_);
v_snd_1574_ = lean_ctor_get(v_a_1572_, 1);
lean_inc(v_snd_1574_);
lean_dec(v_a_1572_);
v___x_1575_ = lean_array_get_size(v_fvars_1509_);
v_type_1576_ = lean_expr_instantiate_rev_range(v_binderType_1565_, v_j_1510_, v___x_1575_, v_fvars_1509_);
lean_dec_ref(v_binderType_1565_);
v_type_1577_ = l_Lean_Expr_headBeta(v_type_1576_);
v___x_1578_ = 0;
lean_inc(v_a_1569_);
v___x_1579_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_1508_, v_a_1569_, v_fst_1573_, v_type_1577_, v_binderInfo_1567_, v___x_1578_);
v___x_1580_ = l_Lean_mkFVar(v_a_1569_);
v___x_1581_ = lean_array_push(v_fvars_1509_, v___x_1580_);
v_i_1507_ = v_n_1527_;
v_lctx_1508_ = v___x_1579_;
v_fvars_1509_ = v___x_1581_;
v_s_1511_ = v_snd_1574_;
v_type_1512_ = v_body_1566_;
goto _start;
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v_a_1569_);
lean_dec_ref(v_body_1566_);
lean_dec_ref(v_binderType_1565_);
lean_dec(v_n_1527_);
lean_dec(v_j_1510_);
lean_dec_ref(v_fvars_1509_);
lean_dec_ref(v_lctx_1508_);
lean_dec(v_mvarId_1506_);
v_a_1583_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1571_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1571_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec_ref(v_body_1566_);
lean_dec_ref(v_binderType_1565_);
lean_dec(v_binderName_1564_);
lean_dec(v_n_1527_);
lean_dec(v_s_1511_);
lean_dec(v_j_1510_);
lean_dec_ref(v_fvars_1509_);
lean_dec_ref(v_lctx_1508_);
lean_dec(v_mvarId_1506_);
v_a_1591_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1568_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1568_);
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
}
default: 
{
lean_object* v___x_1599_; lean_object* v_type_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___f_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1599_ = lean_array_get_size(v_fvars_1509_);
v_type_1600_ = lean_expr_instantiate_rev_range(v_type_1512_, v_j_1510_, v___x_1599_, v_fvars_1509_);
lean_dec_ref(v_type_1512_);
v___x_1601_ = lean_box(v_preserveBinderNames_1503_);
v___x_1602_ = lean_box(v___x_1504_);
v___x_1603_ = lean_box(v_useNamesForExplicitOnly_1505_);
lean_inc_ref(v_fvars_1509_);
lean_inc_ref(v_lctx_1508_);
v___f_1604_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed), 15, 10);
lean_closure_set(v___f_1604_, 0, v_type_1600_);
lean_closure_set(v___f_1604_, 1, v_mvarId_1506_);
lean_closure_set(v___f_1604_, 2, v_n_1527_);
lean_closure_set(v___f_1604_, 3, v___x_1601_);
lean_closure_set(v___f_1604_, 4, v___x_1602_);
lean_closure_set(v___f_1604_, 5, v___x_1603_);
lean_closure_set(v___f_1604_, 6, v_lctx_1508_);
lean_closure_set(v___f_1604_, 7, v_fvars_1509_);
lean_closure_set(v___f_1604_, 8, v___x_1599_);
lean_closure_set(v___f_1604_, 9, v_s_1511_);
v___x_1605_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed), 9, 4);
lean_closure_set(v___x_1605_, 0, lean_box(0));
lean_closure_set(v___x_1605_, 1, v_fvars_1509_);
lean_closure_set(v___x_1605_, 2, v_j_1510_);
lean_closure_set(v___x_1605_, 3, v___f_1604_);
v___x_1606_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1508_, v___x_1605_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
return v___x_1606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(lean_object* v_type_1607_, lean_object* v_mvarId_1608_, lean_object* v_n_1609_, uint8_t v_preserveBinderNames_1610_, uint8_t v___x_1611_, uint8_t v_useNamesForExplicitOnly_1612_, lean_object* v_lctx_1613_, lean_object* v_fvars_1614_, lean_object* v___x_1615_, lean_object* v_s_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_type_1607_, v___y_1618_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1624_; uint8_t v___y_1626_; uint8_t v___x_1647_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref(v___x_1622_);
v___x_1624_ = l_Lean_Expr_cleanupAnnotations(v_a_1623_);
v___x_1647_ = l_Lean_Expr_isForall(v___x_1624_);
if (v___x_1647_ == 0)
{
uint8_t v___x_1648_; 
v___x_1648_ = l_Lean_Expr_isLet(v___x_1624_);
v___y_1626_ = v___x_1648_;
goto v___jp_1625_;
}
else
{
v___y_1626_ = v___x_1647_;
goto v___jp_1625_;
}
v___jp_1625_:
{
if (v___y_1626_ == 0)
{
lean_object* v___x_1627_; 
lean_inc(v___y_1620_);
lean_inc_ref(v___y_1619_);
lean_inc(v___y_1618_);
lean_inc_ref(v___y_1617_);
v___x_1627_ = lean_whnf(v___x_1624_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; uint8_t v___x_1629_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref(v___x_1627_);
v___x_1629_ = l_Lean_Expr_isForall(v_a_1628_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
lean_dec(v_a_1628_);
lean_dec(v_s_1616_);
lean_dec(v___x_1615_);
lean_dec_ref(v_fvars_1614_);
lean_dec_ref(v_lctx_1613_);
v___x_1630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
v___x_1631_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4);
v___x_1632_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1630_, v_mvarId_1608_, v___x_1631_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
return v___x_1632_;
}
else
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1633_ = lean_unsigned_to_nat(1u);
v___x_1634_ = lean_nat_add(v_n_1609_, v___x_1633_);
v___x_1635_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1610_, v___x_1611_, v_useNamesForExplicitOnly_1612_, v_mvarId_1608_, v___x_1634_, v_lctx_1613_, v_fvars_1614_, v___x_1615_, v_s_1616_, v_a_1628_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
return v___x_1635_;
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v_s_1616_);
lean_dec(v___x_1615_);
lean_dec_ref(v_fvars_1614_);
lean_dec_ref(v_lctx_1613_);
lean_dec(v_mvarId_1608_);
v_a_1636_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1627_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1627_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1644_ = lean_unsigned_to_nat(1u);
v___x_1645_ = lean_nat_add(v_n_1609_, v___x_1644_);
v___x_1646_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1610_, v___x_1611_, v_useNamesForExplicitOnly_1612_, v_mvarId_1608_, v___x_1645_, v_lctx_1613_, v_fvars_1614_, v___x_1615_, v_s_1616_, v___x_1624_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
return v___x_1646_;
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v_s_1616_);
lean_dec(v___x_1615_);
lean_dec_ref(v_fvars_1614_);
lean_dec_ref(v_lctx_1613_);
lean_dec(v_mvarId_1608_);
v_a_1649_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1622_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1622_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___boxed(lean_object* v_preserveBinderNames_1657_, lean_object* v___x_1658_, lean_object* v_useNamesForExplicitOnly_1659_, lean_object* v_mvarId_1660_, lean_object* v_i_1661_, lean_object* v_lctx_1662_, lean_object* v_fvars_1663_, lean_object* v_j_1664_, lean_object* v_s_1665_, lean_object* v_type_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1672_; uint8_t v___x_4302__boxed_1673_; uint8_t v_useNamesForExplicitOnly_boxed_1674_; lean_object* v_res_1675_; 
v_preserveBinderNames_boxed_1672_ = lean_unbox(v_preserveBinderNames_1657_);
v___x_4302__boxed_1673_ = lean_unbox(v___x_1658_);
v_useNamesForExplicitOnly_boxed_1674_ = lean_unbox(v_useNamesForExplicitOnly_1659_);
v_res_1675_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_boxed_1672_, v___x_4302__boxed_1673_, v_useNamesForExplicitOnly_boxed_1674_, v_mvarId_1660_, v_i_1661_, v_lctx_1662_, v_fvars_1663_, v_j_1664_, v_s_1665_, v_type_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___lam__0(lean_object* v_mvarId_1676_, lean_object* v___x_1677_, lean_object* v___x_1678_, uint8_t v_preserveBinderNames_1679_, uint8_t v___x_1680_, uint8_t v_useNamesForExplicitOnly_1681_, lean_object* v_n_1682_, lean_object* v_givenNames_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; 
lean_inc(v_mvarId_1676_);
v___x_1689_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1676_, v___x_1677_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v___x_1690_; 
lean_dec_ref(v___x_1689_);
lean_inc(v_mvarId_1676_);
v___x_1690_ = l_Lean_MVarId_getType(v_mvarId_1676_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v_lctx_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref(v___x_1690_);
v_lctx_1692_ = lean_ctor_get(v___y_1684_, 2);
lean_inc_ref(v_lctx_1692_);
v___x_1693_ = lean_mk_empty_array_with_capacity(v___x_1678_);
v___x_1694_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1679_, v___x_1680_, v_useNamesForExplicitOnly_1681_, v_mvarId_1676_, v_n_1682_, v_lctx_1692_, v___x_1693_, v___x_1678_, v_givenNames_1683_, v_a_1691_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec_ref(v___y_1684_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1714_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1697_ = v___x_1694_;
v_isShared_1698_ = v_isSharedCheck_1714_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1694_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1714_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v_fst_1699_; lean_object* v_snd_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1713_; 
v_fst_1699_ = lean_ctor_get(v_a_1695_, 0);
v_snd_1700_ = lean_ctor_get(v_a_1695_, 1);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_a_1695_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1702_ = v_a_1695_;
v_isShared_1703_ = v_isSharedCheck_1713_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_snd_1700_);
lean_inc(v_fst_1699_);
lean_dec(v_a_1695_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1713_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
size_t v_sz_1704_; size_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v_sz_1704_ = lean_array_size(v_fst_1699_);
v___x_1705_ = ((size_t)0ULL);
v___x_1706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(v_sz_1704_, v___x_1705_, v_fst_1699_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1706_);
v___x_1708_ = v___x_1702_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1706_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_snd_1700_);
v___x_1708_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1710_; 
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v___x_1708_);
v___x_1710_ = v___x_1697_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
v_a_1715_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1694_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1694_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec_ref(v___y_1684_);
lean_dec(v_givenNames_1683_);
lean_dec(v_n_1682_);
lean_dec(v___x_1678_);
lean_dec(v_mvarId_1676_);
v_a_1723_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1690_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1690_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec_ref(v___y_1684_);
lean_dec(v_givenNames_1683_);
lean_dec(v_n_1682_);
lean_dec(v___x_1678_);
lean_dec(v_mvarId_1676_);
v_a_1731_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1689_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1689_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___lam__0___boxed(lean_object* v_mvarId_1739_, lean_object* v___x_1740_, lean_object* v___x_1741_, lean_object* v_preserveBinderNames_1742_, lean_object* v___x_1743_, lean_object* v_useNamesForExplicitOnly_1744_, lean_object* v_n_1745_, lean_object* v_givenNames_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1752_; uint8_t v___x_4532__boxed_1753_; uint8_t v_useNamesForExplicitOnly_boxed_1754_; lean_object* v_res_1755_; 
v_preserveBinderNames_boxed_1752_ = lean_unbox(v_preserveBinderNames_1742_);
v___x_4532__boxed_1753_ = lean_unbox(v___x_1743_);
v_useNamesForExplicitOnly_boxed_1754_ = lean_unbox(v_useNamesForExplicitOnly_1744_);
v_res_1755_ = l_Lean_Meta_introNCore___lam__0(v_mvarId_1739_, v___x_1740_, v___x_1741_, v_preserveBinderNames_boxed_1752_, v___x_4532__boxed_1753_, v_useNamesForExplicitOnly_boxed_1754_, v_n_1745_, v_givenNames_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore(lean_object* v_mvarId_1758_, lean_object* v_n_1759_, lean_object* v_givenNames_1760_, uint8_t v_useNamesForExplicitOnly_1761_, uint8_t v_preserveBinderNames_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = lean_unsigned_to_nat(0u);
v___x_1769_ = lean_nat_dec_eq(v_n_1759_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v_options_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___f_1777_; lean_object* v___x_1778_; 
v_options_1770_ = lean_ctor_get(v_a_1765_, 2);
v___x_1771_ = l_Lean_Meta_tactic_hygienic;
v___x_1772_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v_options_1770_, v___x_1771_);
v___x_1773_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
v___x_1774_ = lean_box(v_preserveBinderNames_1762_);
v___x_1775_ = lean_box(v___x_1772_);
v___x_1776_ = lean_box(v_useNamesForExplicitOnly_1761_);
lean_inc(v_mvarId_1758_);
v___f_1777_ = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1777_, 0, v_mvarId_1758_);
lean_closure_set(v___f_1777_, 1, v___x_1773_);
lean_closure_set(v___f_1777_, 2, v___x_1768_);
lean_closure_set(v___f_1777_, 3, v___x_1774_);
lean_closure_set(v___f_1777_, 4, v___x_1775_);
lean_closure_set(v___f_1777_, 5, v___x_1776_);
lean_closure_set(v___f_1777_, 6, v_n_1759_);
lean_closure_set(v___f_1777_, 7, v_givenNames_1760_);
v___x_1778_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_1758_, v___f_1777_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
return v___x_1778_;
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_dec(v_givenNames_1760_);
lean_dec(v_n_1759_);
v___x_1779_ = ((lean_object*)(l_Lean_Meta_introNCore___closed__0));
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
lean_ctor_set(v___x_1780_, 1, v_mvarId_1758_);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
return v___x_1781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___boxed(lean_object* v_mvarId_1782_, lean_object* v_n_1783_, lean_object* v_givenNames_1784_, lean_object* v_useNamesForExplicitOnly_1785_, lean_object* v_preserveBinderNames_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
uint8_t v_useNamesForExplicitOnly_boxed_1792_; uint8_t v_preserveBinderNames_boxed_1793_; lean_object* v_res_1794_; 
v_useNamesForExplicitOnly_boxed_1792_ = lean_unbox(v_useNamesForExplicitOnly_1785_);
v_preserveBinderNames_boxed_1793_ = lean_unbox(v_preserveBinderNames_1786_);
v_res_1794_ = l_Lean_Meta_introNCore(v_mvarId_1782_, v_n_1783_, v_givenNames_1784_, v_useNamesForExplicitOnly_boxed_1792_, v_preserveBinderNames_boxed_1793_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_);
lean_dec(v_a_1790_);
lean_dec_ref(v_a_1789_);
lean_dec(v_a_1788_);
lean_dec_ref(v_a_1787_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(lean_object* v_00_u03b1_1795_, lean_object* v_lctx_1796_, lean_object* v_x_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1796_, v_x_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1804_, lean_object* v_lctx_1805_, lean_object* v_x_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(v_00_u03b1_1804_, v_lctx_1805_, v_x_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(lean_object* v_e_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_1813_, v___y_1815_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___boxed(lean_object* v_e_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(v_e_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(lean_object* v_mvarId_1827_, lean_object* v_val_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1827_, v_val_1828_, v___y_1830_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___boxed(lean_object* v_mvarId_1835_, lean_object* v_val_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(v_mvarId_1835_, v_val_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1843_, lean_object* v_fvars_1844_, lean_object* v_j_1845_, lean_object* v_x_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1844_, v_j_1845_, v_x_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1853_, lean_object* v_fvars_1854_, lean_object* v_j_1855_, lean_object* v_x_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(v_00_u03b1_1853_, v_fvars_1854_, v_j_1855_, v_x_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1866_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___boxed(lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1875_, lean_object* v_x_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(v_x_1876_, v_x_1877_, v_x_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1880_, lean_object* v_x_1881_, size_t v_x_1882_, size_t v_x_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1881_, v_x_1882_, v_x_1883_, v_x_1884_, v_x_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
size_t v_x_4783__boxed_1893_; size_t v_x_4784__boxed_1894_; lean_object* v_res_1895_; 
v_x_4783__boxed_1893_ = lean_unbox_usize(v_x_1889_);
lean_dec(v_x_1889_);
v_x_4784__boxed_1894_ = lean_unbox_usize(v_x_1890_);
lean_dec(v_x_1890_);
v_res_1895_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1887_, v_x_1888_, v_x_4783__boxed_1893_, v_x_4784__boxed_1894_, v_x_1891_, v_x_1892_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11(lean_object* v_00_u03b2_1896_, lean_object* v_n_1897_, lean_object* v_k_1898_, lean_object* v_v_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(v_n_1897_, v_k_1898_, v_v_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(lean_object* v_00_u03b2_1901_, size_t v_depth_1902_, lean_object* v_keys_1903_, lean_object* v_vals_1904_, lean_object* v_heq_1905_, lean_object* v_i_1906_, lean_object* v_entries_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_1902_, v_keys_1903_, v_vals_1904_, v_i_1906_, v_entries_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_1909_, lean_object* v_depth_1910_, lean_object* v_keys_1911_, lean_object* v_vals_1912_, lean_object* v_heq_1913_, lean_object* v_i_1914_, lean_object* v_entries_1915_){
_start:
{
size_t v_depth_boxed_1916_; lean_object* v_res_1917_; 
v_depth_boxed_1916_ = lean_unbox_usize(v_depth_1910_);
lean_dec(v_depth_1910_);
v_res_1917_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(v_00_u03b2_1909_, v_depth_boxed_1916_, v_keys_1911_, v_vals_1912_, v_heq_1913_, v_i_1914_, v_entries_1915_);
lean_dec_ref(v_vals_1912_);
lean_dec_ref(v_keys_1911_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1918_, lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_, lean_object* v_x_1922_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(v_x_1919_, v_x_1920_, v_x_1921_, v_x_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introN(lean_object* v_mvarId_1924_, lean_object* v_n_1925_, lean_object* v_givenNames_1926_, uint8_t v_useNamesForExplicitOnly_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_){
_start:
{
uint8_t v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = 0;
v___x_1934_ = l_Lean_Meta_introNCore(v_mvarId_1924_, v_n_1925_, v_givenNames_1926_, v_useNamesForExplicitOnly_1927_, v___x_1933_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introN___boxed(lean_object* v_mvarId_1935_, lean_object* v_n_1936_, lean_object* v_givenNames_1937_, lean_object* v_useNamesForExplicitOnly_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
uint8_t v_useNamesForExplicitOnly_boxed_1944_; lean_object* v_res_1945_; 
v_useNamesForExplicitOnly_boxed_1944_ = lean_unbox(v_useNamesForExplicitOnly_1938_);
v_res_1945_ = l_Lean_MVarId_introN(v_mvarId_1935_, v_n_1936_, v_givenNames_1937_, v_useNamesForExplicitOnly_boxed_1944_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introNP(lean_object* v_mvarId_1946_, lean_object* v_n_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v___x_1953_; uint8_t v___x_1954_; uint8_t v___x_1955_; lean_object* v___x_1956_; 
v___x_1953_ = lean_box(0);
v___x_1954_ = 0;
v___x_1955_ = 1;
v___x_1956_ = l_Lean_Meta_introNCore(v_mvarId_1946_, v_n_1947_, v___x_1953_, v___x_1954_, v___x_1955_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introNP___boxed(lean_object* v_mvarId_1957_, lean_object* v_n_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_MVarId_introNP(v_mvarId_1957_, v_n_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro(lean_object* v_mvarId_1965_, lean_object* v_name_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; lean_object* v___x_1976_; 
v___x_1972_ = lean_unsigned_to_nat(1u);
v___x_1973_ = lean_box(0);
v___x_1974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1974_, 0, v_name_1966_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = 0;
v___x_1976_ = l_Lean_Meta_introNCore(v_mvarId_1965_, v___x_1972_, v___x_1974_, v___x_1975_, v___x_1975_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1996_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1979_ = v___x_1976_;
v_isShared_1980_ = v_isSharedCheck_1996_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1976_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1996_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v_fst_1981_; lean_object* v_snd_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1995_; 
v_fst_1981_ = lean_ctor_get(v_a_1977_, 0);
v_snd_1982_ = lean_ctor_get(v_a_1977_, 1);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_a_1977_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1984_ = v_a_1977_;
v_isShared_1985_ = v_isSharedCheck_1995_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_snd_1982_);
lean_inc(v_fst_1981_);
lean_dec(v_a_1977_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1995_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1986_ = lean_box(0);
v___x_1987_ = lean_unsigned_to_nat(0u);
v___x_1988_ = lean_array_get(v___x_1986_, v_fst_1981_, v___x_1987_);
lean_dec(v_fst_1981_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1988_);
v___x_1990_ = v___x_1984_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_snd_1982_);
v___x_1990_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1992_; 
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_1990_);
v___x_1992_ = v___x_1979_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
v_a_1997_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1976_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1976_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro___boxed(lean_object* v_mvarId_2005_, lean_object* v_name_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Lean_MVarId_intro(v_mvarId_2005_, v_name_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core(lean_object* v_mvarId_2013_, uint8_t v_preserveBinderNames_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; lean_object* v___x_2023_; 
v___x_2020_ = lean_unsigned_to_nat(1u);
v___x_2021_ = lean_box(0);
v___x_2022_ = 0;
v___x_2023_ = l_Lean_Meta_introNCore(v_mvarId_2013_, v___x_2020_, v___x_2021_, v___x_2022_, v_preserveBinderNames_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2043_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2043_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2043_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v_fst_2028_; lean_object* v_snd_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2042_; 
v_fst_2028_ = lean_ctor_get(v_a_2024_, 0);
v_snd_2029_ = lean_ctor_get(v_a_2024_, 1);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_a_2024_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2031_ = v_a_2024_;
v_isShared_2032_ = v_isSharedCheck_2042_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_snd_2029_);
lean_inc(v_fst_2028_);
lean_dec(v_a_2024_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2042_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2033_ = lean_box(0);
v___x_2034_ = lean_unsigned_to_nat(0u);
v___x_2035_ = lean_array_get(v___x_2033_, v_fst_2028_, v___x_2034_);
lean_dec(v_fst_2028_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2035_);
v___x_2037_ = v___x_2031_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_snd_2029_);
v___x_2037_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2039_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2037_);
v___x_2039_ = v___x_2026_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
v_a_2044_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2023_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2023_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core___boxed(lean_object* v_mvarId_2052_, lean_object* v_preserveBinderNames_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
uint8_t v_preserveBinderNames_boxed_2059_; lean_object* v_res_2060_; 
v_preserveBinderNames_boxed_2059_ = lean_unbox(v_preserveBinderNames_2053_);
v_res_2060_ = l_Lean_Meta_intro1Core(v_mvarId_2052_, v_preserveBinderNames_boxed_2059_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
lean_dec(v_a_2057_);
lean_dec_ref(v_a_2056_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1(lean_object* v_mvarId_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
uint8_t v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = 0;
v___x_2068_ = l_Lean_Meta_intro1Core(v_mvarId_2061_, v___x_2067_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___boxed(lean_object* v_mvarId_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_MVarId_intro1(v_mvarId_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1P(lean_object* v_mvarId_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
uint8_t v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = 1;
v___x_2083_ = l_Lean_Meta_intro1Core(v_mvarId_2076_, v___x_2082_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1P___boxed(lean_object* v_mvarId_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_MVarId_intro1P(v_mvarId_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
lean_dec(v_a_2088_);
lean_dec_ref(v_a_2087_);
lean_dec(v_a_2086_);
lean_dec_ref(v_a_2085_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(lean_object* v_msgData_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v___x_2097_; lean_object* v_env_2098_; lean_object* v___x_2099_; lean_object* v_mctx_2100_; lean_object* v_lctx_2101_; lean_object* v_options_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2097_ = lean_st_ref_get(v___y_2095_);
v_env_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc_ref(v_env_2098_);
lean_dec(v___x_2097_);
v___x_2099_ = lean_st_ref_get(v___y_2093_);
v_mctx_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc_ref(v_mctx_2100_);
lean_dec(v___x_2099_);
v_lctx_2101_ = lean_ctor_get(v___y_2092_, 2);
v_options_2102_ = lean_ctor_get(v___y_2094_, 2);
lean_inc_ref(v_options_2102_);
lean_inc_ref(v_lctx_2101_);
v___x_2103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2103_, 0, v_env_2098_);
lean_ctor_set(v___x_2103_, 1, v_mctx_2100_);
lean_ctor_set(v___x_2103_, 2, v_lctx_2101_);
lean_ctor_set(v___x_2103_, 3, v_options_2102_);
v___x_2104_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
lean_ctor_set(v___x_2104_, 1, v_msgData_2091_);
v___x_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0___boxed(lean_object* v_msgData_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msgData_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(lean_object* v_msg_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_ref_2119_; lean_object* v___x_2120_; lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2129_; 
v_ref_2119_ = lean_ctor_get(v___y_2116_, 5);
v___x_2120_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msg_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2129_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2129_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
lean_inc(v_ref_2119_);
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v_ref_2119_);
lean_ctor_set(v___x_2125_, 1, v_a_2121_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set_tag(v___x_2123_, 1);
lean_ctor_set(v___x_2123_, 0, v___x_2125_);
v___x_2127_ = v___x_2123_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg___boxed(lean_object* v_msg_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v_msg_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
return v_res_2136_;
}
}
static lean_object* _init_l_Lean_MVarId_intro1___00__lam__0___closed__1(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l_Lean_MVarId_intro1___00__lam__0___closed__0));
v___x_2139_ = l_Lean_stringToMessageData(v___x_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__lam__0(lean_object* v_mvarId_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v___x_2146_; 
lean_inc(v_mvarId_2140_);
v___x_2146_ = l_Lean_MVarId_getType_x27(v_mvarId_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref(v___x_2146_);
if (lean_obj_tag(v_a_2147_) == 7)
{
lean_object* v_binderName_2148_; lean_object* v_binderType_2149_; lean_object* v_body_2150_; uint8_t v_binderInfo_2151_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; uint8_t v___x_2188_; 
v_binderName_2148_ = lean_ctor_get(v_a_2147_, 0);
lean_inc(v_binderName_2148_);
v_binderType_2149_ = lean_ctor_get(v_a_2147_, 1);
lean_inc_ref(v_binderType_2149_);
v_body_2150_ = lean_ctor_get(v_a_2147_, 2);
lean_inc_ref(v_body_2150_);
v_binderInfo_2151_ = lean_ctor_get_uint8(v_a_2147_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_2147_);
v___x_2188_ = l_Lean_Expr_hasLooseBVars(v_body_2150_);
if (v___x_2188_ == 0)
{
v___y_2153_ = v___y_2141_;
v___y_2154_ = v___y_2142_;
v___y_2155_ = v___y_2143_;
v___y_2156_ = v___y_2144_;
goto v___jp_2152_;
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec_ref(v_body_2150_);
lean_dec_ref(v_binderType_2149_);
lean_dec(v_binderName_2148_);
v___x_2189_ = lean_obj_once(&l_Lean_MVarId_intro1___00__lam__0___closed__1, &l_Lean_MVarId_intro1___00__lam__0___closed__1_once, _init_l_Lean_MVarId_intro1___00__lam__0___closed__1);
v___x_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2190_, 0, v_mvarId_2140_);
v___x_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v___x_2191_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2192_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2192_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
v___jp_2152_:
{
lean_object* v___x_2157_; 
lean_inc(v_mvarId_2140_);
v___x_2157_ = l_Lean_MVarId_getTag(v_mvarId_2140_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2159_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref(v___x_2157_);
v___x_2159_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_body_2150_, v_a_2158_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2170_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc_n(v_a_2160_, 2);
lean_dec_ref(v___x_2159_);
v___x_2161_ = l_Lean_Expr_lam___override(v_binderName_2148_, v_binderType_2149_, v_a_2160_, v_binderInfo_2151_);
v___x_2162_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_2140_, v___x_2161_, v___y_2154_);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2170_ == 0)
{
lean_object* v_unused_2171_; 
v_unused_2171_ = lean_ctor_get(v___x_2162_, 0);
lean_dec(v_unused_2171_);
v___x_2164_ = v___x_2162_;
v_isShared_2165_ = v_isSharedCheck_2170_;
goto v_resetjp_2163_;
}
else
{
lean_dec(v___x_2162_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2170_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2166_ = l_Lean_Expr_mvarId_x21(v_a_2160_);
lean_dec(v_a_2160_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2166_);
v___x_2168_ = v___x_2164_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v_binderType_2149_);
lean_dec(v_binderName_2148_);
lean_dec(v_mvarId_2140_);
v_a_2172_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2159_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2159_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v_body_2150_);
lean_dec_ref(v_binderType_2149_);
lean_dec(v_binderName_2148_);
lean_dec(v_mvarId_2140_);
v_a_2180_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2157_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2157_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec(v_a_2147_);
v___x_2201_ = lean_obj_once(&l_Lean_MVarId_intro1___00__lam__0___closed__1, &l_Lean_MVarId_intro1___00__lam__0___closed__1_once, _init_l_Lean_MVarId_intro1___00__lam__0___closed__1);
v___x_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2202_, 0, v_mvarId_2140_);
v___x_2203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2201_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v___x_2203_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
return v___x_2204_;
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_mvarId_2140_);
v_a_2205_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2146_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2146_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__lam__0___boxed(lean_object* v_mvarId_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_MVarId_intro1___00__lam__0(v_mvarId_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1__(lean_object* v_mvarId_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v___f_2226_; lean_object* v___x_2227_; 
lean_inc(v_mvarId_2220_);
v___f_2226_ = lean_alloc_closure((void*)(l_Lean_MVarId_intro1___00__lam__0___boxed), 6, 1);
lean_closure_set(v___f_2226_, 0, v_mvarId_2220_);
v___x_2227_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_2220_, v___f_2226_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__boxed(lean_object* v_mvarId_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_MVarId_intro1__(v_mvarId_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(lean_object* v_00_u03b1_2235_, lean_object* v_msg_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v_msg_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___boxed(lean_object* v_00_u03b1_2243_, lean_object* v_msg_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(v_00_u03b1_2243_, v_msg_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntrosSize(lean_object* v_x_2251_){
_start:
{
switch(lean_obj_tag(v_x_2251_))
{
case 7:
{
lean_object* v_body_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_body_2252_ = lean_ctor_get(v_x_2251_, 2);
v___x_2253_ = l_Lean_Meta_getIntrosSize(v_body_2252_);
v___x_2254_ = lean_unsigned_to_nat(1u);
v___x_2255_ = lean_nat_add(v___x_2253_, v___x_2254_);
lean_dec(v___x_2253_);
return v___x_2255_;
}
case 8:
{
lean_object* v_body_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v_body_2256_ = lean_ctor_get(v_x_2251_, 3);
v___x_2257_ = l_Lean_Meta_getIntrosSize(v_body_2256_);
v___x_2258_ = lean_unsigned_to_nat(1u);
v___x_2259_ = lean_nat_add(v___x_2257_, v___x_2258_);
lean_dec(v___x_2257_);
return v___x_2259_;
}
case 10:
{
lean_object* v_expr_2260_; 
v_expr_2260_ = lean_ctor_get(v_x_2251_, 1);
v_x_2251_ = v_expr_2260_;
goto _start;
}
default: 
{
lean_object* v___x_2262_; 
v___x_2262_ = lean_unsigned_to_nat(0u);
return v___x_2262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntrosSize___boxed(lean_object* v_x_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_Meta_getIntrosSize(v_x_2263_);
lean_dec_ref(v_x_2263_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intros(lean_object* v_mvarId_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v___x_2271_; 
lean_inc(v_mvarId_2265_);
v___x_2271_ = l_Lean_MVarId_getType(v_mvarId_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2273_; lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2288_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref(v___x_2271_);
v___x_2273_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_a_2272_, v_a_2267_);
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2288_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2288_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v___x_2278_ = l_Lean_Meta_getIntrosSize(v_a_2274_);
lean_dec(v_a_2274_);
v___x_2279_ = lean_unsigned_to_nat(0u);
v___x_2280_ = lean_nat_dec_eq(v___x_2278_, v___x_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
lean_del_object(v___x_2276_);
v___x_2281_ = lean_box(0);
v___x_2282_ = l_Lean_Meta_introNCore(v_mvarId_2265_, v___x_2278_, v___x_2281_, v___x_2280_, v___x_2280_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
return v___x_2282_;
}
else
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2286_; 
lean_dec(v___x_2278_);
v___x_2283_ = ((lean_object*)(l_Lean_Meta_introNCore___closed__0));
v___x_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
lean_ctor_set(v___x_2284_, 1, v_mvarId_2265_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v___x_2284_);
v___x_2286_ = v___x_2276_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec(v_mvarId_2265_);
v_a_2289_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2271_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2271_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intros___boxed(lean_object* v_mvarId_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_MVarId_intros(v_mvarId_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
return v_res_2303_;
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
