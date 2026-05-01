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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(lean_object* v_lctx_708_, lean_object* v_binderName_709_, uint8_t v_hygienic_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
if (v_hygienic_710_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = l_Lean_LocalContext_getUnusedName(v_lctx_708_, v_binderName_709_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg___boxed(lean_object* v_lctx_717_, lean_object* v_binderName_718_, lean_object* v_hygienic_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
uint8_t v_hygienic_boxed_723_; lean_object* v_res_724_; 
v_hygienic_boxed_723_ = lean_unbox(v_hygienic_719_);
v_res_724_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_717_, v_binderName_718_, v_hygienic_boxed_723_, v_a_720_, v_a_721_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec_ref(v_lctx_717_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore(lean_object* v_lctx_725_, lean_object* v_binderName_726_, uint8_t v_hygienic_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_725_, v_binderName_726_, v_hygienic_727_, v_a_730_, v_a_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___boxed(lean_object* v_lctx_734_, lean_object* v_binderName_735_, lean_object* v_hygienic_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
uint8_t v_hygienic_boxed_742_; lean_object* v_res_743_; 
v_hygienic_boxed_742_ = lean_unbox(v_hygienic_736_);
v_res_743_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore(v_lctx_734_, v_binderName_735_, v_hygienic_boxed_742_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
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
lean_dec_ref(v___x_749_);
if (lean_obj_tag(v_val_751_) == 1)
{
uint8_t v_v_752_; 
v_v_752_ = lean_ctor_get_uint8(v_val_751_, 0);
lean_dec_ref(v_val_751_);
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
v___x_767_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_763_, v_binderName_758_, v___x_766_, v_a_760_, v_a_761_);
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
lean_dec_ref(v___x_825_);
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
v___x_803_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_793_, v_binderName_800_, v_hygienic_792_, v___y_801_, v___y_802_);
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
lean_dec_ref(v_x_880_);
goto v___jp_887_;
}
else
{
if (v_isExplicit_879_ == 0)
{
lean_object* v___x_893_; 
v___x_893_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_874_, v_hygienic_875_, v_lctx_877_, v_binderName_878_, v_x_880_, v_a_881_, v_a_882_);
return v___x_893_;
}
else
{
lean_inc(v_tail_886_);
lean_inc(v_head_885_);
lean_dec_ref(v_x_880_);
goto v___jp_887_;
}
}
v___jp_887_:
{
lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__1));
v___x_889_ = lean_name_eq(v_head_885_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec(v_binderName_878_);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v_head_885_);
lean_ctor_set(v___x_890_, 1, v_tail_886_);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
else
{
lean_object* v___x_892_; 
lean_dec(v_head_885_);
v___x_892_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_874_, v_hygienic_875_, v_lctx_877_, v_binderName_878_, v_tail_886_, v_a_881_, v_a_882_);
return v___x_892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___boxed(lean_object* v_preserveBinderNames_894_, lean_object* v_hygienic_895_, lean_object* v_useNamesForExplicitOnly_896_, lean_object* v_lctx_897_, lean_object* v_binderName_898_, lean_object* v_isExplicit_899_, lean_object* v_x_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
uint8_t v_preserveBinderNames_boxed_904_; uint8_t v_hygienic_boxed_905_; uint8_t v_useNamesForExplicitOnly_boxed_906_; uint8_t v_isExplicit_boxed_907_; lean_object* v_res_908_; 
v_preserveBinderNames_boxed_904_ = lean_unbox(v_preserveBinderNames_894_);
v_hygienic_boxed_905_ = lean_unbox(v_hygienic_895_);
v_useNamesForExplicitOnly_boxed_906_ = lean_unbox(v_useNamesForExplicitOnly_896_);
v_isExplicit_boxed_907_ = lean_unbox(v_isExplicit_899_);
v_res_908_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_boxed_904_, v_hygienic_boxed_905_, v_useNamesForExplicitOnly_boxed_906_, v_lctx_897_, v_binderName_898_, v_isExplicit_boxed_907_, v_x_900_, v_a_901_, v_a_902_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec_ref(v_lctx_897_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(uint8_t v_preserveBinderNames_909_, uint8_t v_hygienic_910_, uint8_t v_useNamesForExplicitOnly_911_, lean_object* v_lctx_912_, lean_object* v_binderName_913_, uint8_t v_isExplicit_914_, lean_object* v_x_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_909_, v_hygienic_910_, v_useNamesForExplicitOnly_911_, v_lctx_912_, v_binderName_913_, v_isExplicit_914_, v_x_915_, v_a_918_, v_a_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___boxed(lean_object* v_preserveBinderNames_922_, lean_object* v_hygienic_923_, lean_object* v_useNamesForExplicitOnly_924_, lean_object* v_lctx_925_, lean_object* v_binderName_926_, lean_object* v_isExplicit_927_, lean_object* v_x_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
uint8_t v_preserveBinderNames_boxed_934_; uint8_t v_hygienic_boxed_935_; uint8_t v_useNamesForExplicitOnly_boxed_936_; uint8_t v_isExplicit_boxed_937_; lean_object* v_res_938_; 
v_preserveBinderNames_boxed_934_ = lean_unbox(v_preserveBinderNames_922_);
v_hygienic_boxed_935_ = lean_unbox(v_hygienic_923_);
v_useNamesForExplicitOnly_boxed_936_ = lean_unbox(v_useNamesForExplicitOnly_924_);
v_isExplicit_boxed_937_ = lean_unbox(v_isExplicit_927_);
v_res_938_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(v_preserveBinderNames_boxed_934_, v_hygienic_boxed_935_, v_useNamesForExplicitOnly_boxed_936_, v_lctx_925_, v_binderName_926_, v_isExplicit_boxed_937_, v_x_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec_ref(v_lctx_925_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(lean_object* v_mvarId_939_, lean_object* v_x_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_939_, v_x_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_946_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_946_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
v_a_955_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_946_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_946_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg___boxed(lean_object* v_mvarId_963_, lean_object* v_x_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_963_, v_x_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(lean_object* v_00_u03b1_971_, lean_object* v_mvarId_972_, lean_object* v_x_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_972_, v_x_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___boxed(lean_object* v_00_u03b1_980_, lean_object* v_mvarId_981_, lean_object* v_x_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(v_00_u03b1_980_, v_mvarId_981_, v_x_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(size_t v_sz_989_, size_t v_i_990_, lean_object* v_bs_991_){
_start:
{
uint8_t v___x_992_; 
v___x_992_ = lean_usize_dec_lt(v_i_990_, v_sz_989_);
if (v___x_992_ == 0)
{
return v_bs_991_;
}
else
{
lean_object* v_v_993_; lean_object* v___x_994_; lean_object* v_bs_x27_995_; lean_object* v___x_996_; size_t v___x_997_; size_t v___x_998_; lean_object* v___x_999_; 
v_v_993_ = lean_array_uget(v_bs_991_, v_i_990_);
v___x_994_ = lean_unsigned_to_nat(0u);
v_bs_x27_995_ = lean_array_uset(v_bs_991_, v_i_990_, v___x_994_);
v___x_996_ = l_Lean_Expr_fvarId_x21(v_v_993_);
lean_dec(v_v_993_);
v___x_997_ = ((size_t)1ULL);
v___x_998_ = lean_usize_add(v_i_990_, v___x_997_);
v___x_999_ = lean_array_uset(v_bs_x27_995_, v_i_990_, v___x_996_);
v_i_990_ = v___x_998_;
v_bs_991_ = v___x_999_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1___boxed(lean_object* v_sz_1001_, lean_object* v_i_1002_, lean_object* v_bs_1003_){
_start:
{
size_t v_sz_boxed_1004_; size_t v_i_boxed_1005_; lean_object* v_res_1006_; 
v_sz_boxed_1004_ = lean_unbox_usize(v_sz_1001_);
lean_dec(v_sz_1001_);
v_i_boxed_1005_ = lean_unbox_usize(v_i_1002_);
lean_dec(v_i_1002_);
v_res_1006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(v_sz_boxed_1004_, v_i_boxed_1005_, v_bs_1003_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(lean_object* v_e_1007_, lean_object* v___y_1008_){
_start:
{
uint8_t v___x_1010_; 
v___x_1010_ = l_Lean_Expr_hasMVar(v_e_1007_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v_e_1007_);
return v___x_1011_;
}
else
{
lean_object* v___x_1012_; lean_object* v_mctx_1013_; lean_object* v___x_1014_; lean_object* v_fst_1015_; lean_object* v_snd_1016_; lean_object* v___x_1017_; lean_object* v_cache_1018_; lean_object* v_zetaDeltaFVarIds_1019_; lean_object* v_postponed_1020_; lean_object* v_diag_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1030_; 
v___x_1012_ = lean_st_ref_get(v___y_1008_);
v_mctx_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc_ref(v_mctx_1013_);
lean_dec(v___x_1012_);
v___x_1014_ = l_Lean_instantiateMVarsCore(v_mctx_1013_, v_e_1007_);
v_fst_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_fst_1015_);
v_snd_1016_ = lean_ctor_get(v___x_1014_, 1);
lean_inc(v_snd_1016_);
lean_dec_ref(v___x_1014_);
v___x_1017_ = lean_st_ref_take(v___y_1008_);
v_cache_1018_ = lean_ctor_get(v___x_1017_, 1);
v_zetaDeltaFVarIds_1019_ = lean_ctor_get(v___x_1017_, 2);
v_postponed_1020_ = lean_ctor_get(v___x_1017_, 3);
v_diag_1021_ = lean_ctor_get(v___x_1017_, 4);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1030_ == 0)
{
lean_object* v_unused_1031_; 
v_unused_1031_ = lean_ctor_get(v___x_1017_, 0);
lean_dec(v_unused_1031_);
v___x_1023_ = v___x_1017_;
v_isShared_1024_ = v_isSharedCheck_1030_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_diag_1021_);
lean_inc(v_postponed_1020_);
lean_inc(v_zetaDeltaFVarIds_1019_);
lean_inc(v_cache_1018_);
lean_dec(v___x_1017_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1030_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v_snd_1016_);
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_snd_1016_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_cache_1018_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_zetaDeltaFVarIds_1019_);
lean_ctor_set(v_reuseFailAlloc_1029_, 3, v_postponed_1020_);
lean_ctor_set(v_reuseFailAlloc_1029_, 4, v_diag_1021_);
v___x_1026_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_st_ref_set(v___y_1008_, v___x_1026_);
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v_fst_1015_);
return v___x_1028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg___boxed(lean_object* v_e_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_1032_, v___y_1033_);
lean_dec(v___y_1033_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; lean_object* v_ngen_1039_; lean_object* v_namePrefix_1040_; lean_object* v_idx_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1070_; 
v___x_1038_ = lean_st_ref_get(v___y_1036_);
v_ngen_1039_ = lean_ctor_get(v___x_1038_, 2);
lean_inc_ref(v_ngen_1039_);
lean_dec(v___x_1038_);
v_namePrefix_1040_ = lean_ctor_get(v_ngen_1039_, 0);
v_idx_1041_ = lean_ctor_get(v_ngen_1039_, 1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_ngen_1039_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1043_ = v_ngen_1039_;
v_isShared_1044_ = v_isSharedCheck_1070_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_idx_1041_);
lean_inc(v_namePrefix_1040_);
lean_dec(v_ngen_1039_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1070_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v_env_1046_; lean_object* v_nextMacroScope_1047_; lean_object* v_auxDeclNGen_1048_; lean_object* v_traceState_1049_; lean_object* v_cache_1050_; lean_object* v_messages_1051_; lean_object* v_infoState_1052_; lean_object* v_snapshotTasks_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1068_; 
v___x_1045_ = lean_st_ref_take(v___y_1036_);
v_env_1046_ = lean_ctor_get(v___x_1045_, 0);
v_nextMacroScope_1047_ = lean_ctor_get(v___x_1045_, 1);
v_auxDeclNGen_1048_ = lean_ctor_get(v___x_1045_, 3);
v_traceState_1049_ = lean_ctor_get(v___x_1045_, 4);
v_cache_1050_ = lean_ctor_get(v___x_1045_, 5);
v_messages_1051_ = lean_ctor_get(v___x_1045_, 6);
v_infoState_1052_ = lean_ctor_get(v___x_1045_, 7);
v_snapshotTasks_1053_ = lean_ctor_get(v___x_1045_, 8);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; 
v_unused_1069_ = lean_ctor_get(v___x_1045_, 2);
lean_dec(v_unused_1069_);
v___x_1055_ = v___x_1045_;
v_isShared_1056_ = v_isSharedCheck_1068_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_snapshotTasks_1053_);
lean_inc(v_infoState_1052_);
lean_inc(v_messages_1051_);
lean_inc(v_cache_1050_);
lean_inc(v_traceState_1049_);
lean_inc(v_auxDeclNGen_1048_);
lean_inc(v_nextMacroScope_1047_);
lean_inc(v_env_1046_);
lean_dec(v___x_1045_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1068_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_r_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
lean_inc(v_idx_1041_);
lean_inc(v_namePrefix_1040_);
v_r_1057_ = l_Lean_Name_num___override(v_namePrefix_1040_, v_idx_1041_);
v___x_1058_ = lean_unsigned_to_nat(1u);
v___x_1059_ = lean_nat_add(v_idx_1041_, v___x_1058_);
lean_dec(v_idx_1041_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 1, v___x_1059_);
v___x_1061_ = v___x_1043_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_namePrefix_1040_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1063_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 2, v___x_1061_);
v___x_1063_ = v___x_1055_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_env_1046_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_nextMacroScope_1047_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1066_, 3, v_auxDeclNGen_1048_);
lean_ctor_set(v_reuseFailAlloc_1066_, 4, v_traceState_1049_);
lean_ctor_set(v_reuseFailAlloc_1066_, 5, v_cache_1050_);
lean_ctor_set(v_reuseFailAlloc_1066_, 6, v_messages_1051_);
lean_ctor_set(v_reuseFailAlloc_1066_, 7, v_infoState_1052_);
lean_ctor_set(v_reuseFailAlloc_1066_, 8, v_snapshotTasks_1053_);
v___x_1063_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_st_ref_set(v___y_1036_, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_r_1057_);
return v___x_1065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1071_);
lean_dec(v___y_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
v___x_1079_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1077_);
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3___boxed(lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(lean_object* v_fvars_1094_, lean_object* v_j_1095_, lean_object* v_x_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp(lean_box(0), v_fvars_1094_, v_j_1095_, v_x_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1102_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
v_a_1111_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1102_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1102_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_fvars_1119_, lean_object* v_j_1120_, lean_object* v_x_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1119_, v_j_1120_, v_x_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(lean_object* v_fvars_1128_, lean_object* v_j_1129_, lean_object* v_x_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1128_, v_j_1129_, v_x_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1136_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1136_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
v_a_1145_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1136_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1136_);
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
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg___boxed(lean_object* v_fvars_1153_, lean_object* v_j_1154_, lean_object* v_x_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(v_fvars_1153_, v_j_1154_, v_x_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1(lean_object* v_00_u03b1_1162_, lean_object* v_fvars_1163_, lean_object* v_j_1164_, lean_object* v_x_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(v_fvars_1163_, v_j_1164_, v_x_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1172_, lean_object* v_fvars_1173_, lean_object* v_j_1174_, lean_object* v_x_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1(v_00_u03b1_1172_, v_fvars_1173_, v_j_1174_, v_x_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(lean_object* v_x_1182_, lean_object* v_x_1183_, lean_object* v_x_1184_, lean_object* v_x_1185_){
_start:
{
lean_object* v_ks_1186_; lean_object* v_vs_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1211_; 
v_ks_1186_ = lean_ctor_get(v_x_1182_, 0);
v_vs_1187_ = lean_ctor_get(v_x_1182_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_x_1182_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1189_ = v_x_1182_;
v_isShared_1190_ = v_isSharedCheck_1211_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_vs_1187_);
lean_inc(v_ks_1186_);
lean_dec(v_x_1182_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1211_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = lean_array_get_size(v_ks_1186_);
v___x_1192_ = lean_nat_dec_lt(v_x_1183_, v___x_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
lean_dec(v_x_1183_);
v___x_1193_ = lean_array_push(v_ks_1186_, v_x_1184_);
v___x_1194_ = lean_array_push(v_vs_1187_, v_x_1185_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___x_1194_);
lean_ctor_set(v___x_1189_, 0, v___x_1193_);
v___x_1196_ = v___x_1189_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
else
{
lean_object* v_k_x27_1198_; uint8_t v___x_1199_; 
v_k_x27_1198_ = lean_array_fget_borrowed(v_ks_1186_, v_x_1183_);
v___x_1199_ = l_Lean_instBEqMVarId_beq(v_x_1184_, v_k_x27_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1201_; 
if (v_isShared_1190_ == 0)
{
v___x_1201_ = v___x_1189_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_ks_1186_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_vs_1187_);
v___x_1201_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_unsigned_to_nat(1u);
v___x_1203_ = lean_nat_add(v_x_1183_, v___x_1202_);
lean_dec(v_x_1183_);
v_x_1182_ = v___x_1201_;
v_x_1183_ = v___x_1203_;
goto _start;
}
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1206_ = lean_array_fset(v_ks_1186_, v_x_1183_, v_x_1184_);
v___x_1207_ = lean_array_fset(v_vs_1187_, v_x_1183_, v_x_1185_);
lean_dec(v_x_1183_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___x_1207_);
lean_ctor_set(v___x_1189_, 0, v___x_1206_);
v___x_1209_ = v___x_1189_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(lean_object* v_n_1212_, lean_object* v_k_1213_, lean_object* v_v_1214_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(v_n_1212_, v___x_1215_, v_k_1213_, v_v_1214_);
return v___x_1216_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0(void){
_start:
{
size_t v___x_1217_; size_t v___x_1218_; size_t v___x_1219_; 
v___x_1217_ = ((size_t)5ULL);
v___x_1218_ = ((size_t)1ULL);
v___x_1219_ = lean_usize_shift_left(v___x_1218_, v___x_1217_);
return v___x_1219_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_1220_; size_t v___x_1221_; size_t v___x_1222_; 
v___x_1220_ = ((size_t)1ULL);
v___x_1221_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0);
v___x_1222_ = lean_usize_sub(v___x_1221_, v___x_1220_);
return v___x_1222_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_1224_, size_t v_x_1225_, size_t v_x_1226_, lean_object* v_x_1227_, lean_object* v_x_1228_){
_start:
{
if (lean_obj_tag(v_x_1224_) == 0)
{
lean_object* v_es_1229_; size_t v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; lean_object* v_j_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v_es_1229_ = lean_ctor_get(v_x_1224_, 0);
v___x_1230_ = ((size_t)5ULL);
v___x_1231_ = ((size_t)1ULL);
v___x_1232_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1);
v___x_1233_ = lean_usize_land(v_x_1225_, v___x_1232_);
v_j_1234_ = lean_usize_to_nat(v___x_1233_);
v___x_1235_ = lean_array_get_size(v_es_1229_);
v___x_1236_ = lean_nat_dec_lt(v_j_1234_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_dec(v_j_1234_);
lean_dec(v_x_1228_);
lean_dec(v_x_1227_);
return v_x_1224_;
}
else
{
lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1273_; 
lean_inc_ref(v_es_1229_);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_x_1224_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; 
v_unused_1274_ = lean_ctor_get(v_x_1224_, 0);
lean_dec(v_unused_1274_);
v___x_1238_ = v_x_1224_;
v_isShared_1239_ = v_isSharedCheck_1273_;
goto v_resetjp_1237_;
}
else
{
lean_dec(v_x_1224_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1273_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v_v_1240_; lean_object* v___x_1241_; lean_object* v_xs_x27_1242_; lean_object* v___y_1244_; 
v_v_1240_ = lean_array_fget(v_es_1229_, v_j_1234_);
v___x_1241_ = lean_box(0);
v_xs_x27_1242_ = lean_array_fset(v_es_1229_, v_j_1234_, v___x_1241_);
switch(lean_obj_tag(v_v_1240_))
{
case 0:
{
lean_object* v_key_1249_; lean_object* v_val_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1260_; 
v_key_1249_ = lean_ctor_get(v_v_1240_, 0);
v_val_1250_ = lean_ctor_get(v_v_1240_, 1);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_v_1240_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1252_ = v_v_1240_;
v_isShared_1253_ = v_isSharedCheck_1260_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_val_1250_);
lean_inc(v_key_1249_);
lean_dec(v_v_1240_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1260_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
uint8_t v___x_1254_; 
v___x_1254_ = l_Lean_instBEqMVarId_beq(v_x_1227_, v_key_1249_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_del_object(v___x_1252_);
v___x_1255_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1249_, v_val_1250_, v_x_1227_, v_x_1228_);
v___x_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
v___y_1244_ = v___x_1256_;
goto v___jp_1243_;
}
else
{
lean_object* v___x_1258_; 
lean_dec(v_val_1250_);
lean_dec(v_key_1249_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v_x_1228_);
lean_ctor_set(v___x_1252_, 0, v_x_1227_);
v___x_1258_ = v___x_1252_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_x_1227_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_x_1228_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
v___y_1244_ = v___x_1258_;
goto v___jp_1243_;
}
}
}
}
case 1:
{
lean_object* v_node_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1271_; 
v_node_1261_ = lean_ctor_get(v_v_1240_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_v_1240_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1263_ = v_v_1240_;
v_isShared_1264_ = v_isSharedCheck_1271_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_node_1261_);
lean_dec(v_v_1240_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1271_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
size_t v___x_1265_; size_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1265_ = lean_usize_shift_right(v_x_1225_, v___x_1230_);
v___x_1266_ = lean_usize_add(v_x_1226_, v___x_1231_);
v___x_1267_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_node_1261_, v___x_1265_, v___x_1266_, v_x_1227_, v_x_1228_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1267_);
v___x_1269_ = v___x_1263_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
v___y_1244_ = v___x_1269_;
goto v___jp_1243_;
}
}
}
default: 
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v_x_1227_);
lean_ctor_set(v___x_1272_, 1, v_x_1228_);
v___y_1244_ = v___x_1272_;
goto v___jp_1243_;
}
}
v___jp_1243_:
{
lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1245_ = lean_array_fset(v_xs_x27_1242_, v_j_1234_, v___y_1244_);
lean_dec(v_j_1234_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1245_);
v___x_1247_ = v___x_1238_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
else
{
lean_object* v_ks_1275_; lean_object* v_vs_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1296_; 
v_ks_1275_ = lean_ctor_get(v_x_1224_, 0);
v_vs_1276_ = lean_ctor_get(v_x_1224_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_x_1224_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1278_ = v_x_1224_;
v_isShared_1279_ = v_isSharedCheck_1296_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_vs_1276_);
lean_inc(v_ks_1275_);
lean_dec(v_x_1224_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1296_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_ks_1275_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_vs_1276_);
v___x_1281_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v_newNode_1282_; uint8_t v___y_1284_; size_t v___x_1290_; uint8_t v___x_1291_; 
v_newNode_1282_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(v___x_1281_, v_x_1227_, v_x_1228_);
v___x_1290_ = ((size_t)7ULL);
v___x_1291_ = lean_usize_dec_le(v___x_1290_, v_x_1226_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1292_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1282_);
v___x_1293_ = lean_unsigned_to_nat(4u);
v___x_1294_ = lean_nat_dec_lt(v___x_1292_, v___x_1293_);
lean_dec(v___x_1292_);
v___y_1284_ = v___x_1294_;
goto v___jp_1283_;
}
else
{
v___y_1284_ = v___x_1291_;
goto v___jp_1283_;
}
v___jp_1283_:
{
if (v___y_1284_ == 0)
{
lean_object* v_ks_1285_; lean_object* v_vs_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v_ks_1285_ = lean_ctor_get(v_newNode_1282_, 0);
lean_inc_ref(v_ks_1285_);
v_vs_1286_ = lean_ctor_get(v_newNode_1282_, 1);
lean_inc_ref(v_vs_1286_);
lean_dec_ref(v_newNode_1282_);
v___x_1287_ = lean_unsigned_to_nat(0u);
v___x_1288_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2);
v___x_1289_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_x_1226_, v_ks_1285_, v_vs_1286_, v___x_1287_, v___x_1288_);
lean_dec_ref(v_vs_1286_);
lean_dec_ref(v_ks_1285_);
return v___x_1289_;
}
else
{
return v_newNode_1282_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(size_t v_depth_1297_, lean_object* v_keys_1298_, lean_object* v_vals_1299_, lean_object* v_i_1300_, lean_object* v_entries_1301_){
_start:
{
lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = lean_array_get_size(v_keys_1298_);
v___x_1303_ = lean_nat_dec_lt(v_i_1300_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_dec(v_i_1300_);
return v_entries_1301_;
}
else
{
lean_object* v_k_1304_; lean_object* v_v_1305_; uint64_t v___x_1306_; size_t v_h_1307_; size_t v___x_1308_; lean_object* v___x_1309_; size_t v___x_1310_; size_t v___x_1311_; size_t v___x_1312_; size_t v_h_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_k_1304_ = lean_array_fget_borrowed(v_keys_1298_, v_i_1300_);
v_v_1305_ = lean_array_fget_borrowed(v_vals_1299_, v_i_1300_);
v___x_1306_ = l_Lean_instHashableMVarId_hash(v_k_1304_);
v_h_1307_ = lean_uint64_to_usize(v___x_1306_);
v___x_1308_ = ((size_t)5ULL);
v___x_1309_ = lean_unsigned_to_nat(1u);
v___x_1310_ = ((size_t)1ULL);
v___x_1311_ = lean_usize_sub(v_depth_1297_, v___x_1310_);
v___x_1312_ = lean_usize_mul(v___x_1308_, v___x_1311_);
v_h_1313_ = lean_usize_shift_right(v_h_1307_, v___x_1312_);
v___x_1314_ = lean_nat_add(v_i_1300_, v___x_1309_);
lean_dec(v_i_1300_);
lean_inc(v_v_1305_);
lean_inc(v_k_1304_);
v___x_1315_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_entries_1301_, v_h_1313_, v_depth_1297_, v_k_1304_, v_v_1305_);
v_i_1300_ = v___x_1314_;
v_entries_1301_ = v___x_1315_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_depth_1317_, lean_object* v_keys_1318_, lean_object* v_vals_1319_, lean_object* v_i_1320_, lean_object* v_entries_1321_){
_start:
{
size_t v_depth_boxed_1322_; lean_object* v_res_1323_; 
v_depth_boxed_1322_ = lean_unbox_usize(v_depth_1317_);
lean_dec(v_depth_1317_);
v_res_1323_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_boxed_1322_, v_keys_1318_, v_vals_1319_, v_i_1320_, v_entries_1321_);
lean_dec_ref(v_vals_1319_);
lean_dec_ref(v_keys_1318_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_x_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_, lean_object* v_x_1327_, lean_object* v_x_1328_){
_start:
{
size_t v_x_3906__boxed_1329_; size_t v_x_3907__boxed_1330_; lean_object* v_res_1331_; 
v_x_3906__boxed_1329_ = lean_unbox_usize(v_x_1325_);
lean_dec(v_x_1325_);
v_x_3907__boxed_1330_ = lean_unbox_usize(v_x_1326_);
lean_dec(v_x_1326_);
v_res_1331_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1324_, v_x_3906__boxed_1329_, v_x_3907__boxed_1330_, v_x_1327_, v_x_1328_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v_x_1334_){
_start:
{
uint64_t v___x_1335_; size_t v___x_1336_; size_t v___x_1337_; lean_object* v___x_1338_; 
v___x_1335_ = l_Lean_instHashableMVarId_hash(v_x_1333_);
v___x_1336_ = lean_uint64_to_usize(v___x_1335_);
v___x_1337_ = ((size_t)1ULL);
v___x_1338_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1332_, v___x_1336_, v___x_1337_, v_x_1333_, v_x_1334_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(lean_object* v_mvarId_1339_, lean_object* v_val_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; lean_object* v_mctx_1344_; lean_object* v_cache_1345_; lean_object* v_zetaDeltaFVarIds_1346_; lean_object* v_postponed_1347_; lean_object* v_diag_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1376_; 
v___x_1343_ = lean_st_ref_take(v___y_1341_);
v_mctx_1344_ = lean_ctor_get(v___x_1343_, 0);
v_cache_1345_ = lean_ctor_get(v___x_1343_, 1);
v_zetaDeltaFVarIds_1346_ = lean_ctor_get(v___x_1343_, 2);
v_postponed_1347_ = lean_ctor_get(v___x_1343_, 3);
v_diag_1348_ = lean_ctor_get(v___x_1343_, 4);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1350_ = v___x_1343_;
v_isShared_1351_ = v_isSharedCheck_1376_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_diag_1348_);
lean_inc(v_postponed_1347_);
lean_inc(v_zetaDeltaFVarIds_1346_);
lean_inc(v_cache_1345_);
lean_inc(v_mctx_1344_);
lean_dec(v___x_1343_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1376_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v_depth_1352_; lean_object* v_levelAssignDepth_1353_; lean_object* v_lmvarCounter_1354_; lean_object* v_mvarCounter_1355_; lean_object* v_lDecls_1356_; lean_object* v_decls_1357_; lean_object* v_userNames_1358_; lean_object* v_lAssignment_1359_; lean_object* v_eAssignment_1360_; lean_object* v_dAssignment_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1375_; 
v_depth_1352_ = lean_ctor_get(v_mctx_1344_, 0);
v_levelAssignDepth_1353_ = lean_ctor_get(v_mctx_1344_, 1);
v_lmvarCounter_1354_ = lean_ctor_get(v_mctx_1344_, 2);
v_mvarCounter_1355_ = lean_ctor_get(v_mctx_1344_, 3);
v_lDecls_1356_ = lean_ctor_get(v_mctx_1344_, 4);
v_decls_1357_ = lean_ctor_get(v_mctx_1344_, 5);
v_userNames_1358_ = lean_ctor_get(v_mctx_1344_, 6);
v_lAssignment_1359_ = lean_ctor_get(v_mctx_1344_, 7);
v_eAssignment_1360_ = lean_ctor_get(v_mctx_1344_, 8);
v_dAssignment_1361_ = lean_ctor_get(v_mctx_1344_, 9);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_mctx_1344_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1363_ = v_mctx_1344_;
v_isShared_1364_ = v_isSharedCheck_1375_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_dAssignment_1361_);
lean_inc(v_eAssignment_1360_);
lean_inc(v_lAssignment_1359_);
lean_inc(v_userNames_1358_);
lean_inc(v_decls_1357_);
lean_inc(v_lDecls_1356_);
lean_inc(v_mvarCounter_1355_);
lean_inc(v_lmvarCounter_1354_);
lean_inc(v_levelAssignDepth_1353_);
lean_inc(v_depth_1352_);
lean_dec(v_mctx_1344_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1375_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(v_eAssignment_1360_, v_mvarId_1339_, v_val_1340_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 8, v___x_1365_);
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_depth_1352_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_levelAssignDepth_1353_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_lmvarCounter_1354_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v_mvarCounter_1355_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v_lDecls_1356_);
lean_ctor_set(v_reuseFailAlloc_1374_, 5, v_decls_1357_);
lean_ctor_set(v_reuseFailAlloc_1374_, 6, v_userNames_1358_);
lean_ctor_set(v_reuseFailAlloc_1374_, 7, v_lAssignment_1359_);
lean_ctor_set(v_reuseFailAlloc_1374_, 8, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1374_, 9, v_dAssignment_1361_);
v___x_1367_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1369_; 
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1367_);
v___x_1369_ = v___x_1350_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_cache_1345_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_zetaDeltaFVarIds_1346_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_postponed_1347_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_diag_1348_);
v___x_1369_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1370_ = lean_st_ref_set(v___y_1341_, v___x_1369_);
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
return v___x_1372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg___boxed(lean_object* v_mvarId_1377_, lean_object* v_val_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1377_, v_val_1378_, v___y_1379_);
lean_dec(v___y_1379_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(lean_object* v_mvarId_1382_, lean_object* v_type_1383_, lean_object* v_fvars_1384_, uint8_t v_isZero_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v___x_1391_; 
lean_inc(v_mvarId_1382_);
v___x_1391_ = l_Lean_MVarId_getTag(v_mvarId_1382_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref(v___x_1391_);
v___x_1393_ = l_Lean_Expr_headBeta(v_type_1383_);
v___x_1394_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1393_, v_a_1392_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; uint8_t v___x_1396_; uint8_t v___x_1397_; lean_object* v___x_1398_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc_n(v_a_1395_, 2);
lean_dec_ref(v___x_1394_);
v___x_1396_ = 0;
v___x_1397_ = 1;
v___x_1398_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1384_, v_a_1395_, v___x_1396_, v_isZero_1385_, v___x_1396_, v_isZero_1385_, v___x_1397_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1400_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref(v___x_1398_);
v___x_1400_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1382_, v_a_1399_, v___y_1387_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1409_; 
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v___x_1400_, 0);
lean_dec(v_unused_1410_);
v___x_1402_ = v___x_1400_;
v_isShared_1403_ = v_isSharedCheck_1409_;
goto v_resetjp_1401_;
}
else
{
lean_dec(v___x_1400_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1409_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1404_ = l_Lean_Expr_mvarId_x21(v_a_1395_);
lean_dec(v_a_1395_);
v___x_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1405_, 0, v_fvars_1384_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1405_);
v___x_1407_ = v___x_1402_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec(v_a_1395_);
lean_dec_ref(v_fvars_1384_);
v_a_1411_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1400_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1400_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec(v_a_1395_);
lean_dec_ref(v_fvars_1384_);
lean_dec(v_mvarId_1382_);
v_a_1419_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1398_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1398_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec_ref(v_fvars_1384_);
lean_dec(v_mvarId_1382_);
v_a_1427_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1394_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1394_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec_ref(v_fvars_1384_);
lean_dec_ref(v_type_1383_);
lean_dec(v_mvarId_1382_);
v_a_1435_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1391_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1391_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0___boxed(lean_object* v_mvarId_1443_, lean_object* v_type_1444_, lean_object* v_fvars_1445_, lean_object* v_isZero_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
uint8_t v_isZero_boxed_1452_; lean_object* v_res_1453_; 
v_isZero_boxed_1452_ = lean_unbox(v_isZero_1446_);
v_res_1453_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(v_mvarId_1443_, v_type_1444_, v_fvars_1445_, v_isZero_boxed_1452_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(lean_object* v_lctx_1454_, lean_object* v_x_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_keyedConfig_1461_; uint8_t v_trackZetaDelta_1462_; lean_object* v_zetaDeltaSet_1463_; lean_object* v_localInstances_1464_; lean_object* v_defEqCtx_x3f_1465_; lean_object* v_synthPendingDepth_1466_; lean_object* v_canUnfold_x3f_1467_; uint8_t v_univApprox_1468_; uint8_t v_inTypeClassResolution_1469_; uint8_t v_cacheInferType_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v_keyedConfig_1461_ = lean_ctor_get(v___y_1456_, 0);
v_trackZetaDelta_1462_ = lean_ctor_get_uint8(v___y_1456_, sizeof(void*)*7);
v_zetaDeltaSet_1463_ = lean_ctor_get(v___y_1456_, 1);
v_localInstances_1464_ = lean_ctor_get(v___y_1456_, 3);
v_defEqCtx_x3f_1465_ = lean_ctor_get(v___y_1456_, 4);
v_synthPendingDepth_1466_ = lean_ctor_get(v___y_1456_, 5);
v_canUnfold_x3f_1467_ = lean_ctor_get(v___y_1456_, 6);
v_univApprox_1468_ = lean_ctor_get_uint8(v___y_1456_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1469_ = lean_ctor_get_uint8(v___y_1456_, sizeof(void*)*7 + 2);
v_cacheInferType_1470_ = lean_ctor_get_uint8(v___y_1456_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_1467_);
lean_inc(v_synthPendingDepth_1466_);
lean_inc(v_defEqCtx_x3f_1465_);
lean_inc_ref(v_localInstances_1464_);
lean_inc(v_zetaDeltaSet_1463_);
lean_inc_ref(v_keyedConfig_1461_);
v___x_1471_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1471_, 0, v_keyedConfig_1461_);
lean_ctor_set(v___x_1471_, 1, v_zetaDeltaSet_1463_);
lean_ctor_set(v___x_1471_, 2, v_lctx_1454_);
lean_ctor_set(v___x_1471_, 3, v_localInstances_1464_);
lean_ctor_set(v___x_1471_, 4, v_defEqCtx_x3f_1465_);
lean_ctor_set(v___x_1471_, 5, v_synthPendingDepth_1466_);
lean_ctor_set(v___x_1471_, 6, v_canUnfold_x3f_1467_);
lean_ctor_set_uint8(v___x_1471_, sizeof(void*)*7, v_trackZetaDelta_1462_);
lean_ctor_set_uint8(v___x_1471_, sizeof(void*)*7 + 1, v_univApprox_1468_);
lean_ctor_set_uint8(v___x_1471_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1469_);
lean_ctor_set_uint8(v___x_1471_, sizeof(void*)*7 + 3, v_cacheInferType_1470_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
lean_inc(v___y_1457_);
v___x_1472_ = lean_apply_5(v_x_1455_, v___x_1471_, v___y_1457_, v___y_1458_, v___y_1459_, lean_box(0));
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg___boxed(lean_object* v_lctx_1473_, lean_object* v_x_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1473_, v_x_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed(lean_object* v_type_1481_, lean_object* v_mvarId_1482_, lean_object* v_n_1483_, lean_object* v_preserveBinderNames_1484_, lean_object* v___x_1485_, lean_object* v_useNamesForExplicitOnly_1486_, lean_object* v_lctx_1487_, lean_object* v_fvars_1488_, lean_object* v___x_1489_, lean_object* v_s_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1496_; uint8_t v___x_4273__boxed_1497_; uint8_t v_useNamesForExplicitOnly_boxed_1498_; lean_object* v_res_1499_; 
v_preserveBinderNames_boxed_1496_ = lean_unbox(v_preserveBinderNames_1484_);
v___x_4273__boxed_1497_ = lean_unbox(v___x_1485_);
v_useNamesForExplicitOnly_boxed_1498_ = lean_unbox(v_useNamesForExplicitOnly_1486_);
v_res_1499_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(v_type_1481_, v_mvarId_1482_, v_n_1483_, v_preserveBinderNames_boxed_1496_, v___x_4273__boxed_1497_, v_useNamesForExplicitOnly_boxed_1498_, v_lctx_1487_, v_fvars_1488_, v___x_1489_, v_s_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v_n_1483_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(uint8_t v_preserveBinderNames_1500_, uint8_t v___x_1501_, uint8_t v_useNamesForExplicitOnly_1502_, lean_object* v_mvarId_1503_, lean_object* v_i_1504_, lean_object* v_lctx_1505_, lean_object* v_fvars_1506_, lean_object* v_j_1507_, lean_object* v_s_1508_, lean_object* v_type_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v_zero_1515_; uint8_t v_isZero_1516_; 
v_zero_1515_ = lean_unsigned_to_nat(0u);
v_isZero_1516_ = lean_nat_dec_eq(v_i_1504_, v_zero_1515_);
if (v_isZero_1516_ == 1)
{
lean_object* v___x_1517_; lean_object* v_type_1518_; lean_object* v___x_1519_; lean_object* v___f_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec(v_s_1508_);
lean_dec(v_i_1504_);
v___x_1517_ = lean_array_get_size(v_fvars_1506_);
v_type_1518_ = lean_expr_instantiate_rev_range(v_type_1509_, v_j_1507_, v___x_1517_, v_fvars_1506_);
lean_dec_ref(v_type_1509_);
v___x_1519_ = lean_box(v_isZero_1516_);
lean_inc_ref(v_fvars_1506_);
v___f_1520_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1520_, 0, v_mvarId_1503_);
lean_closure_set(v___f_1520_, 1, v_type_1518_);
lean_closure_set(v___f_1520_, 2, v_fvars_1506_);
lean_closure_set(v___f_1520_, 3, v___x_1519_);
v___x_1521_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed), 9, 4);
lean_closure_set(v___x_1521_, 0, lean_box(0));
lean_closure_set(v___x_1521_, 1, v_fvars_1506_);
lean_closure_set(v___x_1521_, 2, v_j_1507_);
lean_closure_set(v___x_1521_, 3, v___f_1520_);
v___x_1522_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1505_, v___x_1521_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
return v___x_1522_;
}
else
{
lean_object* v_one_1523_; lean_object* v_n_1524_; 
v_one_1523_ = lean_unsigned_to_nat(1u);
v_n_1524_ = lean_nat_sub(v_i_1504_, v_one_1523_);
lean_dec(v_i_1504_);
switch(lean_obj_tag(v_type_1509_))
{
case 8:
{
lean_object* v_declName_1525_; lean_object* v_type_1526_; lean_object* v_value_1527_; lean_object* v_body_1528_; lean_object* v___x_1529_; 
v_declName_1525_ = lean_ctor_get(v_type_1509_, 0);
lean_inc(v_declName_1525_);
v_type_1526_ = lean_ctor_get(v_type_1509_, 1);
lean_inc_ref(v_type_1526_);
v_value_1527_ = lean_ctor_get(v_type_1509_, 2);
lean_inc_ref(v_value_1527_);
v_body_1528_ = lean_ctor_get(v_type_1509_, 3);
lean_inc_ref(v_body_1528_);
lean_dec_ref(v_type_1509_);
v___x_1529_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; uint8_t v___x_1531_; lean_object* v___x_1532_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref(v___x_1529_);
v___x_1531_ = 1;
v___x_1532_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_1500_, v___x_1501_, v_useNamesForExplicitOnly_1502_, v_lctx_1505_, v_declName_1525_, v___x_1531_, v_s_1508_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v_fst_1534_; lean_object* v_snd_1535_; lean_object* v___x_1536_; lean_object* v_type_1537_; lean_object* v_type_1538_; lean_object* v_val_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref(v___x_1532_);
v_fst_1534_ = lean_ctor_get(v_a_1533_, 0);
lean_inc(v_fst_1534_);
v_snd_1535_ = lean_ctor_get(v_a_1533_, 1);
lean_inc(v_snd_1535_);
lean_dec(v_a_1533_);
v___x_1536_ = lean_array_get_size(v_fvars_1506_);
v_type_1537_ = lean_expr_instantiate_rev_range(v_type_1526_, v_j_1507_, v___x_1536_, v_fvars_1506_);
lean_dec_ref(v_type_1526_);
v_type_1538_ = l_Lean_Expr_headBeta(v_type_1537_);
v_val_1539_ = lean_expr_instantiate_rev_range(v_value_1527_, v_j_1507_, v___x_1536_, v_fvars_1506_);
lean_dec_ref(v_value_1527_);
v___x_1540_ = 0;
lean_inc(v_a_1530_);
v___x_1541_ = l_Lean_LocalContext_mkLetDecl(v_lctx_1505_, v_a_1530_, v_fst_1534_, v_type_1538_, v_val_1539_, v_isZero_1516_, v___x_1540_);
v___x_1542_ = l_Lean_mkFVar(v_a_1530_);
v___x_1543_ = lean_array_push(v_fvars_1506_, v___x_1542_);
v_i_1504_ = v_n_1524_;
v_lctx_1505_ = v___x_1541_;
v_fvars_1506_ = v___x_1543_;
v_s_1508_ = v_snd_1535_;
v_type_1509_ = v_body_1528_;
goto _start;
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec(v_a_1530_);
lean_dec_ref(v_body_1528_);
lean_dec_ref(v_value_1527_);
lean_dec_ref(v_type_1526_);
lean_dec(v_n_1524_);
lean_dec(v_j_1507_);
lean_dec_ref(v_fvars_1506_);
lean_dec_ref(v_lctx_1505_);
lean_dec(v_mvarId_1503_);
v_a_1545_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1532_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1532_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec_ref(v_body_1528_);
lean_dec_ref(v_value_1527_);
lean_dec_ref(v_type_1526_);
lean_dec(v_declName_1525_);
lean_dec(v_n_1524_);
lean_dec(v_s_1508_);
lean_dec(v_j_1507_);
lean_dec_ref(v_fvars_1506_);
lean_dec_ref(v_lctx_1505_);
lean_dec(v_mvarId_1503_);
v_a_1553_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1529_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1529_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1561_; lean_object* v_binderType_1562_; lean_object* v_body_1563_; uint8_t v_binderInfo_1564_; lean_object* v___x_1565_; 
v_binderName_1561_ = lean_ctor_get(v_type_1509_, 0);
lean_inc(v_binderName_1561_);
v_binderType_1562_ = lean_ctor_get(v_type_1509_, 1);
lean_inc_ref(v_binderType_1562_);
v_body_1563_ = lean_ctor_get(v_type_1509_, 2);
lean_inc_ref(v_body_1563_);
v_binderInfo_1564_ = lean_ctor_get_uint8(v_type_1509_, sizeof(void*)*3 + 8);
lean_dec_ref(v_type_1509_);
v___x_1565_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref(v___x_1565_);
v___x_1567_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_1564_);
v___x_1568_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_1500_, v___x_1501_, v_useNamesForExplicitOnly_1502_, v_lctx_1505_, v_binderName_1561_, v___x_1567_, v_s_1508_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v_fst_1570_; lean_object* v_snd_1571_; lean_object* v___x_1572_; lean_object* v_type_1573_; lean_object* v_type_1574_; uint8_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref(v___x_1568_);
v_fst_1570_ = lean_ctor_get(v_a_1569_, 0);
lean_inc(v_fst_1570_);
v_snd_1571_ = lean_ctor_get(v_a_1569_, 1);
lean_inc(v_snd_1571_);
lean_dec(v_a_1569_);
v___x_1572_ = lean_array_get_size(v_fvars_1506_);
v_type_1573_ = lean_expr_instantiate_rev_range(v_binderType_1562_, v_j_1507_, v___x_1572_, v_fvars_1506_);
lean_dec_ref(v_binderType_1562_);
v_type_1574_ = l_Lean_Expr_headBeta(v_type_1573_);
v___x_1575_ = 0;
lean_inc(v_a_1566_);
v___x_1576_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_1505_, v_a_1566_, v_fst_1570_, v_type_1574_, v_binderInfo_1564_, v___x_1575_);
v___x_1577_ = l_Lean_mkFVar(v_a_1566_);
v___x_1578_ = lean_array_push(v_fvars_1506_, v___x_1577_);
v_i_1504_ = v_n_1524_;
v_lctx_1505_ = v___x_1576_;
v_fvars_1506_ = v___x_1578_;
v_s_1508_ = v_snd_1571_;
v_type_1509_ = v_body_1563_;
goto _start;
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v_a_1566_);
lean_dec_ref(v_body_1563_);
lean_dec_ref(v_binderType_1562_);
lean_dec(v_n_1524_);
lean_dec(v_j_1507_);
lean_dec_ref(v_fvars_1506_);
lean_dec_ref(v_lctx_1505_);
lean_dec(v_mvarId_1503_);
v_a_1580_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1568_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1568_);
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
lean_dec_ref(v_body_1563_);
lean_dec_ref(v_binderType_1562_);
lean_dec(v_binderName_1561_);
lean_dec(v_n_1524_);
lean_dec(v_s_1508_);
lean_dec(v_j_1507_);
lean_dec_ref(v_fvars_1506_);
lean_dec_ref(v_lctx_1505_);
lean_dec(v_mvarId_1503_);
v_a_1588_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1565_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1565_);
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
default: 
{
lean_object* v___x_1596_; lean_object* v_type_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___f_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1596_ = lean_array_get_size(v_fvars_1506_);
v_type_1597_ = lean_expr_instantiate_rev_range(v_type_1509_, v_j_1507_, v___x_1596_, v_fvars_1506_);
lean_dec_ref(v_type_1509_);
v___x_1598_ = lean_box(v_preserveBinderNames_1500_);
v___x_1599_ = lean_box(v___x_1501_);
v___x_1600_ = lean_box(v_useNamesForExplicitOnly_1502_);
lean_inc_ref(v_fvars_1506_);
lean_inc_ref(v_lctx_1505_);
v___f_1601_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed), 15, 10);
lean_closure_set(v___f_1601_, 0, v_type_1597_);
lean_closure_set(v___f_1601_, 1, v_mvarId_1503_);
lean_closure_set(v___f_1601_, 2, v_n_1524_);
lean_closure_set(v___f_1601_, 3, v___x_1598_);
lean_closure_set(v___f_1601_, 4, v___x_1599_);
lean_closure_set(v___f_1601_, 5, v___x_1600_);
lean_closure_set(v___f_1601_, 6, v_lctx_1505_);
lean_closure_set(v___f_1601_, 7, v_fvars_1506_);
lean_closure_set(v___f_1601_, 8, v___x_1596_);
lean_closure_set(v___f_1601_, 9, v_s_1508_);
v___x_1602_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed), 9, 4);
lean_closure_set(v___x_1602_, 0, lean_box(0));
lean_closure_set(v___x_1602_, 1, v_fvars_1506_);
lean_closure_set(v___x_1602_, 2, v_j_1507_);
lean_closure_set(v___x_1602_, 3, v___f_1601_);
v___x_1603_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1505_, v___x_1602_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
return v___x_1603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(lean_object* v_type_1604_, lean_object* v_mvarId_1605_, lean_object* v_n_1606_, uint8_t v_preserveBinderNames_1607_, uint8_t v___x_1608_, uint8_t v_useNamesForExplicitOnly_1609_, lean_object* v_lctx_1610_, lean_object* v_fvars_1611_, lean_object* v___x_1612_, lean_object* v_s_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_type_1604_, v___y_1615_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1621_; uint8_t v___y_1623_; uint8_t v___x_1644_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref(v___x_1619_);
v___x_1621_ = l_Lean_Expr_cleanupAnnotations(v_a_1620_);
v___x_1644_ = l_Lean_Expr_isForall(v___x_1621_);
if (v___x_1644_ == 0)
{
uint8_t v___x_1645_; 
v___x_1645_ = l_Lean_Expr_isLet(v___x_1621_);
v___y_1623_ = v___x_1645_;
goto v___jp_1622_;
}
else
{
v___y_1623_ = v___x_1644_;
goto v___jp_1622_;
}
v___jp_1622_:
{
if (v___y_1623_ == 0)
{
lean_object* v___x_1624_; 
lean_inc(v___y_1617_);
lean_inc_ref(v___y_1616_);
lean_inc(v___y_1615_);
lean_inc_ref(v___y_1614_);
v___x_1624_ = lean_whnf(v___x_1621_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; uint8_t v___x_1626_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref(v___x_1624_);
v___x_1626_ = l_Lean_Expr_isForall(v_a_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec(v_a_1625_);
lean_dec(v_s_1613_);
lean_dec(v___x_1612_);
lean_dec_ref(v_fvars_1611_);
lean_dec_ref(v_lctx_1610_);
v___x_1627_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
v___x_1628_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4);
v___x_1629_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1627_, v_mvarId_1605_, v___x_1628_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
return v___x_1629_;
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = lean_unsigned_to_nat(1u);
v___x_1631_ = lean_nat_add(v_n_1606_, v___x_1630_);
v___x_1632_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1607_, v___x_1608_, v_useNamesForExplicitOnly_1609_, v_mvarId_1605_, v___x_1631_, v_lctx_1610_, v_fvars_1611_, v___x_1612_, v_s_1613_, v_a_1625_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
return v___x_1632_;
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v_s_1613_);
lean_dec(v___x_1612_);
lean_dec_ref(v_fvars_1611_);
lean_dec_ref(v_lctx_1610_);
lean_dec(v_mvarId_1605_);
v_a_1633_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1624_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1624_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
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
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1641_ = lean_unsigned_to_nat(1u);
v___x_1642_ = lean_nat_add(v_n_1606_, v___x_1641_);
v___x_1643_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1607_, v___x_1608_, v_useNamesForExplicitOnly_1609_, v_mvarId_1605_, v___x_1642_, v_lctx_1610_, v_fvars_1611_, v___x_1612_, v_s_1613_, v___x_1621_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
return v___x_1643_;
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v_s_1613_);
lean_dec(v___x_1612_);
lean_dec_ref(v_fvars_1611_);
lean_dec_ref(v_lctx_1610_);
lean_dec(v_mvarId_1605_);
v_a_1646_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1619_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1619_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___boxed(lean_object* v_preserveBinderNames_1654_, lean_object* v___x_1655_, lean_object* v_useNamesForExplicitOnly_1656_, lean_object* v_mvarId_1657_, lean_object* v_i_1658_, lean_object* v_lctx_1659_, lean_object* v_fvars_1660_, lean_object* v_j_1661_, lean_object* v_s_1662_, lean_object* v_type_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1669_; uint8_t v___x_4306__boxed_1670_; uint8_t v_useNamesForExplicitOnly_boxed_1671_; lean_object* v_res_1672_; 
v_preserveBinderNames_boxed_1669_ = lean_unbox(v_preserveBinderNames_1654_);
v___x_4306__boxed_1670_ = lean_unbox(v___x_1655_);
v_useNamesForExplicitOnly_boxed_1671_ = lean_unbox(v_useNamesForExplicitOnly_1656_);
v_res_1672_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_boxed_1669_, v___x_4306__boxed_1670_, v_useNamesForExplicitOnly_boxed_1671_, v_mvarId_1657_, v_i_1658_, v_lctx_1659_, v_fvars_1660_, v_j_1661_, v_s_1662_, v_type_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
lean_dec(v_a_1667_);
lean_dec_ref(v_a_1666_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___lam__0(lean_object* v_mvarId_1673_, lean_object* v___x_1674_, lean_object* v___x_1675_, uint8_t v_preserveBinderNames_1676_, uint8_t v___x_1677_, uint8_t v_useNamesForExplicitOnly_1678_, lean_object* v_n_1679_, lean_object* v_givenNames_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v___x_1686_; 
lean_inc(v_mvarId_1673_);
v___x_1686_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1673_, v___x_1674_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v___x_1687_; 
lean_dec_ref(v___x_1686_);
lean_inc(v_mvarId_1673_);
v___x_1687_ = l_Lean_MVarId_getType(v_mvarId_1673_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v_lctx_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref(v___x_1687_);
v_lctx_1689_ = lean_ctor_get(v___y_1681_, 2);
lean_inc_ref(v_lctx_1689_);
v___x_1690_ = lean_mk_empty_array_with_capacity(v___x_1675_);
v___x_1691_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1676_, v___x_1677_, v_useNamesForExplicitOnly_1678_, v_mvarId_1673_, v_n_1679_, v_lctx_1689_, v___x_1690_, v___x_1675_, v_givenNames_1680_, v_a_1688_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec_ref(v___y_1681_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1711_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1711_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1711_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v_fst_1696_; lean_object* v_snd_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1710_; 
v_fst_1696_ = lean_ctor_get(v_a_1692_, 0);
v_snd_1697_ = lean_ctor_get(v_a_1692_, 1);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_a_1692_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1699_ = v_a_1692_;
v_isShared_1700_ = v_isSharedCheck_1710_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_snd_1697_);
lean_inc(v_fst_1696_);
lean_dec(v_a_1692_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1710_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
size_t v_sz_1701_; size_t v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1705_; 
v_sz_1701_ = lean_array_size(v_fst_1696_);
v___x_1702_ = ((size_t)0ULL);
v___x_1703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(v_sz_1701_, v___x_1702_, v_fst_1696_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v___x_1703_);
v___x_1705_ = v___x_1699_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_snd_1697_);
v___x_1705_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1707_; 
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1705_);
v___x_1707_ = v___x_1694_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
v_a_1712_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1691_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1691_);
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
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
lean_dec_ref(v___y_1681_);
lean_dec(v_givenNames_1680_);
lean_dec(v_n_1679_);
lean_dec(v___x_1675_);
lean_dec(v_mvarId_1673_);
v_a_1720_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1687_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1687_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec_ref(v___y_1681_);
lean_dec(v_givenNames_1680_);
lean_dec(v_n_1679_);
lean_dec(v___x_1675_);
lean_dec(v_mvarId_1673_);
v_a_1728_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1686_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1686_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___lam__0___boxed(lean_object* v_mvarId_1736_, lean_object* v___x_1737_, lean_object* v___x_1738_, lean_object* v_preserveBinderNames_1739_, lean_object* v___x_1740_, lean_object* v_useNamesForExplicitOnly_1741_, lean_object* v_n_1742_, lean_object* v_givenNames_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1749_; uint8_t v___x_4536__boxed_1750_; uint8_t v_useNamesForExplicitOnly_boxed_1751_; lean_object* v_res_1752_; 
v_preserveBinderNames_boxed_1749_ = lean_unbox(v_preserveBinderNames_1739_);
v___x_4536__boxed_1750_ = lean_unbox(v___x_1740_);
v_useNamesForExplicitOnly_boxed_1751_ = lean_unbox(v_useNamesForExplicitOnly_1741_);
v_res_1752_ = l_Lean_Meta_introNCore___lam__0(v_mvarId_1736_, v___x_1737_, v___x_1738_, v_preserveBinderNames_boxed_1749_, v___x_4536__boxed_1750_, v_useNamesForExplicitOnly_boxed_1751_, v_n_1742_, v_givenNames_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore(lean_object* v_mvarId_1755_, lean_object* v_n_1756_, lean_object* v_givenNames_1757_, uint8_t v_useNamesForExplicitOnly_1758_, uint8_t v_preserveBinderNames_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1765_ = lean_unsigned_to_nat(0u);
v___x_1766_ = lean_nat_dec_eq(v_n_1756_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v_options_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___f_1774_; lean_object* v___x_1775_; 
v_options_1767_ = lean_ctor_get(v_a_1762_, 2);
v___x_1768_ = l_Lean_Meta_tactic_hygienic;
v___x_1769_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v_options_1767_, v___x_1768_);
v___x_1770_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
v___x_1771_ = lean_box(v_preserveBinderNames_1759_);
v___x_1772_ = lean_box(v___x_1769_);
v___x_1773_ = lean_box(v_useNamesForExplicitOnly_1758_);
lean_inc(v_mvarId_1755_);
v___f_1774_ = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1774_, 0, v_mvarId_1755_);
lean_closure_set(v___f_1774_, 1, v___x_1770_);
lean_closure_set(v___f_1774_, 2, v___x_1765_);
lean_closure_set(v___f_1774_, 3, v___x_1771_);
lean_closure_set(v___f_1774_, 4, v___x_1772_);
lean_closure_set(v___f_1774_, 5, v___x_1773_);
lean_closure_set(v___f_1774_, 6, v_n_1756_);
lean_closure_set(v___f_1774_, 7, v_givenNames_1757_);
v___x_1775_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_1755_, v___f_1774_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_);
return v___x_1775_;
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_dec(v_givenNames_1757_);
lean_dec(v_n_1756_);
v___x_1776_ = ((lean_object*)(l_Lean_Meta_introNCore___closed__0));
v___x_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
lean_ctor_set(v___x_1777_, 1, v_mvarId_1755_);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
return v___x_1778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___boxed(lean_object* v_mvarId_1779_, lean_object* v_n_1780_, lean_object* v_givenNames_1781_, lean_object* v_useNamesForExplicitOnly_1782_, lean_object* v_preserveBinderNames_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
uint8_t v_useNamesForExplicitOnly_boxed_1789_; uint8_t v_preserveBinderNames_boxed_1790_; lean_object* v_res_1791_; 
v_useNamesForExplicitOnly_boxed_1789_ = lean_unbox(v_useNamesForExplicitOnly_1782_);
v_preserveBinderNames_boxed_1790_ = lean_unbox(v_preserveBinderNames_1783_);
v_res_1791_ = l_Lean_Meta_introNCore(v_mvarId_1779_, v_n_1780_, v_givenNames_1781_, v_useNamesForExplicitOnly_boxed_1789_, v_preserveBinderNames_boxed_1790_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(lean_object* v_00_u03b1_1792_, lean_object* v_lctx_1793_, lean_object* v_x_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1793_, v_x_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1801_, lean_object* v_lctx_1802_, lean_object* v_x_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(v_00_u03b1_1801_, v_lctx_1802_, v_x_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(lean_object* v_e_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_1810_, v___y_1812_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___boxed(lean_object* v_e_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(v_e_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(lean_object* v_mvarId_1824_, lean_object* v_val_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1824_, v_val_1825_, v___y_1827_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___boxed(lean_object* v_mvarId_1832_, lean_object* v_val_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(v_mvarId_1832_, v_val_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1840_, lean_object* v_fvars_1841_, lean_object* v_j_1842_, lean_object* v_x_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1841_, v_j_1842_, v_x_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1850_, lean_object* v_fvars_1851_, lean_object* v_j_1852_, lean_object* v_x_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(v_00_u03b1_1850_, v_fvars_1851_, v_j_1852_, v_x_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1863_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___boxed(lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1872_, lean_object* v_x_1873_, lean_object* v_x_1874_, lean_object* v_x_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(v_x_1873_, v_x_1874_, v_x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1877_, lean_object* v_x_1878_, size_t v_x_1879_, size_t v_x_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1878_, v_x_1879_, v_x_1880_, v_x_1881_, v_x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_){
_start:
{
size_t v_x_4787__boxed_1890_; size_t v_x_4788__boxed_1891_; lean_object* v_res_1892_; 
v_x_4787__boxed_1890_ = lean_unbox_usize(v_x_1886_);
lean_dec(v_x_1886_);
v_x_4788__boxed_1891_ = lean_unbox_usize(v_x_1887_);
lean_dec(v_x_1887_);
v_res_1892_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1884_, v_x_1885_, v_x_4787__boxed_1890_, v_x_4788__boxed_1891_, v_x_1888_, v_x_1889_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11(lean_object* v_00_u03b2_1893_, lean_object* v_n_1894_, lean_object* v_k_1895_, lean_object* v_v_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(v_n_1894_, v_k_1895_, v_v_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(lean_object* v_00_u03b2_1898_, size_t v_depth_1899_, lean_object* v_keys_1900_, lean_object* v_vals_1901_, lean_object* v_heq_1902_, lean_object* v_i_1903_, lean_object* v_entries_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_1899_, v_keys_1900_, v_vals_1901_, v_i_1903_, v_entries_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_1906_, lean_object* v_depth_1907_, lean_object* v_keys_1908_, lean_object* v_vals_1909_, lean_object* v_heq_1910_, lean_object* v_i_1911_, lean_object* v_entries_1912_){
_start:
{
size_t v_depth_boxed_1913_; lean_object* v_res_1914_; 
v_depth_boxed_1913_ = lean_unbox_usize(v_depth_1907_);
lean_dec(v_depth_1907_);
v_res_1914_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(v_00_u03b2_1906_, v_depth_boxed_1913_, v_keys_1908_, v_vals_1909_, v_heq_1910_, v_i_1911_, v_entries_1912_);
lean_dec_ref(v_vals_1909_);
lean_dec_ref(v_keys_1908_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1915_, lean_object* v_x_1916_, lean_object* v_x_1917_, lean_object* v_x_1918_, lean_object* v_x_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(v_x_1916_, v_x_1917_, v_x_1918_, v_x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introN(lean_object* v_mvarId_1921_, lean_object* v_n_1922_, lean_object* v_givenNames_1923_, uint8_t v_useNamesForExplicitOnly_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_){
_start:
{
uint8_t v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = 0;
v___x_1931_ = l_Lean_Meta_introNCore(v_mvarId_1921_, v_n_1922_, v_givenNames_1923_, v_useNamesForExplicitOnly_1924_, v___x_1930_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introN___boxed(lean_object* v_mvarId_1932_, lean_object* v_n_1933_, lean_object* v_givenNames_1934_, lean_object* v_useNamesForExplicitOnly_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
uint8_t v_useNamesForExplicitOnly_boxed_1941_; lean_object* v_res_1942_; 
v_useNamesForExplicitOnly_boxed_1941_ = lean_unbox(v_useNamesForExplicitOnly_1935_);
v_res_1942_ = l_Lean_MVarId_introN(v_mvarId_1932_, v_n_1933_, v_givenNames_1934_, v_useNamesForExplicitOnly_boxed_1941_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1936_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introNP(lean_object* v_mvarId_1943_, lean_object* v_n_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v___x_1950_; uint8_t v___x_1951_; uint8_t v___x_1952_; lean_object* v___x_1953_; 
v___x_1950_ = lean_box(0);
v___x_1951_ = 0;
v___x_1952_ = 1;
v___x_1953_ = l_Lean_Meta_introNCore(v_mvarId_1943_, v_n_1944_, v___x_1950_, v___x_1951_, v___x_1952_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introNP___boxed(lean_object* v_mvarId_1954_, lean_object* v_n_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_MVarId_introNP(v_mvarId_1954_, v_n_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_);
lean_dec(v_a_1959_);
lean_dec_ref(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro(lean_object* v_mvarId_1962_, lean_object* v_name_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; lean_object* v___x_1973_; 
v___x_1969_ = lean_unsigned_to_nat(1u);
v___x_1970_ = lean_box(0);
v___x_1971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1971_, 0, v_name_1963_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = 0;
v___x_1973_ = l_Lean_Meta_introNCore(v_mvarId_1962_, v___x_1969_, v___x_1971_, v___x_1972_, v___x_1972_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1993_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1993_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1993_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v_fst_1978_; lean_object* v_snd_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1992_; 
v_fst_1978_ = lean_ctor_get(v_a_1974_, 0);
v_snd_1979_ = lean_ctor_get(v_a_1974_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_a_1974_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1981_ = v_a_1974_;
v_isShared_1982_ = v_isSharedCheck_1992_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_snd_1979_);
lean_inc(v_fst_1978_);
lean_dec(v_a_1974_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1992_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1983_ = lean_box(0);
v___x_1984_ = lean_unsigned_to_nat(0u);
v___x_1985_ = lean_array_get(v___x_1983_, v_fst_1978_, v___x_1984_);
lean_dec(v_fst_1978_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_1985_);
v___x_1987_ = v___x_1981_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_snd_1979_);
v___x_1987_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1989_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1987_);
v___x_1989_ = v___x_1976_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
v_a_1994_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1973_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1973_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro___boxed(lean_object* v_mvarId_2002_, lean_object* v_name_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_MVarId_intro(v_mvarId_2002_, v_name_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core(lean_object* v_mvarId_2010_, uint8_t v_preserveBinderNames_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; lean_object* v___x_2020_; 
v___x_2017_ = lean_unsigned_to_nat(1u);
v___x_2018_ = lean_box(0);
v___x_2019_ = 0;
v___x_2020_ = l_Lean_Meta_introNCore(v_mvarId_2010_, v___x_2017_, v___x_2018_, v___x_2019_, v_preserveBinderNames_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2040_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2023_ = v___x_2020_;
v_isShared_2024_ = v_isSharedCheck_2040_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2020_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2040_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v_fst_2025_; lean_object* v_snd_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2039_; 
v_fst_2025_ = lean_ctor_get(v_a_2021_, 0);
v_snd_2026_ = lean_ctor_get(v_a_2021_, 1);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_a_2021_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2028_ = v_a_2021_;
v_isShared_2029_ = v_isSharedCheck_2039_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_snd_2026_);
lean_inc(v_fst_2025_);
lean_dec(v_a_2021_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2039_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2034_; 
v___x_2030_ = lean_box(0);
v___x_2031_ = lean_unsigned_to_nat(0u);
v___x_2032_ = lean_array_get(v___x_2030_, v_fst_2025_, v___x_2031_);
lean_dec(v_fst_2025_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2032_);
v___x_2034_ = v___x_2028_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2032_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v_snd_2026_);
v___x_2034_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
lean_object* v___x_2036_; 
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2034_);
v___x_2036_ = v___x_2023_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
v_a_2041_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2020_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2020_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core___boxed(lean_object* v_mvarId_2049_, lean_object* v_preserveBinderNames_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
uint8_t v_preserveBinderNames_boxed_2056_; lean_object* v_res_2057_; 
v_preserveBinderNames_boxed_2056_ = lean_unbox(v_preserveBinderNames_2050_);
v_res_2057_ = l_Lean_Meta_intro1Core(v_mvarId_2049_, v_preserveBinderNames_boxed_2056_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1(lean_object* v_mvarId_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
uint8_t v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = 0;
v___x_2065_ = l_Lean_Meta_intro1Core(v_mvarId_2058_, v___x_2064_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___boxed(lean_object* v_mvarId_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_MVarId_intro1(v_mvarId_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
lean_dec(v_a_2070_);
lean_dec_ref(v_a_2069_);
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2067_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1P(lean_object* v_mvarId_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
uint8_t v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = 1;
v___x_2080_ = l_Lean_Meta_intro1Core(v_mvarId_2073_, v___x_2079_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1P___boxed(lean_object* v_mvarId_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_MVarId_intro1P(v_mvarId_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(lean_object* v_msgData_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v___x_2094_; lean_object* v_env_2095_; lean_object* v___x_2096_; lean_object* v_mctx_2097_; lean_object* v_lctx_2098_; lean_object* v_options_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2094_ = lean_st_ref_get(v___y_2092_);
v_env_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc_ref(v_env_2095_);
lean_dec(v___x_2094_);
v___x_2096_ = lean_st_ref_get(v___y_2090_);
v_mctx_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc_ref(v_mctx_2097_);
lean_dec(v___x_2096_);
v_lctx_2098_ = lean_ctor_get(v___y_2089_, 2);
v_options_2099_ = lean_ctor_get(v___y_2091_, 2);
lean_inc_ref(v_options_2099_);
lean_inc_ref(v_lctx_2098_);
v___x_2100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2100_, 0, v_env_2095_);
lean_ctor_set(v___x_2100_, 1, v_mctx_2097_);
lean_ctor_set(v___x_2100_, 2, v_lctx_2098_);
lean_ctor_set(v___x_2100_, 3, v_options_2099_);
v___x_2101_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v_msgData_2088_);
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0___boxed(lean_object* v_msgData_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msgData_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(lean_object* v_msg_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_ref_2116_; lean_object* v___x_2117_; lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2126_; 
v_ref_2116_ = lean_ctor_get(v___y_2113_, 5);
v___x_2117_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msg_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2126_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2126_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
lean_inc(v_ref_2116_);
v___x_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2122_, 0, v_ref_2116_);
lean_ctor_set(v___x_2122_, 1, v_a_2118_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set_tag(v___x_2120_, 1);
lean_ctor_set(v___x_2120_, 0, v___x_2122_);
v___x_2124_ = v___x_2120_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg___boxed(lean_object* v_msg_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v_msg_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2133_;
}
}
static lean_object* _init_l_Lean_MVarId_intro1___00__lam__0___closed__1(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = ((lean_object*)(l_Lean_MVarId_intro1___00__lam__0___closed__0));
v___x_2136_ = l_Lean_stringToMessageData(v___x_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__lam__0(lean_object* v_mvarId_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v___x_2143_; 
lean_inc(v_mvarId_2137_);
v___x_2143_ = l_Lean_MVarId_getType_x27(v_mvarId_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref(v___x_2143_);
if (lean_obj_tag(v_a_2144_) == 7)
{
lean_object* v_binderName_2145_; lean_object* v_binderType_2146_; lean_object* v_body_2147_; uint8_t v_binderInfo_2148_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; uint8_t v___x_2185_; 
v_binderName_2145_ = lean_ctor_get(v_a_2144_, 0);
lean_inc(v_binderName_2145_);
v_binderType_2146_ = lean_ctor_get(v_a_2144_, 1);
lean_inc_ref(v_binderType_2146_);
v_body_2147_ = lean_ctor_get(v_a_2144_, 2);
lean_inc_ref(v_body_2147_);
v_binderInfo_2148_ = lean_ctor_get_uint8(v_a_2144_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_2144_);
v___x_2185_ = l_Lean_Expr_hasLooseBVars(v_body_2147_);
if (v___x_2185_ == 0)
{
v___y_2150_ = v___y_2138_;
v___y_2151_ = v___y_2139_;
v___y_2152_ = v___y_2140_;
v___y_2153_ = v___y_2141_;
goto v___jp_2149_;
}
else
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec_ref(v_body_2147_);
lean_dec_ref(v_binderType_2146_);
lean_dec(v_binderName_2145_);
v___x_2186_ = lean_obj_once(&l_Lean_MVarId_intro1___00__lam__0___closed__1, &l_Lean_MVarId_intro1___00__lam__0___closed__1_once, _init_l_Lean_MVarId_intro1___00__lam__0___closed__1);
v___x_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2187_, 0, v_mvarId_2137_);
v___x_2188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2186_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
v___x_2189_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v___x_2188_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
v___jp_2149_:
{
lean_object* v___x_2154_; 
lean_inc(v_mvarId_2137_);
v___x_2154_ = l_Lean_MVarId_getTag(v_mvarId_2137_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2156_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref(v___x_2154_);
v___x_2156_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_body_2147_, v_a_2155_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2167_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc_n(v_a_2157_, 2);
lean_dec_ref(v___x_2156_);
v___x_2158_ = l_Lean_Expr_lam___override(v_binderName_2145_, v_binderType_2146_, v_a_2157_, v_binderInfo_2148_);
v___x_2159_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_2137_, v___x_2158_, v___y_2151_);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; 
v_unused_2168_ = lean_ctor_get(v___x_2159_, 0);
lean_dec(v_unused_2168_);
v___x_2161_ = v___x_2159_;
v_isShared_2162_ = v_isSharedCheck_2167_;
goto v_resetjp_2160_;
}
else
{
lean_dec(v___x_2159_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2167_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; lean_object* v___x_2165_; 
v___x_2163_ = l_Lean_Expr_mvarId_x21(v_a_2157_);
lean_dec(v_a_2157_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v___x_2163_);
v___x_2165_ = v___x_2161_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec_ref(v_binderType_2146_);
lean_dec(v_binderName_2145_);
lean_dec(v_mvarId_2137_);
v_a_2169_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2156_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2156_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec_ref(v_body_2147_);
lean_dec_ref(v_binderType_2146_);
lean_dec(v_binderName_2145_);
lean_dec(v_mvarId_2137_);
v_a_2177_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2154_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2154_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_dec(v_a_2144_);
v___x_2198_ = lean_obj_once(&l_Lean_MVarId_intro1___00__lam__0___closed__1, &l_Lean_MVarId_intro1___00__lam__0___closed__1_once, _init_l_Lean_MVarId_intro1___00__lam__0___closed__1);
v___x_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2199_, 0, v_mvarId_2137_);
v___x_2200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2198_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
v___x_2201_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v___x_2200_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
return v___x_2201_;
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec(v_mvarId_2137_);
v_a_2202_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2143_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2143_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__lam__0___boxed(lean_object* v_mvarId_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_MVarId_intro1___00__lam__0(v_mvarId_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1__(lean_object* v_mvarId_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v___f_2223_; lean_object* v___x_2224_; 
lean_inc(v_mvarId_2217_);
v___f_2223_ = lean_alloc_closure((void*)(l_Lean_MVarId_intro1___00__lam__0___boxed), 6, 1);
lean_closure_set(v___f_2223_, 0, v_mvarId_2217_);
v___x_2224_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_2217_, v___f_2223_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__boxed(lean_object* v_mvarId_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_MVarId_intro1__(v_mvarId_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(lean_object* v_00_u03b1_2232_, lean_object* v_msg_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v_msg_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___boxed(lean_object* v_00_u03b1_2240_, lean_object* v_msg_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(v_00_u03b1_2240_, v_msg_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntrosSize(lean_object* v_x_2248_){
_start:
{
switch(lean_obj_tag(v_x_2248_))
{
case 7:
{
lean_object* v_body_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v_body_2249_ = lean_ctor_get(v_x_2248_, 2);
v___x_2250_ = l_Lean_Meta_getIntrosSize(v_body_2249_);
v___x_2251_ = lean_unsigned_to_nat(1u);
v___x_2252_ = lean_nat_add(v___x_2250_, v___x_2251_);
lean_dec(v___x_2250_);
return v___x_2252_;
}
case 8:
{
lean_object* v_body_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v_body_2253_ = lean_ctor_get(v_x_2248_, 3);
v___x_2254_ = l_Lean_Meta_getIntrosSize(v_body_2253_);
v___x_2255_ = lean_unsigned_to_nat(1u);
v___x_2256_ = lean_nat_add(v___x_2254_, v___x_2255_);
lean_dec(v___x_2254_);
return v___x_2256_;
}
case 10:
{
lean_object* v_expr_2257_; 
v_expr_2257_ = lean_ctor_get(v_x_2248_, 1);
v_x_2248_ = v_expr_2257_;
goto _start;
}
default: 
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_unsigned_to_nat(0u);
return v___x_2259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntrosSize___boxed(lean_object* v_x_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Meta_getIntrosSize(v_x_2260_);
lean_dec_ref(v_x_2260_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intros(lean_object* v_mvarId_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v___x_2268_; 
lean_inc(v_mvarId_2262_);
v___x_2268_ = l_Lean_MVarId_getType(v_mvarId_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2270_; lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2285_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref(v___x_2268_);
v___x_2270_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_a_2269_, v_a_2264_);
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2273_ = v___x_2270_;
v_isShared_2274_ = v_isSharedCheck_2285_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2285_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; 
v___x_2275_ = l_Lean_Meta_getIntrosSize(v_a_2271_);
lean_dec(v_a_2271_);
v___x_2276_ = lean_unsigned_to_nat(0u);
v___x_2277_ = lean_nat_dec_eq(v___x_2275_, v___x_2276_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_del_object(v___x_2273_);
v___x_2278_ = lean_box(0);
v___x_2279_ = l_Lean_Meta_introNCore(v_mvarId_2262_, v___x_2275_, v___x_2278_, v___x_2277_, v___x_2277_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
return v___x_2279_;
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
lean_dec(v___x_2275_);
v___x_2280_ = ((lean_object*)(l_Lean_Meta_introNCore___closed__0));
v___x_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
lean_ctor_set(v___x_2281_, 1, v_mvarId_2262_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2281_);
v___x_2283_ = v___x_2273_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec(v_mvarId_2262_);
v_a_2286_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2268_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2268_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intros___boxed(lean_object* v_mvarId_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_MVarId_intros(v_mvarId_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
return v_res_2300_;
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
