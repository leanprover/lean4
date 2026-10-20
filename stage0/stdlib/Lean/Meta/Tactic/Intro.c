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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshFVarId___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_a_19_; lean_object* v___x_1325__overap_20_; lean_object* v___x_21_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_a_19_);
lean_dec_ref_known(v___x_18_, 1);
v___x_1325__overap_20_ = l_Lean_MVarId_assign___redArg(v___x_5_, v_mvarId_1_, v_a_19_);
v___x_21_ = lean_apply_5(v___x_1325__overap_20_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
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
v___x_84_ = l_instMonadEIO___redArg();
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___boxed(lean_object* v___x_99_, lean_object* v___x_100_, lean_object* v_type_101_, lean_object* v_n_102_, lean_object* v_mvarId_103_, lean_object* v_mkName_104_, lean_object* v_lctx_105_, lean_object* v_fvars_106_, lean_object* v___x_107_, lean_object* v_s_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1(v___x_99_, v___x_100_, v_type_101_, v_n_102_, v_mvarId_103_, v_mkName_104_, v_lctx_105_, v_fvars_106_, v___x_107_, v_s_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
lean_dec(v_n_102_);
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
lean_object* v___x_188_; lean_object* v_type_189_; lean_object* v___x_190_; lean_object* v___f_191_; lean_object* v___x_192_; lean_object* v___x_1294__overap_193_; lean_object* v___x_194_; 
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
v___x_1294__overap_193_ = l_Lean_Meta_withLCtx_x27___redArg(v___x_146_, v___x_183_, v_lctx_118_, v___x_192_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
v___x_194_ = lean_apply_5(v___x_1294__overap_193_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
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
lean_object* v_declName_197_; lean_object* v_type_198_; lean_object* v_value_199_; lean_object* v_body_200_; lean_object* v___x_201_; lean_object* v_type_202_; lean_object* v_type_203_; lean_object* v_val_204_; lean_object* v___x_1296__overap_205_; lean_object* v___x_206_; 
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
v___x_201_ = lean_array_get_size(v_fvars_119_);
v_type_202_ = lean_expr_instantiate_rev_range(v_type_198_, v_j_120_, v___x_201_, v_fvars_119_);
lean_dec_ref(v_type_198_);
v_type_203_ = l_Lean_Expr_headBeta(v_type_202_);
v_val_204_ = lean_expr_instantiate_rev_range(v_value_199_, v_j_120_, v___x_201_, v_fvars_119_);
lean_dec_ref(v_value_199_);
v___x_1296__overap_205_ = l_Lean_mkFreshFVarId___redArg(v___x_183_, v___x_185_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
v___x_206_ = lean_apply_5(v___x_1296__overap_205_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref_known(v___x_206_, 1);
v___x_208_ = 1;
v___x_209_ = lean_box(v___x_208_);
lean_inc_ref(v_mkName_116_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
lean_inc_ref(v_lctx_118_);
v___x_210_ = lean_apply_9(v_mkName_116_, v_lctx_118_, v_declName_197_, v___x_209_, v_s_121_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v_fst_212_; lean_object* v_snd_213_; uint8_t v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
lean_dec_ref_known(v___x_210_, 1);
v_fst_212_ = lean_ctor_get(v_a_211_, 0);
lean_inc(v_fst_212_);
v_snd_213_ = lean_ctor_get(v_a_211_, 1);
lean_inc(v_snd_213_);
lean_dec(v_a_211_);
v___x_214_ = 0;
lean_inc(v_a_207_);
v___x_215_ = l_Lean_LocalContext_mkLetDecl(v_lctx_118_, v_a_207_, v_fst_212_, v_type_203_, v_val_204_, v_isZero_187_, v___x_214_);
v___x_216_ = l_Lean_mkFVar(v_a_207_);
v___x_217_ = lean_array_push(v_fvars_119_, v___x_216_);
v_i_117_ = v_n_196_;
v_lctx_118_ = v___x_215_;
v_fvars_119_ = v___x_217_;
v_s_121_ = v_snd_213_;
v_type_122_ = v_body_200_;
goto _start;
}
else
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
lean_dec(v_a_207_);
lean_dec_ref(v_val_204_);
lean_dec_ref(v_type_203_);
lean_dec_ref(v_body_200_);
lean_dec(v_n_196_);
lean_dec(v_j_120_);
lean_dec_ref(v_fvars_119_);
lean_dec_ref(v_lctx_118_);
lean_dec_ref(v_mkName_116_);
lean_dec(v_mvarId_115_);
v_a_219_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_210_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_210_);
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
lean_dec_ref(v_val_204_);
lean_dec_ref(v_type_203_);
lean_dec_ref(v_body_200_);
lean_dec(v_declName_197_);
lean_dec(v_n_196_);
lean_dec(v_s_121_);
lean_dec(v_j_120_);
lean_dec_ref(v_fvars_119_);
lean_dec_ref(v_lctx_118_);
lean_dec_ref(v_mkName_116_);
lean_dec(v_mvarId_115_);
v_a_227_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_206_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_206_);
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
lean_object* v_binderName_235_; lean_object* v_binderType_236_; lean_object* v_body_237_; uint8_t v_binderInfo_238_; lean_object* v___x_239_; lean_object* v_type_240_; lean_object* v_type_241_; lean_object* v___x_1298__overap_242_; lean_object* v___x_243_; 
lean_dec_ref(v___x_146_);
v_binderName_235_ = lean_ctor_get(v_type_122_, 0);
lean_inc(v_binderName_235_);
v_binderType_236_ = lean_ctor_get(v_type_122_, 1);
lean_inc_ref(v_binderType_236_);
v_body_237_ = lean_ctor_get(v_type_122_, 2);
lean_inc_ref(v_body_237_);
v_binderInfo_238_ = lean_ctor_get_uint8(v_type_122_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_122_, 3);
v___x_239_ = lean_array_get_size(v_fvars_119_);
v_type_240_ = lean_expr_instantiate_rev_range(v_binderType_236_, v_j_120_, v___x_239_, v_fvars_119_);
lean_dec_ref(v_binderType_236_);
v_type_241_ = l_Lean_Expr_headBeta(v_type_240_);
v___x_1298__overap_242_ = l_Lean_mkFreshFVarId___redArg(v___x_183_, v___x_185_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
v___x_243_ = lean_apply_5(v___x_1298__overap_242_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_a_244_);
lean_dec_ref_known(v___x_243_, 1);
v___x_245_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_238_);
v___x_246_ = lean_box(v___x_245_);
lean_inc_ref(v_mkName_116_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
lean_inc_ref(v_lctx_118_);
v___x_247_ = lean_apply_9(v_mkName_116_, v_lctx_118_, v_binderName_235_, v___x_246_, v_s_121_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v_fst_249_; lean_object* v_snd_250_; uint8_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_248_);
lean_dec_ref_known(v___x_247_, 1);
v_fst_249_ = lean_ctor_get(v_a_248_, 0);
lean_inc(v_fst_249_);
v_snd_250_ = lean_ctor_get(v_a_248_, 1);
lean_inc(v_snd_250_);
lean_dec(v_a_248_);
v___x_251_ = 0;
lean_inc(v_a_244_);
v___x_252_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_118_, v_a_244_, v_fst_249_, v_type_241_, v_binderInfo_238_, v___x_251_);
v___x_253_ = l_Lean_mkFVar(v_a_244_);
v___x_254_ = lean_array_push(v_fvars_119_, v___x_253_);
v_i_117_ = v_n_196_;
v_lctx_118_ = v___x_252_;
v_fvars_119_ = v___x_254_;
v_s_121_ = v_snd_250_;
v_type_122_ = v_body_237_;
goto _start;
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec(v_a_244_);
lean_dec_ref(v_type_241_);
lean_dec_ref(v_body_237_);
lean_dec(v_n_196_);
lean_dec(v_j_120_);
lean_dec_ref(v_fvars_119_);
lean_dec_ref(v_lctx_118_);
lean_dec_ref(v_mkName_116_);
lean_dec(v_mvarId_115_);
v_a_256_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_247_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_247_);
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
lean_dec_ref(v_type_241_);
lean_dec_ref(v_body_237_);
lean_dec(v_binderName_235_);
lean_dec(v_n_196_);
lean_dec(v_s_121_);
lean_dec(v_j_120_);
lean_dec_ref(v_fvars_119_);
lean_dec_ref(v_lctx_118_);
lean_dec_ref(v_mkName_116_);
lean_dec(v_mvarId_115_);
v_a_264_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_243_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_243_);
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
lean_object* v___x_272_; lean_object* v_type_273_; lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___x_1304__overap_276_; lean_object* v___x_277_; 
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
lean_closure_set(v___f_274_, 3, v_n_196_);
lean_closure_set(v___f_274_, 4, v_mvarId_115_);
lean_closure_set(v___f_274_, 5, v_mkName_116_);
lean_closure_set(v___f_274_, 6, v_lctx_118_);
lean_closure_set(v___f_274_, 7, v_fvars_119_);
lean_closure_set(v___f_274_, 8, v___x_272_);
lean_closure_set(v___f_274_, 9, v_s_121_);
lean_inc_ref(v___x_146_);
v___x_275_ = l_Lean_Meta_withNewLocalInstances___redArg(v___x_146_, v___x_183_, v_fvars_119_, v_j_120_, v___f_274_);
v___x_1304__overap_276_ = l_Lean_Meta_withLCtx_x27___redArg(v___x_146_, v___x_183_, v_lctx_118_, v___x_275_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
v___x_277_ = lean_apply_5(v___x_1304__overap_276_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1(lean_object* v___x_284_, lean_object* v___x_285_, lean_object* v_type_286_, lean_object* v_n_287_, lean_object* v_mvarId_288_, lean_object* v_mkName_289_, lean_object* v_lctx_290_, lean_object* v_fvars_291_, lean_object* v___x_292_, lean_object* v_s_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_1352__overap_299_; lean_object* v___x_300_; 
v___x_1352__overap_299_ = l_Lean_instantiateMVars___redArg(v___x_284_, v___x_285_, v_type_286_);
lean_inc(v___y_297_);
lean_inc_ref(v___y_296_);
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
v___x_300_ = lean_apply_5(v___x_1352__overap_299_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, lean_box(0));
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_302_; uint8_t v___x_307_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref_known(v___x_300_, 1);
v___x_302_ = l_Lean_Expr_cleanupAnnotations(v_a_301_);
v___x_307_ = l_Lean_Expr_isForall(v___x_302_);
if (v___x_307_ == 0)
{
uint8_t v___x_308_; 
v___x_308_ = l_Lean_Expr_isLet(v___x_302_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
lean_inc(v___y_297_);
lean_inc_ref(v___y_296_);
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
v___x_309_ = lean_whnf(v___x_302_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; uint8_t v___x_311_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_309_, 1);
v___x_311_ = l_Lean_Expr_isForall(v_a_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec(v_a_310_);
lean_dec(v_s_293_);
lean_dec(v___x_292_);
lean_dec_ref(v_fvars_291_);
lean_dec_ref(v_lctx_290_);
lean_dec_ref(v_mkName_289_);
v___x_312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
v___x_313_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4);
v___x_314_ = l_Lean_Meta_throwTacticEx___redArg(v___x_312_, v_mvarId_288_, v___x_313_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
return v___x_314_;
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_add(v_n_287_, v___x_315_);
v___x_317_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_288_, v_mkName_289_, v___x_316_, v_lctx_290_, v_fvars_291_, v___x_292_, v_s_293_, v_a_310_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
return v___x_317_;
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v_s_293_);
lean_dec(v___x_292_);
lean_dec_ref(v_fvars_291_);
lean_dec_ref(v_lctx_290_);
lean_dec_ref(v_mkName_289_);
lean_dec(v_mvarId_288_);
v_a_318_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_309_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_309_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
goto v___jp_303_;
}
}
else
{
goto v___jp_303_;
}
v___jp_303_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_304_ = lean_unsigned_to_nat(1u);
v___x_305_ = lean_nat_add(v_n_287_, v___x_304_);
v___x_306_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_288_, v_mkName_289_, v___x_305_, v_lctx_290_, v_fvars_291_, v___x_292_, v_s_293_, v___x_302_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
return v___x_306_;
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v_s_293_);
lean_dec(v___x_292_);
lean_dec_ref(v_fvars_291_);
lean_dec_ref(v_lctx_290_);
lean_dec_ref(v_mkName_289_);
lean_dec(v_mvarId_288_);
v_a_326_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_300_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_300_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___boxed(lean_object* v_mvarId_334_, lean_object* v_mkName_335_, lean_object* v_i_336_, lean_object* v_lctx_337_, lean_object* v_fvars_338_, lean_object* v_j_339_, lean_object* v_s_340_, lean_object* v_type_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_334_, v_mkName_335_, v_i_336_, v_lctx_337_, v_fvars_338_, v_j_339_, v_s_340_, v_type_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(lean_object* v_00_u03c3_348_, lean_object* v_mvarId_349_, lean_object* v_mkName_350_, lean_object* v_i_351_, lean_object* v_lctx_352_, lean_object* v_fvars_353_, lean_object* v_j_354_, lean_object* v_s_355_, lean_object* v_type_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_349_, v_mkName_350_, v_i_351_, v_lctx_352_, v_fvars_353_, v_j_354_, v_s_355_, v_type_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___boxed(lean_object* v_00_u03c3_363_, lean_object* v_mvarId_364_, lean_object* v_mkName_365_, lean_object* v_i_366_, lean_object* v_lctx_367_, lean_object* v_fvars_368_, lean_object* v_j_369_, lean_object* v_s_370_, lean_object* v_type_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(v_00_u03c3_363_, v_mvarId_364_, v_mkName_365_, v_i_366_, v_lctx_367_, v_fvars_368_, v_j_369_, v_s_370_, v_type_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0(lean_object* v_mvarId_399_, lean_object* v___x_400_, lean_object* v_mkName_401_, lean_object* v_n_402_, lean_object* v_s_403_, lean_object* v___f_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___x_410_; 
lean_inc(v_mvarId_399_);
v___x_410_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_399_, v___x_400_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v___x_411_; 
lean_dec_ref_known(v___x_410_, 1);
lean_inc(v_mvarId_399_);
v___x_411_ = l_Lean_MVarId_getType(v_mvarId_399_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v_lctx_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_411_, 1);
v_lctx_413_ = lean_ctor_get(v___y_405_, 2);
lean_inc_ref(v_lctx_413_);
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__0));
v___x_416_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_399_, v_mkName_401_, v_n_402_, v_lctx_413_, v___x_415_, v___x_414_, v_s_403_, v_a_412_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec_ref(v___y_405_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_437_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_437_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_437_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_437_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v_fst_421_; lean_object* v_snd_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_436_; 
v_fst_421_ = lean_ctor_get(v_a_417_, 0);
v_snd_422_ = lean_ctor_get(v_a_417_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v_a_417_);
if (v_isSharedCheck_436_ == 0)
{
v___x_424_ = v_a_417_;
v_isShared_425_ = v_isSharedCheck_436_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_snd_422_);
lean_inc(v_fst_421_);
lean_dec(v_a_417_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_436_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; size_t v_sz_427_; size_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__10));
v_sz_427_ = lean_array_size(v_fst_421_);
v___x_428_ = ((size_t)0ULL);
v___x_429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_426_, v___f_404_, v_sz_427_, v___x_428_, v_fst_421_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_429_);
v___x_431_ = v___x_424_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_snd_422_);
v___x_431_ = v_reuseFailAlloc_435_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_433_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_431_);
v___x_433_ = v___x_419_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec_ref(v___f_404_);
v_a_438_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_416_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_416_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec_ref(v___y_405_);
lean_dec_ref(v___f_404_);
lean_dec(v_s_403_);
lean_dec(v_n_402_);
lean_dec_ref(v_mkName_401_);
lean_dec(v_mvarId_399_);
v_a_446_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_411_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_411_);
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
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
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
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_dec_ref(v___y_405_);
lean_dec_ref(v___f_404_);
lean_dec(v_s_403_);
lean_dec(v_n_402_);
lean_dec_ref(v_mkName_401_);
lean_dec(v_mvarId_399_);
v_a_454_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_410_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_410_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed(lean_object* v_mvarId_462_, lean_object* v___x_463_, lean_object* v_mkName_464_, lean_object* v_n_465_, lean_object* v_s_466_, lean_object* v___f_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0(v_mvarId_462_, v___x_463_, v_mkName_464_, v_n_465_, v_s_466_, v___f_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg(lean_object* v_mvarId_475_, lean_object* v_n_476_, lean_object* v_mkName_477_, lean_object* v_s_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v___x_484_; lean_object* v_toApplicative_485_; lean_object* v_toFunctor_486_; lean_object* v_toSeq_487_; lean_object* v_toSeqLeft_488_; lean_object* v_toSeqRight_489_; lean_object* v___f_490_; lean_object* v___f_491_; lean_object* v___f_492_; lean_object* v___f_493_; lean_object* v___x_494_; lean_object* v___f_495_; lean_object* v___f_496_; lean_object* v___f_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_toApplicative_503_; lean_object* v_toFunctor_504_; lean_object* v_toSeq_505_; lean_object* v_toSeqLeft_506_; lean_object* v_toSeqRight_507_; lean_object* v___f_508_; lean_object* v___f_509_; lean_object* v___x_510_; lean_object* v___f_511_; lean_object* v___f_512_; lean_object* v___f_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v_toApplicative_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_549_; 
v___x_484_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
v_toApplicative_485_ = lean_ctor_get(v___x_484_, 0);
v_toFunctor_486_ = lean_ctor_get(v_toApplicative_485_, 0);
v_toSeq_487_ = lean_ctor_get(v_toApplicative_485_, 2);
v_toSeqLeft_488_ = lean_ctor_get(v_toApplicative_485_, 3);
v_toSeqRight_489_ = lean_ctor_get(v_toApplicative_485_, 4);
v___f_490_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2));
v___f_491_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_486_, 2);
v___f_492_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_492_, 0, v_toFunctor_486_);
v___f_493_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_493_, 0, v_toFunctor_486_);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___f_492_);
lean_ctor_set(v___x_494_, 1, v___f_493_);
lean_inc(v_toSeqRight_489_);
v___f_495_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_495_, 0, v_toSeqRight_489_);
lean_inc(v_toSeqLeft_488_);
v___f_496_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_496_, 0, v_toSeqLeft_488_);
lean_inc(v_toSeq_487_);
v___f_497_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_497_, 0, v_toSeq_487_);
v___x_498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_498_, 0, v___x_494_);
lean_ctor_set(v___x_498_, 1, v___f_490_);
lean_ctor_set(v___x_498_, 2, v___f_497_);
lean_ctor_set(v___x_498_, 3, v___f_496_);
lean_ctor_set(v___x_498_, 4, v___f_495_);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___f_491_);
v___x_500_ = l_StateRefT_x27_instMonad___redArg(v___x_499_);
v___x_501_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_501_, 0, lean_box(0));
lean_closure_set(v___x_501_, 1, lean_box(0));
lean_closure_set(v___x_501_, 2, v___x_500_);
v___x_502_ = l_instMonadControlTOfPure___redArg(v___x_501_);
v_toApplicative_503_ = lean_ctor_get(v___x_484_, 0);
v_toFunctor_504_ = lean_ctor_get(v_toApplicative_503_, 0);
v_toSeq_505_ = lean_ctor_get(v_toApplicative_503_, 2);
v_toSeqLeft_506_ = lean_ctor_get(v_toApplicative_503_, 3);
v_toSeqRight_507_ = lean_ctor_get(v_toApplicative_503_, 4);
lean_inc_ref_n(v_toFunctor_504_, 2);
v___f_508_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_508_, 0, v_toFunctor_504_);
v___f_509_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_509_, 0, v_toFunctor_504_);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___f_508_);
lean_ctor_set(v___x_510_, 1, v___f_509_);
lean_inc(v_toSeqRight_507_);
v___f_511_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_511_, 0, v_toSeqRight_507_);
lean_inc(v_toSeqLeft_506_);
v___f_512_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_512_, 0, v_toSeqLeft_506_);
lean_inc(v_toSeq_505_);
v___f_513_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_513_, 0, v_toSeq_505_);
v___x_514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_514_, 0, v___x_510_);
lean_ctor_set(v___x_514_, 1, v___f_490_);
lean_ctor_set(v___x_514_, 2, v___f_513_);
lean_ctor_set(v___x_514_, 3, v___f_512_);
lean_ctor_set(v___x_514_, 4, v___f_511_);
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v___f_491_);
v___x_516_ = l_StateRefT_x27_instMonad___redArg(v___x_515_);
v_toApplicative_517_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; 
v_unused_550_ = lean_ctor_get(v___x_516_, 1);
lean_dec(v_unused_550_);
v___x_519_ = v___x_516_;
v_isShared_520_ = v_isSharedCheck_549_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_toApplicative_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_549_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_toFunctor_521_; lean_object* v_toSeq_522_; lean_object* v_toSeqLeft_523_; lean_object* v_toSeqRight_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_547_; 
v_toFunctor_521_ = lean_ctor_get(v_toApplicative_517_, 0);
v_toSeq_522_ = lean_ctor_get(v_toApplicative_517_, 2);
v_toSeqLeft_523_ = lean_ctor_get(v_toApplicative_517_, 3);
v_toSeqRight_524_ = lean_ctor_get(v_toApplicative_517_, 4);
v_isSharedCheck_547_ = !lean_is_exclusive(v_toApplicative_517_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; 
v_unused_548_ = lean_ctor_get(v_toApplicative_517_, 1);
lean_dec(v_unused_548_);
v___x_526_ = v_toApplicative_517_;
v_isShared_527_ = v_isSharedCheck_547_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_toSeqRight_524_);
lean_inc(v_toSeqLeft_523_);
lean_inc(v_toSeq_522_);
lean_inc(v_toFunctor_521_);
lean_dec(v_toApplicative_517_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_547_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___f_528_; lean_object* v___f_529_; lean_object* v___f_530_; lean_object* v___f_531_; lean_object* v___f_532_; lean_object* v___x_533_; lean_object* v___f_534_; lean_object* v___f_535_; lean_object* v___f_536_; lean_object* v___x_538_; 
v___f_528_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0));
v___f_529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4));
v___f_530_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5));
lean_inc_ref(v_toFunctor_521_);
v___f_531_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_531_, 0, v_toFunctor_521_);
v___f_532_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_532_, 0, v_toFunctor_521_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v___f_531_);
lean_ctor_set(v___x_533_, 1, v___f_532_);
v___f_534_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_534_, 0, v_toSeqRight_524_);
v___f_535_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_535_, 0, v_toSeqLeft_523_);
v___f_536_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_536_, 0, v_toSeq_522_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 4, v___f_534_);
lean_ctor_set(v___x_526_, 3, v___f_535_);
lean_ctor_set(v___x_526_, 2, v___f_536_);
lean_ctor_set(v___x_526_, 1, v___f_529_);
lean_ctor_set(v___x_526_, 0, v___x_533_);
v___x_538_ = v___x_526_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v___f_529_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v___f_536_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v___f_535_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v___f_534_);
v___x_538_ = v_reuseFailAlloc_546_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_540_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v___f_530_);
lean_ctor_set(v___x_519_, 0, v___x_538_);
v___x_540_ = v___x_519_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v___f_530_);
v___x_540_ = v_reuseFailAlloc_545_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; lean_object* v___f_542_; lean_object* v___x_534__overap_543_; lean_object* v___x_544_; 
v___x_541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
lean_inc(v_mvarId_475_);
v___f_542_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_542_, 0, v_mvarId_475_);
lean_closure_set(v___f_542_, 1, v___x_541_);
lean_closure_set(v___f_542_, 2, v_mkName_477_);
lean_closure_set(v___f_542_, 3, v_n_476_);
lean_closure_set(v___f_542_, 4, v_s_478_);
lean_closure_set(v___f_542_, 5, v___f_528_);
v___x_534__overap_543_ = l_Lean_MVarId_withContext___redArg(v___x_502_, v___x_540_, v_mvarId_475_, v___f_542_);
lean_inc(v_a_482_);
lean_inc_ref(v_a_481_);
lean_inc(v_a_480_);
lean_inc_ref(v_a_479_);
v___x_544_ = lean_apply_5(v___x_534__overap_543_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, lean_box(0));
return v___x_544_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___boxed(lean_object* v_mvarId_551_, lean_object* v_n_552_, lean_object* v_mkName_553_, lean_object* v_s_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg(v_mvarId_551_, v_n_552_, v_mkName_553_, v_s_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(lean_object* v_00_u03c3_561_, lean_object* v_mvarId_562_, lean_object* v_n_563_, lean_object* v_mkName_564_, lean_object* v_s_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_571_; lean_object* v_toApplicative_572_; lean_object* v_toFunctor_573_; lean_object* v_toSeq_574_; lean_object* v_toSeqLeft_575_; lean_object* v_toSeqRight_576_; lean_object* v___f_577_; lean_object* v___f_578_; lean_object* v___f_579_; lean_object* v___f_580_; lean_object* v___x_581_; lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___f_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_toApplicative_590_; lean_object* v_toFunctor_591_; lean_object* v_toSeq_592_; lean_object* v_toSeqLeft_593_; lean_object* v_toSeqRight_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___x_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___f_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v_toApplicative_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_636_; 
v___x_571_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
v_toApplicative_572_ = lean_ctor_get(v___x_571_, 0);
v_toFunctor_573_ = lean_ctor_get(v_toApplicative_572_, 0);
v_toSeq_574_ = lean_ctor_get(v_toApplicative_572_, 2);
v_toSeqLeft_575_ = lean_ctor_get(v_toApplicative_572_, 3);
v_toSeqRight_576_ = lean_ctor_get(v_toApplicative_572_, 4);
v___f_577_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2));
v___f_578_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_573_, 2);
v___f_579_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_579_, 0, v_toFunctor_573_);
v___f_580_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_580_, 0, v_toFunctor_573_);
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v___f_579_);
lean_ctor_set(v___x_581_, 1, v___f_580_);
lean_inc(v_toSeqRight_576_);
v___f_582_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_582_, 0, v_toSeqRight_576_);
lean_inc(v_toSeqLeft_575_);
v___f_583_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_583_, 0, v_toSeqLeft_575_);
lean_inc(v_toSeq_574_);
v___f_584_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_584_, 0, v_toSeq_574_);
v___x_585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_585_, 0, v___x_581_);
lean_ctor_set(v___x_585_, 1, v___f_577_);
lean_ctor_set(v___x_585_, 2, v___f_584_);
lean_ctor_set(v___x_585_, 3, v___f_583_);
lean_ctor_set(v___x_585_, 4, v___f_582_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___f_578_);
v___x_587_ = l_StateRefT_x27_instMonad___redArg(v___x_586_);
v___x_588_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_588_, 0, lean_box(0));
lean_closure_set(v___x_588_, 1, lean_box(0));
lean_closure_set(v___x_588_, 2, v___x_587_);
v___x_589_ = l_instMonadControlTOfPure___redArg(v___x_588_);
v_toApplicative_590_ = lean_ctor_get(v___x_571_, 0);
v_toFunctor_591_ = lean_ctor_get(v_toApplicative_590_, 0);
v_toSeq_592_ = lean_ctor_get(v_toApplicative_590_, 2);
v_toSeqLeft_593_ = lean_ctor_get(v_toApplicative_590_, 3);
v_toSeqRight_594_ = lean_ctor_get(v_toApplicative_590_, 4);
lean_inc_ref_n(v_toFunctor_591_, 2);
v___f_595_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_595_, 0, v_toFunctor_591_);
v___f_596_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_596_, 0, v_toFunctor_591_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v___f_595_);
lean_ctor_set(v___x_597_, 1, v___f_596_);
lean_inc(v_toSeqRight_594_);
v___f_598_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_598_, 0, v_toSeqRight_594_);
lean_inc(v_toSeqLeft_593_);
v___f_599_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_599_, 0, v_toSeqLeft_593_);
lean_inc(v_toSeq_592_);
v___f_600_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_600_, 0, v_toSeq_592_);
v___x_601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_601_, 0, v___x_597_);
lean_ctor_set(v___x_601_, 1, v___f_577_);
lean_ctor_set(v___x_601_, 2, v___f_600_);
lean_ctor_set(v___x_601_, 3, v___f_599_);
lean_ctor_set(v___x_601_, 4, v___f_598_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___f_578_);
v___x_603_ = l_StateRefT_x27_instMonad___redArg(v___x_602_);
v_toApplicative_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; 
v_unused_637_ = lean_ctor_get(v___x_603_, 1);
lean_dec(v_unused_637_);
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_636_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_toApplicative_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_636_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v_toFunctor_608_; lean_object* v_toSeq_609_; lean_object* v_toSeqLeft_610_; lean_object* v_toSeqRight_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_634_; 
v_toFunctor_608_ = lean_ctor_get(v_toApplicative_604_, 0);
v_toSeq_609_ = lean_ctor_get(v_toApplicative_604_, 2);
v_toSeqLeft_610_ = lean_ctor_get(v_toApplicative_604_, 3);
v_toSeqRight_611_ = lean_ctor_get(v_toApplicative_604_, 4);
v_isSharedCheck_634_ = !lean_is_exclusive(v_toApplicative_604_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; 
v_unused_635_ = lean_ctor_get(v_toApplicative_604_, 1);
lean_dec(v_unused_635_);
v___x_613_ = v_toApplicative_604_;
v_isShared_614_ = v_isSharedCheck_634_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_toSeqRight_611_);
lean_inc(v_toSeqLeft_610_);
lean_inc(v_toSeq_609_);
lean_inc(v_toFunctor_608_);
lean_dec(v_toApplicative_604_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_634_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___f_615_; lean_object* v___f_616_; lean_object* v___f_617_; lean_object* v___f_618_; lean_object* v___f_619_; lean_object* v___x_620_; lean_object* v___f_621_; lean_object* v___f_622_; lean_object* v___f_623_; lean_object* v___x_625_; 
v___f_615_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0));
v___f_616_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4));
v___f_617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5));
lean_inc_ref(v_toFunctor_608_);
v___f_618_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_618_, 0, v_toFunctor_608_);
v___f_619_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_619_, 0, v_toFunctor_608_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___f_618_);
lean_ctor_set(v___x_620_, 1, v___f_619_);
v___f_621_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_621_, 0, v_toSeqRight_611_);
v___f_622_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_622_, 0, v_toSeqLeft_610_);
v___f_623_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_623_, 0, v_toSeq_609_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 4, v___f_621_);
lean_ctor_set(v___x_613_, 3, v___f_622_);
lean_ctor_set(v___x_613_, 2, v___f_623_);
lean_ctor_set(v___x_613_, 1, v___f_616_);
lean_ctor_set(v___x_613_, 0, v___x_620_);
v___x_625_ = v___x_613_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___f_616_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v___f_623_);
lean_ctor_set(v_reuseFailAlloc_633_, 3, v___f_622_);
lean_ctor_set(v_reuseFailAlloc_633_, 4, v___f_621_);
v___x_625_ = v_reuseFailAlloc_633_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_627_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v___f_617_);
lean_ctor_set(v___x_606_, 0, v___x_625_);
v___x_627_ = v___x_606_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___f_617_);
v___x_627_ = v_reuseFailAlloc_632_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; lean_object* v___f_629_; lean_object* v___x_622__overap_630_; lean_object* v___x_631_; 
v___x_628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
lean_inc(v_mvarId_562_);
v___f_629_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_629_, 0, v_mvarId_562_);
lean_closure_set(v___f_629_, 1, v___x_628_);
lean_closure_set(v___f_629_, 2, v_mkName_564_);
lean_closure_set(v___f_629_, 3, v_n_563_);
lean_closure_set(v___f_629_, 4, v_s_565_);
lean_closure_set(v___f_629_, 5, v___f_615_);
v___x_622__overap_630_ = l_Lean_MVarId_withContext___redArg(v___x_589_, v___x_627_, v_mvarId_562_, v___f_629_);
lean_inc(v_a_569_);
lean_inc_ref(v_a_568_);
lean_inc(v_a_567_);
lean_inc_ref(v_a_566_);
v___x_631_ = lean_apply_5(v___x_622__overap_630_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, lean_box(0));
return v___x_631_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___boxed(lean_object* v_00_u03c3_638_, lean_object* v_mvarId_639_, lean_object* v_n_640_, lean_object* v_mkName_641_, lean_object* v_s_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(v_00_u03c3_638_, v_mvarId_639_, v_n_640_, v_mkName_641_, v_s_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(lean_object* v_name_649_, lean_object* v_decl_650_, lean_object* v_ref_651_){
_start:
{
lean_object* v_defValue_653_; lean_object* v_descr_654_; lean_object* v_deprecation_x3f_655_; lean_object* v___x_656_; uint8_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_defValue_653_ = lean_ctor_get(v_decl_650_, 0);
v_descr_654_ = lean_ctor_get(v_decl_650_, 1);
v_deprecation_x3f_655_ = lean_ctor_get(v_decl_650_, 2);
v___x_656_ = lean_alloc_ctor(1, 0, 1);
v___x_657_ = lean_unbox(v_defValue_653_);
lean_ctor_set_uint8(v___x_656_, 0, v___x_657_);
lean_inc(v_deprecation_x3f_655_);
lean_inc_ref(v_descr_654_);
lean_inc_n(v_name_649_, 2);
v___x_658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_658_, 0, v_name_649_);
lean_ctor_set(v___x_658_, 1, v_ref_651_);
lean_ctor_set(v___x_658_, 2, v___x_656_);
lean_ctor_set(v___x_658_, 3, v_descr_654_);
lean_ctor_set(v___x_658_, 4, v_deprecation_x3f_655_);
v___x_659_ = lean_register_option(v_name_649_, v___x_658_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_667_; 
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; 
v_unused_668_ = lean_ctor_get(v___x_659_, 0);
lean_dec(v_unused_668_);
v___x_661_ = v___x_659_;
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
else
{
lean_dec(v___x_659_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_665_; 
lean_inc(v_defValue_653_);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v_name_649_);
lean_ctor_set(v___x_663_, 1, v_defValue_653_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_663_);
v___x_665_ = v___x_661_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_663_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec(v_name_649_);
v_a_669_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_659_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_659_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_677_, lean_object* v_decl_678_, lean_object* v_ref_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(v_name_677_, v_decl_678_, v_ref_679_);
lean_dec_ref(v_decl_678_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_));
v___x_702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_));
v___x_703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_));
v___x_704_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(v___x_701_, v___x_702_, v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4____boxed(lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_();
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(lean_object* v_lctx_707_, lean_object* v_binderName_708_, uint8_t v_hygienic_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
if (v_hygienic_709_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = l_Lean_LocalContext_getUnusedName(v_lctx_707_, v_binderName_708_);
lean_dec(v_binderName_708_);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
else
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Core_mkFreshUserName(v_binderName_708_, v_a_710_, v_a_711_);
return v___x_715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg___boxed(lean_object* v_lctx_716_, lean_object* v_binderName_717_, lean_object* v_hygienic_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
uint8_t v_hygienic_boxed_722_; lean_object* v_res_723_; 
v_hygienic_boxed_722_ = lean_unbox(v_hygienic_718_);
v_res_723_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_716_, v_binderName_717_, v_hygienic_boxed_722_, v_a_719_, v_a_720_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec_ref(v_lctx_716_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore(lean_object* v_lctx_724_, lean_object* v_binderName_725_, uint8_t v_hygienic_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_724_, v_binderName_725_, v_hygienic_726_, v_a_729_, v_a_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore___boxed(lean_object* v_lctx_733_, lean_object* v_binderName_734_, lean_object* v_hygienic_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
uint8_t v_hygienic_boxed_741_; lean_object* v_res_742_; 
v_hygienic_boxed_741_ = lean_unbox(v_hygienic_735_);
v_res_742_ = l_Lean_Meta_mkFreshBinderNameForTacticCore(v_lctx_733_, v_binderName_734_, v_hygienic_boxed_741_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec_ref(v_lctx_733_);
return v_res_742_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(lean_object* v_opts_743_, lean_object* v_opt_744_){
_start:
{
lean_object* v_name_745_; lean_object* v_defValue_746_; lean_object* v_map_747_; lean_object* v___x_748_; 
v_name_745_ = lean_ctor_get(v_opt_744_, 0);
v_defValue_746_ = lean_ctor_get(v_opt_744_, 1);
v_map_747_ = lean_ctor_get(v_opts_743_, 0);
v___x_748_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_747_, v_name_745_);
if (lean_obj_tag(v___x_748_) == 0)
{
uint8_t v___x_749_; 
v___x_749_ = lean_unbox(v_defValue_746_);
return v___x_749_;
}
else
{
lean_object* v_val_750_; 
v_val_750_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_val_750_);
lean_dec_ref_known(v___x_748_, 1);
if (lean_obj_tag(v_val_750_) == 1)
{
uint8_t v_v_751_; 
v_v_751_ = lean_ctor_get_uint8(v_val_750_, 0);
lean_dec_ref_known(v_val_750_, 0);
return v_v_751_;
}
else
{
uint8_t v___x_752_; 
lean_dec(v_val_750_);
v___x_752_ = lean_unbox(v_defValue_746_);
return v___x_752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0___boxed(lean_object* v_opts_753_, lean_object* v_opt_754_){
_start:
{
uint8_t v_res_755_; lean_object* v_r_756_; 
v_res_755_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v_opts_753_, v_opt_754_);
lean_dec_ref(v_opt_754_);
lean_dec_ref(v_opts_753_);
v_r_756_ = lean_box(v_res_755_);
return v_r_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg(lean_object* v_binderName_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_lctx_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; lean_object* v___x_766_; 
v_lctx_762_ = lean_ctor_get(v_a_758_, 2);
v___x_763_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_759_);
v___x_764_ = l_Lean_Meta_tactic_hygienic;
v___x_765_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v___x_763_, v___x_764_);
lean_dec_ref(v___x_763_);
v___x_766_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_762_, v_binderName_757_, v___x_765_, v_a_759_, v_a_760_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg___boxed(lean_object* v_binderName_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_binderName_767_, v_a_768_, v_a_769_, v_a_770_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec_ref(v_a_768_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic(lean_object* v_binderName_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_binderName_773_, v_a_774_, v_a_776_, v_a_777_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___boxed(lean_object* v_binderName_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_Meta_mkFreshBinderNameForTactic(v_binderName_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(uint8_t v_preserveBinderNames_790_, uint8_t v_hygienic_791_, lean_object* v_lctx_792_, lean_object* v_binderName_793_, lean_object* v_rest_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_binderName_799_; lean_object* v___y_800_; lean_object* v___y_801_; uint8_t v___x_822_; 
v___x_822_ = l_Lean_Name_isAnonymous(v_binderName_793_);
if (v___x_822_ == 0)
{
v_binderName_799_ = v_binderName_793_;
v___y_800_ = v_a_795_;
v___y_801_ = v_a_796_;
goto v___jp_798_;
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec(v_binderName_793_);
v___x_823_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__1));
v___x_824_ = l_Lean_Core_mkFreshUserName(v___x_823_, v_a_795_, v_a_796_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_825_);
lean_dec_ref_known(v___x_824_, 1);
v_binderName_799_ = v_a_825_;
v___y_800_ = v_a_795_;
v___y_801_ = v_a_796_;
goto v___jp_798_;
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_rest_794_);
v_a_826_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_824_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_824_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
v___jp_798_:
{
if (v_preserveBinderNames_790_ == 0)
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_792_, v_binderName_799_, v_hygienic_791_, v___y_800_, v___y_801_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_811_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_811_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_a_803_);
lean_ctor_set(v___x_807_, 1, v_rest_794_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_807_);
v___x_809_ = v___x_805_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v_rest_794_);
v_a_812_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_802_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_802_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_binderName_799_);
lean_ctor_set(v___x_820_, 1, v_rest_794_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___boxed(lean_object* v_preserveBinderNames_834_, lean_object* v_hygienic_835_, lean_object* v_lctx_836_, lean_object* v_binderName_837_, lean_object* v_rest_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
uint8_t v_preserveBinderNames_boxed_842_; uint8_t v_hygienic_boxed_843_; lean_object* v_res_844_; 
v_preserveBinderNames_boxed_842_ = lean_unbox(v_preserveBinderNames_834_);
v_hygienic_boxed_843_ = lean_unbox(v_hygienic_835_);
v_res_844_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_boxed_842_, v_hygienic_boxed_843_, v_lctx_836_, v_binderName_837_, v_rest_838_, v_a_839_, v_a_840_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec_ref(v_lctx_836_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(uint8_t v_preserveBinderNames_845_, uint8_t v_hygienic_846_, lean_object* v_lctx_847_, lean_object* v_binderName_848_, lean_object* v_rest_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_845_, v_hygienic_846_, v_lctx_847_, v_binderName_848_, v_rest_849_, v_a_852_, v_a_853_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___boxed(lean_object* v_preserveBinderNames_856_, lean_object* v_hygienic_857_, lean_object* v_lctx_858_, lean_object* v_binderName_859_, lean_object* v_rest_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
uint8_t v_preserveBinderNames_boxed_866_; uint8_t v_hygienic_boxed_867_; lean_object* v_res_868_; 
v_preserveBinderNames_boxed_866_ = lean_unbox(v_preserveBinderNames_856_);
v_hygienic_boxed_867_ = lean_unbox(v_hygienic_857_);
v_res_868_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(v_preserveBinderNames_boxed_866_, v_hygienic_boxed_867_, v_lctx_858_, v_binderName_859_, v_rest_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
lean_dec(v_a_862_);
lean_dec_ref(v_a_861_);
lean_dec_ref(v_lctx_858_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(uint8_t v_preserveBinderNames_873_, uint8_t v_hygienic_874_, uint8_t v_useNamesForExplicitOnly_875_, lean_object* v_lctx_876_, lean_object* v_binderName_877_, uint8_t v_isExplicit_878_, lean_object* v_x_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
if (lean_obj_tag(v_x_879_) == 0)
{
lean_object* v___x_883_; 
v___x_883_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_873_, v_hygienic_874_, v_lctx_876_, v_binderName_877_, v_x_879_, v_a_880_, v_a_881_);
return v___x_883_;
}
else
{
lean_object* v_head_884_; lean_object* v_tail_885_; 
v_head_884_ = lean_ctor_get(v_x_879_, 0);
v_tail_885_ = lean_ctor_get(v_x_879_, 1);
if (v_useNamesForExplicitOnly_875_ == 0)
{
lean_inc(v_tail_885_);
lean_inc(v_head_884_);
lean_dec_ref_known(v_x_879_, 2);
goto v___jp_886_;
}
else
{
if (v_isExplicit_878_ == 0)
{
lean_object* v___x_892_; 
v___x_892_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_873_, v_hygienic_874_, v_lctx_876_, v_binderName_877_, v_x_879_, v_a_880_, v_a_881_);
return v___x_892_;
}
else
{
lean_inc(v_tail_885_);
lean_inc(v_head_884_);
lean_dec_ref_known(v_x_879_, 2);
goto v___jp_886_;
}
}
v___jp_886_:
{
lean_object* v___x_887_; uint8_t v___x_888_; 
v___x_887_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__1));
v___x_888_ = lean_name_eq(v_head_884_, v___x_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec(v_binderName_877_);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v_head_884_);
lean_ctor_set(v___x_889_, 1, v_tail_885_);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
else
{
lean_object* v___x_891_; 
lean_dec(v_head_884_);
v___x_891_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_873_, v_hygienic_874_, v_lctx_876_, v_binderName_877_, v_tail_885_, v_a_880_, v_a_881_);
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___boxed(lean_object* v_preserveBinderNames_893_, lean_object* v_hygienic_894_, lean_object* v_useNamesForExplicitOnly_895_, lean_object* v_lctx_896_, lean_object* v_binderName_897_, lean_object* v_isExplicit_898_, lean_object* v_x_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
uint8_t v_preserveBinderNames_boxed_903_; uint8_t v_hygienic_boxed_904_; uint8_t v_useNamesForExplicitOnly_boxed_905_; uint8_t v_isExplicit_boxed_906_; lean_object* v_res_907_; 
v_preserveBinderNames_boxed_903_ = lean_unbox(v_preserveBinderNames_893_);
v_hygienic_boxed_904_ = lean_unbox(v_hygienic_894_);
v_useNamesForExplicitOnly_boxed_905_ = lean_unbox(v_useNamesForExplicitOnly_895_);
v_isExplicit_boxed_906_ = lean_unbox(v_isExplicit_898_);
v_res_907_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_boxed_903_, v_hygienic_boxed_904_, v_useNamesForExplicitOnly_boxed_905_, v_lctx_896_, v_binderName_897_, v_isExplicit_boxed_906_, v_x_899_, v_a_900_, v_a_901_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec_ref(v_lctx_896_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(uint8_t v_preserveBinderNames_908_, uint8_t v_hygienic_909_, uint8_t v_useNamesForExplicitOnly_910_, lean_object* v_lctx_911_, lean_object* v_binderName_912_, uint8_t v_isExplicit_913_, lean_object* v_x_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_908_, v_hygienic_909_, v_useNamesForExplicitOnly_910_, v_lctx_911_, v_binderName_912_, v_isExplicit_913_, v_x_914_, v_a_917_, v_a_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___boxed(lean_object* v_preserveBinderNames_921_, lean_object* v_hygienic_922_, lean_object* v_useNamesForExplicitOnly_923_, lean_object* v_lctx_924_, lean_object* v_binderName_925_, lean_object* v_isExplicit_926_, lean_object* v_x_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
uint8_t v_preserveBinderNames_boxed_933_; uint8_t v_hygienic_boxed_934_; uint8_t v_useNamesForExplicitOnly_boxed_935_; uint8_t v_isExplicit_boxed_936_; lean_object* v_res_937_; 
v_preserveBinderNames_boxed_933_ = lean_unbox(v_preserveBinderNames_921_);
v_hygienic_boxed_934_ = lean_unbox(v_hygienic_922_);
v_useNamesForExplicitOnly_boxed_935_ = lean_unbox(v_useNamesForExplicitOnly_923_);
v_isExplicit_boxed_936_ = lean_unbox(v_isExplicit_926_);
v_res_937_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(v_preserveBinderNames_boxed_933_, v_hygienic_boxed_934_, v_useNamesForExplicitOnly_boxed_935_, v_lctx_924_, v_binderName_925_, v_isExplicit_boxed_936_, v_x_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec_ref(v_lctx_924_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(lean_object* v_mvarId_938_, lean_object* v_x_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_938_, v_x_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
v_a_954_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_945_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_945_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg___boxed(lean_object* v_mvarId_962_, lean_object* v_x_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_962_, v_x_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(lean_object* v_00_u03b1_970_, lean_object* v_mvarId_971_, lean_object* v_x_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_971_, v_x_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___boxed(lean_object* v_00_u03b1_979_, lean_object* v_mvarId_980_, lean_object* v_x_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(v_00_u03b1_979_, v_mvarId_980_, v_x_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(size_t v_sz_988_, size_t v_i_989_, lean_object* v_bs_990_){
_start:
{
uint8_t v___x_991_; 
v___x_991_ = lean_usize_dec_lt(v_i_989_, v_sz_988_);
if (v___x_991_ == 0)
{
return v_bs_990_;
}
else
{
lean_object* v_v_992_; lean_object* v___x_993_; lean_object* v_bs_x27_994_; lean_object* v___x_995_; size_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; 
v_v_992_ = lean_array_uget(v_bs_990_, v_i_989_);
v___x_993_ = lean_unsigned_to_nat(0u);
v_bs_x27_994_ = lean_array_uset(v_bs_990_, v_i_989_, v___x_993_);
v___x_995_ = l_Lean_Expr_fvarId_x21(v_v_992_);
lean_dec(v_v_992_);
v___x_996_ = ((size_t)1ULL);
v___x_997_ = lean_usize_add(v_i_989_, v___x_996_);
v___x_998_ = lean_array_uset(v_bs_x27_994_, v_i_989_, v___x_995_);
v_i_989_ = v___x_997_;
v_bs_990_ = v___x_998_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1___boxed(lean_object* v_sz_1000_, lean_object* v_i_1001_, lean_object* v_bs_1002_){
_start:
{
size_t v_sz_boxed_1003_; size_t v_i_boxed_1004_; lean_object* v_res_1005_; 
v_sz_boxed_1003_ = lean_unbox_usize(v_sz_1000_);
lean_dec(v_sz_1000_);
v_i_boxed_1004_ = lean_unbox_usize(v_i_1001_);
lean_dec(v_i_1001_);
v_res_1005_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(v_sz_boxed_1003_, v_i_boxed_1004_, v_bs_1002_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(lean_object* v_e_1006_, lean_object* v___y_1007_){
_start:
{
uint8_t v___x_1009_; 
v___x_1009_ = l_Lean_Expr_hasMVar(v_e_1006_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v_e_1006_);
return v___x_1010_;
}
else
{
lean_object* v___x_1011_; lean_object* v_mctx_1012_; lean_object* v___x_1013_; lean_object* v_fst_1014_; lean_object* v_snd_1015_; lean_object* v___x_1016_; lean_object* v_cache_1017_; lean_object* v_zetaDeltaFVarIds_1018_; lean_object* v_postponed_1019_; lean_object* v_diag_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1029_; 
v___x_1011_ = lean_st_ref_get(v___y_1007_);
v_mctx_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc_ref(v_mctx_1012_);
lean_dec(v___x_1011_);
v___x_1013_ = l_Lean_instantiateMVarsCore(v_mctx_1012_, v_e_1006_);
v_fst_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_fst_1014_);
v_snd_1015_ = lean_ctor_get(v___x_1013_, 1);
lean_inc(v_snd_1015_);
lean_dec_ref(v___x_1013_);
v___x_1016_ = lean_st_ref_take(v___y_1007_);
v_cache_1017_ = lean_ctor_get(v___x_1016_, 1);
v_zetaDeltaFVarIds_1018_ = lean_ctor_get(v___x_1016_, 2);
v_postponed_1019_ = lean_ctor_get(v___x_1016_, 3);
v_diag_1020_ = lean_ctor_get(v___x_1016_, 4);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v___x_1016_, 0);
lean_dec(v_unused_1030_);
v___x_1022_ = v___x_1016_;
v_isShared_1023_ = v_isSharedCheck_1029_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_diag_1020_);
lean_inc(v_postponed_1019_);
lean_inc(v_zetaDeltaFVarIds_1018_);
lean_inc(v_cache_1017_);
lean_dec(v___x_1016_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1029_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v_snd_1015_);
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_snd_1015_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_cache_1017_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_zetaDeltaFVarIds_1018_);
lean_ctor_set(v_reuseFailAlloc_1028_, 3, v_postponed_1019_);
lean_ctor_set(v_reuseFailAlloc_1028_, 4, v_diag_1020_);
v___x_1025_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_st_ref_put(v___y_1007_, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v_fst_1014_);
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg___boxed(lean_object* v_e_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_1031_, v___y_1032_);
lean_dec(v___y_1032_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; lean_object* v_ngen_1038_; lean_object* v_namePrefix_1039_; lean_object* v_idx_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1070_; 
v___x_1037_ = lean_st_ref_get(v___y_1035_);
v_ngen_1038_ = lean_ctor_get(v___x_1037_, 2);
lean_inc_ref(v_ngen_1038_);
lean_dec(v___x_1037_);
v_namePrefix_1039_ = lean_ctor_get(v_ngen_1038_, 0);
v_idx_1040_ = lean_ctor_get(v_ngen_1038_, 1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_ngen_1038_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1042_ = v_ngen_1038_;
v_isShared_1043_ = v_isSharedCheck_1070_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_idx_1040_);
lean_inc(v_namePrefix_1039_);
lean_dec(v_ngen_1038_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1070_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_r_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
lean_inc(v_idx_1040_);
lean_inc(v_namePrefix_1039_);
v_r_1044_ = l_Lean_Name_num___override(v_namePrefix_1039_, v_idx_1040_);
v___x_1045_ = lean_unsigned_to_nat(1u);
v___x_1046_ = lean_nat_add(v_idx_1040_, v___x_1045_);
lean_dec(v_idx_1040_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 1, v___x_1046_);
v___x_1048_ = v___x_1042_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_namePrefix_1039_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; lean_object* v_env_1050_; lean_object* v_nextMacroScope_1051_; lean_object* v_auxDeclNGen_1052_; lean_object* v_traceState_1053_; lean_object* v_cache_1054_; lean_object* v_recordedDeps_1055_; lean_object* v_messages_1056_; lean_object* v_infoState_1057_; lean_object* v_snapshotTasks_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1067_; 
v___x_1049_ = lean_st_ref_take(v___y_1035_);
v_env_1050_ = lean_ctor_get(v___x_1049_, 0);
v_nextMacroScope_1051_ = lean_ctor_get(v___x_1049_, 1);
v_auxDeclNGen_1052_ = lean_ctor_get(v___x_1049_, 3);
v_traceState_1053_ = lean_ctor_get(v___x_1049_, 4);
v_cache_1054_ = lean_ctor_get(v___x_1049_, 5);
v_recordedDeps_1055_ = lean_ctor_get(v___x_1049_, 6);
v_messages_1056_ = lean_ctor_get(v___x_1049_, 7);
v_infoState_1057_ = lean_ctor_get(v___x_1049_, 8);
v_snapshotTasks_1058_ = lean_ctor_get(v___x_1049_, 9);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v___x_1049_, 2);
lean_dec(v_unused_1068_);
v___x_1060_ = v___x_1049_;
v_isShared_1061_ = v_isSharedCheck_1067_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_snapshotTasks_1058_);
lean_inc(v_infoState_1057_);
lean_inc(v_messages_1056_);
lean_inc(v_recordedDeps_1055_);
lean_inc(v_cache_1054_);
lean_inc(v_traceState_1053_);
lean_inc(v_auxDeclNGen_1052_);
lean_inc(v_nextMacroScope_1051_);
lean_inc(v_env_1050_);
lean_dec(v___x_1049_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1067_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 2, v___x_1048_);
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_env_1050_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_nextMacroScope_1051_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1066_, 3, v_auxDeclNGen_1052_);
lean_ctor_set(v_reuseFailAlloc_1066_, 4, v_traceState_1053_);
lean_ctor_set(v_reuseFailAlloc_1066_, 5, v_cache_1054_);
lean_ctor_set(v_reuseFailAlloc_1066_, 6, v_recordedDeps_1055_);
lean_ctor_set(v_reuseFailAlloc_1066_, 7, v_messages_1056_);
lean_ctor_set(v_reuseFailAlloc_1066_, 8, v_infoState_1057_);
lean_ctor_set(v_reuseFailAlloc_1066_, 9, v_snapshotTasks_1058_);
v___x_1063_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_st_ref_put(v___y_1035_, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_r_1044_);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_1218_, size_t v_x_1219_, size_t v_x_1220_, lean_object* v_x_1221_, lean_object* v_x_1222_){
_start:
{
if (lean_obj_tag(v_x_1218_) == 0)
{
lean_object* v_es_1223_; size_t v___x_1224_; size_t v___x_1225_; lean_object* v_j_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v_es_1223_ = lean_ctor_get(v_x_1218_, 0);
v___x_1224_ = ((size_t)31ULL);
v___x_1225_ = lean_usize_land(v_x_1219_, v___x_1224_);
v_j_1226_ = lean_usize_to_nat(v___x_1225_);
v___x_1227_ = lean_array_get_size(v_es_1223_);
v___x_1228_ = lean_nat_dec_lt(v_j_1226_, v___x_1227_);
if (v___x_1228_ == 0)
{
lean_dec(v_j_1226_);
lean_dec(v_x_1222_);
lean_dec(v_x_1221_);
return v_x_1218_;
}
else
{
lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1267_; 
lean_inc_ref(v_es_1223_);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_x_1218_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; 
v_unused_1268_ = lean_ctor_get(v_x_1218_, 0);
lean_dec(v_unused_1268_);
v___x_1230_ = v_x_1218_;
v_isShared_1231_ = v_isSharedCheck_1267_;
goto v_resetjp_1229_;
}
else
{
lean_dec(v_x_1218_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1267_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v_v_1232_; lean_object* v___x_1233_; lean_object* v_xs_x27_1234_; lean_object* v___y_1236_; 
v_v_1232_ = lean_array_fget(v_es_1223_, v_j_1226_);
v___x_1233_ = lean_box(0);
v_xs_x27_1234_ = lean_array_fset(v_es_1223_, v_j_1226_, v___x_1233_);
switch(lean_obj_tag(v_v_1232_))
{
case 0:
{
lean_object* v_key_1241_; lean_object* v_val_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1252_; 
v_key_1241_ = lean_ctor_get(v_v_1232_, 0);
v_val_1242_ = lean_ctor_get(v_v_1232_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_v_1232_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1244_ = v_v_1232_;
v_isShared_1245_ = v_isSharedCheck_1252_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_val_1242_);
lean_inc(v_key_1241_);
lean_dec(v_v_1232_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1252_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
uint8_t v___x_1246_; 
v___x_1246_ = l_Lean_instBEqMVarId_beq(v_x_1221_, v_key_1241_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_del_object(v___x_1244_);
v___x_1247_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1241_, v_val_1242_, v_x_1221_, v_x_1222_);
v___x_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
v___y_1236_ = v___x_1248_;
goto v___jp_1235_;
}
else
{
lean_object* v___x_1250_; 
lean_dec(v_val_1242_);
lean_dec(v_key_1241_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v_x_1222_);
lean_ctor_set(v___x_1244_, 0, v_x_1221_);
v___x_1250_ = v___x_1244_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_x_1221_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_x_1222_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
v___y_1236_ = v___x_1250_;
goto v___jp_1235_;
}
}
}
}
case 1:
{
lean_object* v_node_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1265_; 
v_node_1253_ = lean_ctor_get(v_v_1232_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_v_1232_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1255_ = v_v_1232_;
v_isShared_1256_ = v_isSharedCheck_1265_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_node_1253_);
lean_dec(v_v_1232_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1265_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
size_t v___x_1257_; size_t v___x_1258_; size_t v___x_1259_; size_t v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1257_ = ((size_t)5ULL);
v___x_1258_ = lean_usize_shift_right(v_x_1219_, v___x_1257_);
v___x_1259_ = ((size_t)1ULL);
v___x_1260_ = lean_usize_add(v_x_1220_, v___x_1259_);
v___x_1261_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_node_1253_, v___x_1258_, v___x_1260_, v_x_1221_, v_x_1222_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1261_);
v___x_1263_ = v___x_1255_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
v___y_1236_ = v___x_1263_;
goto v___jp_1235_;
}
}
}
default: 
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v_x_1221_);
lean_ctor_set(v___x_1266_, 1, v_x_1222_);
v___y_1236_ = v___x_1266_;
goto v___jp_1235_;
}
}
v___jp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1237_ = lean_array_fset(v_xs_x27_1234_, v_j_1226_, v___y_1236_);
lean_dec(v_j_1226_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v___x_1237_);
v___x_1239_ = v___x_1230_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
else
{
lean_object* v_ks_1269_; lean_object* v_vs_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1288_; 
v_ks_1269_ = lean_ctor_get(v_x_1218_, 0);
v_vs_1270_ = lean_ctor_get(v_x_1218_, 1);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_x_1218_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1272_ = v_x_1218_;
v_isShared_1273_ = v_isSharedCheck_1288_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_vs_1270_);
lean_inc(v_ks_1269_);
lean_dec(v_x_1218_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1288_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_ks_1269_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_vs_1270_);
v___x_1275_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v_newNode_1276_; size_t v___x_1277_; uint8_t v___x_1278_; 
v_newNode_1276_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(v___x_1275_, v_x_1221_, v_x_1222_);
v___x_1277_ = ((size_t)7ULL);
v___x_1278_ = lean_usize_dec_le(v___x_1277_, v_x_1220_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1279_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1276_);
v___x_1280_ = lean_unsigned_to_nat(4u);
v___x_1281_ = lean_nat_dec_lt(v___x_1279_, v___x_1280_);
lean_dec(v___x_1279_);
if (v___x_1281_ == 0)
{
lean_object* v_ks_1282_; lean_object* v_vs_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_ks_1282_ = lean_ctor_get(v_newNode_1276_, 0);
lean_inc_ref(v_ks_1282_);
v_vs_1283_ = lean_ctor_get(v_newNode_1276_, 1);
lean_inc_ref(v_vs_1283_);
lean_dec_ref(v_newNode_1276_);
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0);
v___x_1286_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_x_1220_, v_ks_1282_, v_vs_1283_, v___x_1284_, v___x_1285_);
lean_dec_ref(v_vs_1283_);
lean_dec_ref(v_ks_1282_);
return v___x_1286_;
}
else
{
return v_newNode_1276_;
}
}
else
{
return v_newNode_1276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(size_t v_depth_1289_, lean_object* v_keys_1290_, lean_object* v_vals_1291_, lean_object* v_i_1292_, lean_object* v_entries_1293_){
_start:
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = lean_array_get_size(v_keys_1290_);
v___x_1295_ = lean_nat_dec_lt(v_i_1292_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_dec(v_i_1292_);
return v_entries_1293_;
}
else
{
lean_object* v_k_1296_; lean_object* v_v_1297_; uint64_t v___x_1298_; size_t v_h_1299_; size_t v___x_1300_; lean_object* v___x_1301_; size_t v___x_1302_; size_t v___x_1303_; size_t v___x_1304_; size_t v_h_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_k_1296_ = lean_array_fget_borrowed(v_keys_1290_, v_i_1292_);
v_v_1297_ = lean_array_fget_borrowed(v_vals_1291_, v_i_1292_);
v___x_1298_ = l_Lean_instHashableMVarId_hash(v_k_1296_);
v_h_1299_ = lean_uint64_to_usize(v___x_1298_);
v___x_1300_ = ((size_t)5ULL);
v___x_1301_ = lean_unsigned_to_nat(1u);
v___x_1302_ = ((size_t)1ULL);
v___x_1303_ = lean_usize_sub(v_depth_1289_, v___x_1302_);
v___x_1304_ = lean_usize_mul(v___x_1300_, v___x_1303_);
v_h_1305_ = lean_usize_shift_right(v_h_1299_, v___x_1304_);
v___x_1306_ = lean_nat_add(v_i_1292_, v___x_1301_);
lean_dec(v_i_1292_);
lean_inc(v_v_1297_);
lean_inc(v_k_1296_);
v___x_1307_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_entries_1293_, v_h_1305_, v_depth_1289_, v_k_1296_, v_v_1297_);
v_i_1292_ = v___x_1306_;
v_entries_1293_ = v___x_1307_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_depth_1309_, lean_object* v_keys_1310_, lean_object* v_vals_1311_, lean_object* v_i_1312_, lean_object* v_entries_1313_){
_start:
{
size_t v_depth_boxed_1314_; lean_object* v_res_1315_; 
v_depth_boxed_1314_ = lean_unbox_usize(v_depth_1309_);
lean_dec(v_depth_1309_);
v_res_1315_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_boxed_1314_, v_keys_1310_, v_vals_1311_, v_i_1312_, v_entries_1313_);
lean_dec_ref(v_vals_1311_);
lean_dec_ref(v_keys_1310_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_x_1316_, lean_object* v_x_1317_, lean_object* v_x_1318_, lean_object* v_x_1319_, lean_object* v_x_1320_){
_start:
{
size_t v_x_3879__boxed_1321_; size_t v_x_3880__boxed_1322_; lean_object* v_res_1323_; 
v_x_3879__boxed_1321_ = lean_unbox_usize(v_x_1317_);
lean_dec(v_x_1317_);
v_x_3880__boxed_1322_ = lean_unbox_usize(v_x_1318_);
lean_dec(v_x_1318_);
v_res_1323_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1316_, v_x_3879__boxed_1321_, v_x_3880__boxed_1322_, v_x_1319_, v_x_1320_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_){
_start:
{
uint64_t v___x_1327_; size_t v___x_1328_; size_t v___x_1329_; lean_object* v___x_1330_; 
v___x_1327_ = l_Lean_instHashableMVarId_hash(v_x_1325_);
v___x_1328_ = lean_uint64_to_usize(v___x_1327_);
v___x_1329_ = ((size_t)1ULL);
v___x_1330_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1324_, v___x_1328_, v___x_1329_, v_x_1325_, v_x_1326_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(lean_object* v_mvarId_1331_, lean_object* v_val_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; lean_object* v_mctx_1336_; lean_object* v_cache_1337_; lean_object* v_zetaDeltaFVarIds_1338_; lean_object* v_postponed_1339_; lean_object* v_diag_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1370_; 
v___x_1335_ = lean_st_ref_take(v___y_1333_);
v_mctx_1336_ = lean_ctor_get(v___x_1335_, 0);
v_cache_1337_ = lean_ctor_get(v___x_1335_, 1);
v_zetaDeltaFVarIds_1338_ = lean_ctor_get(v___x_1335_, 2);
v_postponed_1339_ = lean_ctor_get(v___x_1335_, 3);
v_diag_1340_ = lean_ctor_get(v___x_1335_, 4);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1342_ = v___x_1335_;
v_isShared_1343_ = v_isSharedCheck_1370_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_diag_1340_);
lean_inc(v_postponed_1339_);
lean_inc(v_zetaDeltaFVarIds_1338_);
lean_inc(v_cache_1337_);
lean_inc(v_mctx_1336_);
lean_dec(v___x_1335_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1370_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_depth_1344_; lean_object* v_levelAssignDepth_1345_; lean_object* v_lmvarCounter_1346_; lean_object* v_mvarCounter_1347_; lean_object* v_lDecls_1348_; lean_object* v_decls_1349_; lean_object* v_userNames_1350_; lean_object* v_lAssignment_1351_; lean_object* v_eAssignment_1352_; lean_object* v_dAssignment_1353_; lean_object* v_instanceTypedMVars_1354_; lean_object* v_synthNormMemo_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1369_; 
v_depth_1344_ = lean_ctor_get(v_mctx_1336_, 0);
v_levelAssignDepth_1345_ = lean_ctor_get(v_mctx_1336_, 1);
v_lmvarCounter_1346_ = lean_ctor_get(v_mctx_1336_, 2);
v_mvarCounter_1347_ = lean_ctor_get(v_mctx_1336_, 3);
v_lDecls_1348_ = lean_ctor_get(v_mctx_1336_, 4);
v_decls_1349_ = lean_ctor_get(v_mctx_1336_, 5);
v_userNames_1350_ = lean_ctor_get(v_mctx_1336_, 6);
v_lAssignment_1351_ = lean_ctor_get(v_mctx_1336_, 7);
v_eAssignment_1352_ = lean_ctor_get(v_mctx_1336_, 8);
v_dAssignment_1353_ = lean_ctor_get(v_mctx_1336_, 9);
v_instanceTypedMVars_1354_ = lean_ctor_get(v_mctx_1336_, 10);
v_synthNormMemo_1355_ = lean_ctor_get(v_mctx_1336_, 11);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_mctx_1336_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1357_ = v_mctx_1336_;
v_isShared_1358_ = v_isSharedCheck_1369_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_synthNormMemo_1355_);
lean_inc(v_instanceTypedMVars_1354_);
lean_inc(v_dAssignment_1353_);
lean_inc(v_eAssignment_1352_);
lean_inc(v_lAssignment_1351_);
lean_inc(v_userNames_1350_);
lean_inc(v_decls_1349_);
lean_inc(v_lDecls_1348_);
lean_inc(v_mvarCounter_1347_);
lean_inc(v_lmvarCounter_1346_);
lean_inc(v_levelAssignDepth_1345_);
lean_inc(v_depth_1344_);
lean_dec(v_mctx_1336_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1369_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1359_ = lean_box(0);
v___x_1360_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(v_eAssignment_1352_, v_mvarId_1331_, v_val_1332_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 8, v___x_1360_);
v___x_1362_ = v___x_1357_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_depth_1344_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_levelAssignDepth_1345_);
lean_ctor_set(v_reuseFailAlloc_1368_, 2, v_lmvarCounter_1346_);
lean_ctor_set(v_reuseFailAlloc_1368_, 3, v_mvarCounter_1347_);
lean_ctor_set(v_reuseFailAlloc_1368_, 4, v_lDecls_1348_);
lean_ctor_set(v_reuseFailAlloc_1368_, 5, v_decls_1349_);
lean_ctor_set(v_reuseFailAlloc_1368_, 6, v_userNames_1350_);
lean_ctor_set(v_reuseFailAlloc_1368_, 7, v_lAssignment_1351_);
lean_ctor_set(v_reuseFailAlloc_1368_, 8, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1368_, 9, v_dAssignment_1353_);
lean_ctor_set(v_reuseFailAlloc_1368_, 10, v_instanceTypedMVars_1354_);
lean_ctor_set(v_reuseFailAlloc_1368_, 11, v_synthNormMemo_1355_);
v___x_1362_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1364_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1362_);
v___x_1364_ = v___x_1342_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_cache_1337_);
lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_zetaDeltaFVarIds_1338_);
lean_ctor_set(v_reuseFailAlloc_1367_, 3, v_postponed_1339_);
lean_ctor_set(v_reuseFailAlloc_1367_, 4, v_diag_1340_);
v___x_1364_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = lean_st_ref_put(v___y_1333_, v___x_1364_);
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1359_);
return v___x_1366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg___boxed(lean_object* v_mvarId_1371_, lean_object* v_val_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1371_, v_val_1372_, v___y_1373_);
lean_dec(v___y_1373_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(lean_object* v_mvarId_1376_, lean_object* v_type_1377_, lean_object* v_fvars_1378_, uint8_t v_isZero_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v___x_1385_; 
lean_inc(v_mvarId_1376_);
v___x_1385_ = l_Lean_MVarId_getTag(v_mvarId_1376_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref_known(v___x_1385_, 1);
v___x_1387_ = l_Lean_Expr_headBeta(v_type_1377_);
v___x_1388_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1387_, v_a_1386_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; uint8_t v___x_1390_; uint8_t v___x_1391_; lean_object* v___x_1392_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc_n(v_a_1389_, 2);
lean_dec_ref_known(v___x_1388_, 1);
v___x_1390_ = 0;
v___x_1391_ = 1;
v___x_1392_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1378_, v_a_1389_, v___x_1390_, v_isZero_1379_, v___x_1390_, v_isZero_1379_, v___x_1391_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1394_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1392_, 1);
v___x_1394_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1376_, v_a_1393_, v___y_1381_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1403_; 
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; 
v_unused_1404_ = lean_ctor_get(v___x_1394_, 0);
lean_dec(v_unused_1404_);
v___x_1396_ = v___x_1394_;
v_isShared_1397_ = v_isSharedCheck_1403_;
goto v_resetjp_1395_;
}
else
{
lean_dec(v___x_1394_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1403_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1398_ = l_Lean_Expr_mvarId_x21(v_a_1389_);
lean_dec(v_a_1389_);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v_fvars_1378_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v___x_1399_);
v___x_1401_ = v___x_1396_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec(v_a_1389_);
lean_dec_ref(v_fvars_1378_);
v_a_1405_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1394_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1394_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec(v_a_1389_);
lean_dec_ref(v_fvars_1378_);
lean_dec(v_mvarId_1376_);
v_a_1413_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1392_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1392_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec_ref(v_fvars_1378_);
lean_dec(v_mvarId_1376_);
v_a_1421_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1388_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1388_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec_ref(v_fvars_1378_);
lean_dec_ref(v_type_1377_);
lean_dec(v_mvarId_1376_);
v_a_1429_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1385_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1385_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0___boxed(lean_object* v_mvarId_1437_, lean_object* v_type_1438_, lean_object* v_fvars_1439_, lean_object* v_isZero_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
uint8_t v_isZero_boxed_1446_; lean_object* v_res_1447_; 
v_isZero_boxed_1446_ = lean_unbox(v_isZero_1440_);
v_res_1447_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(v_mvarId_1437_, v_type_1438_, v_fvars_1439_, v_isZero_boxed_1446_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(lean_object* v_lctx_1448_, lean_object* v_x_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_keyedConfig_1455_; uint8_t v_trackZetaDelta_1456_; lean_object* v_zetaDeltaSet_1457_; lean_object* v_localInstances_1458_; lean_object* v_defEqCtx_x3f_1459_; lean_object* v_synthPendingDepth_1460_; lean_object* v_customCanUnfoldPredicate_x3f_1461_; uint8_t v_univApprox_1462_; uint8_t v_inTypeClassResolution_1463_; uint8_t v_cacheInferType_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v_keyedConfig_1455_ = lean_ctor_get(v___y_1450_, 0);
v_trackZetaDelta_1456_ = lean_ctor_get_uint8(v___y_1450_, sizeof(void*)*7);
v_zetaDeltaSet_1457_ = lean_ctor_get(v___y_1450_, 1);
v_localInstances_1458_ = lean_ctor_get(v___y_1450_, 3);
v_defEqCtx_x3f_1459_ = lean_ctor_get(v___y_1450_, 4);
v_synthPendingDepth_1460_ = lean_ctor_get(v___y_1450_, 5);
v_customCanUnfoldPredicate_x3f_1461_ = lean_ctor_get(v___y_1450_, 6);
v_univApprox_1462_ = lean_ctor_get_uint8(v___y_1450_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1463_ = lean_ctor_get_uint8(v___y_1450_, sizeof(void*)*7 + 2);
v_cacheInferType_1464_ = lean_ctor_get_uint8(v___y_1450_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_1461_);
lean_inc(v_synthPendingDepth_1460_);
lean_inc(v_defEqCtx_x3f_1459_);
lean_inc_ref(v_localInstances_1458_);
lean_inc(v_zetaDeltaSet_1457_);
lean_inc_ref(v_keyedConfig_1455_);
v___x_1465_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1465_, 0, v_keyedConfig_1455_);
lean_ctor_set(v___x_1465_, 1, v_zetaDeltaSet_1457_);
lean_ctor_set(v___x_1465_, 2, v_lctx_1448_);
lean_ctor_set(v___x_1465_, 3, v_localInstances_1458_);
lean_ctor_set(v___x_1465_, 4, v_defEqCtx_x3f_1459_);
lean_ctor_set(v___x_1465_, 5, v_synthPendingDepth_1460_);
lean_ctor_set(v___x_1465_, 6, v_customCanUnfoldPredicate_x3f_1461_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*7, v_trackZetaDelta_1456_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*7 + 1, v_univApprox_1462_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1463_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*7 + 3, v_cacheInferType_1464_);
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc(v___y_1451_);
v___x_1466_ = lean_apply_5(v_x_1449_, v___x_1465_, v___y_1451_, v___y_1452_, v___y_1453_, lean_box(0));
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg___boxed(lean_object* v_lctx_1467_, lean_object* v_x_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1467_, v_x_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed(lean_object* v_type_1475_, lean_object* v_n_1476_, lean_object* v_preserveBinderNames_1477_, lean_object* v___x_1478_, lean_object* v_useNamesForExplicitOnly_1479_, lean_object* v_mvarId_1480_, lean_object* v_lctx_1481_, lean_object* v_fvars_1482_, lean_object* v___x_1483_, lean_object* v_s_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1490_; uint8_t v___x_4236__boxed_1491_; uint8_t v_useNamesForExplicitOnly_boxed_1492_; lean_object* v_res_1493_; 
v_preserveBinderNames_boxed_1490_ = lean_unbox(v_preserveBinderNames_1477_);
v___x_4236__boxed_1491_ = lean_unbox(v___x_1478_);
v_useNamesForExplicitOnly_boxed_1492_ = lean_unbox(v_useNamesForExplicitOnly_1479_);
v_res_1493_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(v_type_1475_, v_n_1476_, v_preserveBinderNames_boxed_1490_, v___x_4236__boxed_1491_, v_useNamesForExplicitOnly_boxed_1492_, v_mvarId_1480_, v_lctx_1481_, v_fvars_1482_, v___x_1483_, v_s_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v_n_1476_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(uint8_t v_preserveBinderNames_1494_, uint8_t v___x_1495_, uint8_t v_useNamesForExplicitOnly_1496_, lean_object* v_mvarId_1497_, lean_object* v_i_1498_, lean_object* v_lctx_1499_, lean_object* v_fvars_1500_, lean_object* v_j_1501_, lean_object* v_s_1502_, lean_object* v_type_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v_zero_1509_; uint8_t v_isZero_1510_; 
v_zero_1509_ = lean_unsigned_to_nat(0u);
v_isZero_1510_ = lean_nat_dec_eq(v_i_1498_, v_zero_1509_);
if (v_isZero_1510_ == 1)
{
lean_object* v___x_1511_; lean_object* v_type_1512_; lean_object* v___x_1513_; lean_object* v___f_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_dec(v_s_1502_);
lean_dec(v_i_1498_);
v___x_1511_ = lean_array_get_size(v_fvars_1500_);
v_type_1512_ = lean_expr_instantiate_rev_range(v_type_1503_, v_j_1501_, v___x_1511_, v_fvars_1500_);
lean_dec_ref(v_type_1503_);
v___x_1513_ = lean_box(v_isZero_1510_);
lean_inc_ref(v_fvars_1500_);
v___f_1514_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1514_, 0, v_mvarId_1497_);
lean_closure_set(v___f_1514_, 1, v_type_1512_);
lean_closure_set(v___f_1514_, 2, v_fvars_1500_);
lean_closure_set(v___f_1514_, 3, v___x_1513_);
v___x_1515_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed), 9, 4);
lean_closure_set(v___x_1515_, 0, lean_box(0));
lean_closure_set(v___x_1515_, 1, v_fvars_1500_);
lean_closure_set(v___x_1515_, 2, v_j_1501_);
lean_closure_set(v___x_1515_, 3, v___f_1514_);
v___x_1516_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1499_, v___x_1515_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
return v___x_1516_;
}
else
{
lean_object* v_one_1517_; lean_object* v_n_1518_; 
v_one_1517_ = lean_unsigned_to_nat(1u);
v_n_1518_ = lean_nat_sub(v_i_1498_, v_one_1517_);
lean_dec(v_i_1498_);
switch(lean_obj_tag(v_type_1503_))
{
case 8:
{
lean_object* v_declName_1519_; lean_object* v_type_1520_; lean_object* v_value_1521_; lean_object* v_body_1522_; lean_object* v___x_1523_; lean_object* v_type_1524_; lean_object* v_type_1525_; lean_object* v_val_1526_; lean_object* v___x_1527_; 
v_declName_1519_ = lean_ctor_get(v_type_1503_, 0);
lean_inc(v_declName_1519_);
v_type_1520_ = lean_ctor_get(v_type_1503_, 1);
lean_inc_ref(v_type_1520_);
v_value_1521_ = lean_ctor_get(v_type_1503_, 2);
lean_inc_ref(v_value_1521_);
v_body_1522_ = lean_ctor_get(v_type_1503_, 3);
lean_inc_ref(v_body_1522_);
lean_dec_ref_known(v_type_1503_, 4);
v___x_1523_ = lean_array_get_size(v_fvars_1500_);
v_type_1524_ = lean_expr_instantiate_rev_range(v_type_1520_, v_j_1501_, v___x_1523_, v_fvars_1500_);
lean_dec_ref(v_type_1520_);
v_type_1525_ = l_Lean_Expr_headBeta(v_type_1524_);
v_val_1526_ = lean_expr_instantiate_rev_range(v_value_1521_, v_j_1501_, v___x_1523_, v_fvars_1500_);
lean_dec_ref(v_value_1521_);
v___x_1527_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; uint8_t v___x_1529_; lean_object* v___x_1530_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___x_1527_, 1);
v___x_1529_ = 1;
v___x_1530_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_1494_, v___x_1495_, v_useNamesForExplicitOnly_1496_, v_lctx_1499_, v_declName_1519_, v___x_1529_, v_s_1502_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v_fst_1532_; lean_object* v_snd_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v_fst_1532_ = lean_ctor_get(v_a_1531_, 0);
lean_inc(v_fst_1532_);
v_snd_1533_ = lean_ctor_get(v_a_1531_, 1);
lean_inc(v_snd_1533_);
lean_dec(v_a_1531_);
v___x_1534_ = 0;
lean_inc(v_a_1528_);
v___x_1535_ = l_Lean_LocalContext_mkLetDecl(v_lctx_1499_, v_a_1528_, v_fst_1532_, v_type_1525_, v_val_1526_, v_isZero_1510_, v___x_1534_);
v___x_1536_ = l_Lean_mkFVar(v_a_1528_);
v___x_1537_ = lean_array_push(v_fvars_1500_, v___x_1536_);
v_i_1498_ = v_n_1518_;
v_lctx_1499_ = v___x_1535_;
v_fvars_1500_ = v___x_1537_;
v_s_1502_ = v_snd_1533_;
v_type_1503_ = v_body_1522_;
goto _start;
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec(v_a_1528_);
lean_dec_ref(v_val_1526_);
lean_dec_ref(v_type_1525_);
lean_dec_ref(v_body_1522_);
lean_dec(v_n_1518_);
lean_dec(v_j_1501_);
lean_dec_ref(v_fvars_1500_);
lean_dec_ref(v_lctx_1499_);
lean_dec(v_mvarId_1497_);
v_a_1539_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1530_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1530_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec_ref(v_val_1526_);
lean_dec_ref(v_type_1525_);
lean_dec_ref(v_body_1522_);
lean_dec(v_declName_1519_);
lean_dec(v_n_1518_);
lean_dec(v_s_1502_);
lean_dec(v_j_1501_);
lean_dec_ref(v_fvars_1500_);
lean_dec_ref(v_lctx_1499_);
lean_dec(v_mvarId_1497_);
v_a_1547_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1527_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1527_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1555_; lean_object* v_binderType_1556_; lean_object* v_body_1557_; uint8_t v_binderInfo_1558_; lean_object* v___x_1559_; lean_object* v_type_1560_; lean_object* v_type_1561_; lean_object* v___x_1562_; 
v_binderName_1555_ = lean_ctor_get(v_type_1503_, 0);
lean_inc(v_binderName_1555_);
v_binderType_1556_ = lean_ctor_get(v_type_1503_, 1);
lean_inc_ref(v_binderType_1556_);
v_body_1557_ = lean_ctor_get(v_type_1503_, 2);
lean_inc_ref(v_body_1557_);
v_binderInfo_1558_ = lean_ctor_get_uint8(v_type_1503_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_1503_, 3);
v___x_1559_ = lean_array_get_size(v_fvars_1500_);
v_type_1560_ = lean_expr_instantiate_rev_range(v_binderType_1556_, v_j_1501_, v___x_1559_, v_fvars_1500_);
lean_dec_ref(v_binderType_1556_);
v_type_1561_ = l_Lean_Expr_headBeta(v_type_1560_);
v___x_1562_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1562_, 1);
v___x_1564_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_1558_);
v___x_1565_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_1494_, v___x_1495_, v_useNamesForExplicitOnly_1496_, v_lctx_1499_, v_binderName_1555_, v___x_1564_, v_s_1502_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v_fst_1567_; lean_object* v_snd_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v_fst_1567_ = lean_ctor_get(v_a_1566_, 0);
lean_inc(v_fst_1567_);
v_snd_1568_ = lean_ctor_get(v_a_1566_, 1);
lean_inc(v_snd_1568_);
lean_dec(v_a_1566_);
v___x_1569_ = 0;
lean_inc(v_a_1563_);
v___x_1570_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_1499_, v_a_1563_, v_fst_1567_, v_type_1561_, v_binderInfo_1558_, v___x_1569_);
v___x_1571_ = l_Lean_mkFVar(v_a_1563_);
v___x_1572_ = lean_array_push(v_fvars_1500_, v___x_1571_);
v_i_1498_ = v_n_1518_;
v_lctx_1499_ = v___x_1570_;
v_fvars_1500_ = v___x_1572_;
v_s_1502_ = v_snd_1568_;
v_type_1503_ = v_body_1557_;
goto _start;
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec(v_a_1563_);
lean_dec_ref(v_type_1561_);
lean_dec_ref(v_body_1557_);
lean_dec(v_n_1518_);
lean_dec(v_j_1501_);
lean_dec_ref(v_fvars_1500_);
lean_dec_ref(v_lctx_1499_);
lean_dec(v_mvarId_1497_);
v_a_1574_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1565_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1565_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v_type_1561_);
lean_dec_ref(v_body_1557_);
lean_dec(v_binderName_1555_);
lean_dec(v_n_1518_);
lean_dec(v_s_1502_);
lean_dec(v_j_1501_);
lean_dec_ref(v_fvars_1500_);
lean_dec_ref(v_lctx_1499_);
lean_dec(v_mvarId_1497_);
v_a_1582_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1562_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1562_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
default: 
{
lean_object* v___x_1590_; lean_object* v_type_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___f_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1590_ = lean_array_get_size(v_fvars_1500_);
v_type_1591_ = lean_expr_instantiate_rev_range(v_type_1503_, v_j_1501_, v___x_1590_, v_fvars_1500_);
lean_dec_ref(v_type_1503_);
v___x_1592_ = lean_box(v_preserveBinderNames_1494_);
v___x_1593_ = lean_box(v___x_1495_);
v___x_1594_ = lean_box(v_useNamesForExplicitOnly_1496_);
lean_inc_ref(v_fvars_1500_);
lean_inc_ref(v_lctx_1499_);
v___f_1595_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed), 15, 10);
lean_closure_set(v___f_1595_, 0, v_type_1591_);
lean_closure_set(v___f_1595_, 1, v_n_1518_);
lean_closure_set(v___f_1595_, 2, v___x_1592_);
lean_closure_set(v___f_1595_, 3, v___x_1593_);
lean_closure_set(v___f_1595_, 4, v___x_1594_);
lean_closure_set(v___f_1595_, 5, v_mvarId_1497_);
lean_closure_set(v___f_1595_, 6, v_lctx_1499_);
lean_closure_set(v___f_1595_, 7, v_fvars_1500_);
lean_closure_set(v___f_1595_, 8, v___x_1590_);
lean_closure_set(v___f_1595_, 9, v_s_1502_);
v___x_1596_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed), 9, 4);
lean_closure_set(v___x_1596_, 0, lean_box(0));
lean_closure_set(v___x_1596_, 1, v_fvars_1500_);
lean_closure_set(v___x_1596_, 2, v_j_1501_);
lean_closure_set(v___x_1596_, 3, v___f_1595_);
v___x_1597_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1499_, v___x_1596_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
return v___x_1597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(lean_object* v_type_1598_, lean_object* v_n_1599_, uint8_t v_preserveBinderNames_1600_, uint8_t v___x_1601_, uint8_t v_useNamesForExplicitOnly_1602_, lean_object* v_mvarId_1603_, lean_object* v_lctx_1604_, lean_object* v_fvars_1605_, lean_object* v___x_1606_, lean_object* v_s_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_type_1598_, v___y_1609_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1615_; uint8_t v___x_1620_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
v___x_1615_ = l_Lean_Expr_cleanupAnnotations(v_a_1614_);
v___x_1620_ = l_Lean_Expr_isForall(v___x_1615_);
if (v___x_1620_ == 0)
{
uint8_t v___x_1621_; 
v___x_1621_ = l_Lean_Expr_isLet(v___x_1615_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; 
lean_inc(v___y_1611_);
lean_inc_ref(v___y_1610_);
lean_inc(v___y_1609_);
lean_inc_ref(v___y_1608_);
v___x_1622_ = lean_whnf(v___x_1615_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; uint8_t v___x_1624_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1622_, 1);
v___x_1624_ = l_Lean_Expr_isForall(v_a_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec(v_a_1623_);
lean_dec(v_s_1607_);
lean_dec(v___x_1606_);
lean_dec_ref(v_fvars_1605_);
lean_dec_ref(v_lctx_1604_);
v___x_1625_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
v___x_1626_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4);
v___x_1627_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1625_, v_mvarId_1603_, v___x_1626_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
return v___x_1627_;
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = lean_unsigned_to_nat(1u);
v___x_1629_ = lean_nat_add(v_n_1599_, v___x_1628_);
v___x_1630_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1600_, v___x_1601_, v_useNamesForExplicitOnly_1602_, v_mvarId_1603_, v___x_1629_, v_lctx_1604_, v_fvars_1605_, v___x_1606_, v_s_1607_, v_a_1623_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
return v___x_1630_;
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v_s_1607_);
lean_dec(v___x_1606_);
lean_dec_ref(v_fvars_1605_);
lean_dec_ref(v_lctx_1604_);
lean_dec(v_mvarId_1603_);
v_a_1631_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1622_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1622_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
goto v___jp_1616_;
}
}
else
{
goto v___jp_1616_;
}
v___jp_1616_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1617_ = lean_unsigned_to_nat(1u);
v___x_1618_ = lean_nat_add(v_n_1599_, v___x_1617_);
v___x_1619_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1600_, v___x_1601_, v_useNamesForExplicitOnly_1602_, v_mvarId_1603_, v___x_1618_, v_lctx_1604_, v_fvars_1605_, v___x_1606_, v_s_1607_, v___x_1615_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
return v___x_1619_;
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v_s_1607_);
lean_dec(v___x_1606_);
lean_dec_ref(v_fvars_1605_);
lean_dec_ref(v_lctx_1604_);
lean_dec(v_mvarId_1603_);
v_a_1639_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1613_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1613_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___boxed(lean_object* v_preserveBinderNames_1647_, lean_object* v___x_1648_, lean_object* v_useNamesForExplicitOnly_1649_, lean_object* v_mvarId_1650_, lean_object* v_i_1651_, lean_object* v_lctx_1652_, lean_object* v_fvars_1653_, lean_object* v_j_1654_, lean_object* v_s_1655_, lean_object* v_type_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1662_; uint8_t v___x_4268__boxed_1663_; uint8_t v_useNamesForExplicitOnly_boxed_1664_; lean_object* v_res_1665_; 
v_preserveBinderNames_boxed_1662_ = lean_unbox(v_preserveBinderNames_1647_);
v___x_4268__boxed_1663_ = lean_unbox(v___x_1648_);
v_useNamesForExplicitOnly_boxed_1664_ = lean_unbox(v_useNamesForExplicitOnly_1649_);
v_res_1665_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_boxed_1662_, v___x_4268__boxed_1663_, v_useNamesForExplicitOnly_boxed_1664_, v_mvarId_1650_, v_i_1651_, v_lctx_1652_, v_fvars_1653_, v_j_1654_, v_s_1655_, v_type_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___lam__0(lean_object* v_mvarId_1666_, lean_object* v___x_1667_, lean_object* v___x_1668_, uint8_t v_preserveBinderNames_1669_, uint8_t v___x_1670_, uint8_t v_useNamesForExplicitOnly_1671_, lean_object* v_n_1672_, lean_object* v_givenNames_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; 
lean_inc(v_mvarId_1666_);
v___x_1679_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1666_, v___x_1667_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v___x_1680_; 
lean_dec_ref_known(v___x_1679_, 1);
lean_inc(v_mvarId_1666_);
v___x_1680_ = l_Lean_MVarId_getType(v_mvarId_1666_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v_lctx_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1680_, 1);
v_lctx_1682_ = lean_ctor_get(v___y_1674_, 2);
lean_inc_ref(v_lctx_1682_);
v___x_1683_ = lean_mk_empty_array_with_capacity(v___x_1668_);
v___x_1684_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1669_, v___x_1670_, v_useNamesForExplicitOnly_1671_, v_mvarId_1666_, v_n_1672_, v_lctx_1682_, v___x_1683_, v___x_1668_, v_givenNames_1673_, v_a_1681_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec_ref(v___y_1674_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1704_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1704_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1704_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v_fst_1689_; lean_object* v_snd_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1703_; 
v_fst_1689_ = lean_ctor_get(v_a_1685_, 0);
v_snd_1690_ = lean_ctor_get(v_a_1685_, 1);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_a_1685_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1692_ = v_a_1685_;
v_isShared_1693_ = v_isSharedCheck_1703_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_snd_1690_);
lean_inc(v_fst_1689_);
lean_dec(v_a_1685_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1703_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
size_t v_sz_1694_; size_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1698_; 
v_sz_1694_ = lean_array_size(v_fst_1689_);
v___x_1695_ = ((size_t)0ULL);
v___x_1696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(v_sz_1694_, v___x_1695_, v_fst_1689_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1696_);
v___x_1698_ = v___x_1692_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1696_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_snd_1690_);
v___x_1698_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
lean_object* v___x_1700_; 
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1698_);
v___x_1700_ = v___x_1687_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
v_a_1705_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1684_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1684_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
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
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec_ref(v___y_1674_);
lean_dec(v_givenNames_1673_);
lean_dec(v_n_1672_);
lean_dec(v___x_1668_);
lean_dec(v_mvarId_1666_);
v_a_1713_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1680_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1680_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec_ref(v___y_1674_);
lean_dec(v_givenNames_1673_);
lean_dec(v_n_1672_);
lean_dec(v___x_1668_);
lean_dec(v_mvarId_1666_);
v_a_1721_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1679_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1679_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___lam__0___boxed(lean_object* v_mvarId_1729_, lean_object* v___x_1730_, lean_object* v___x_1731_, lean_object* v_preserveBinderNames_1732_, lean_object* v___x_1733_, lean_object* v_useNamesForExplicitOnly_1734_, lean_object* v_n_1735_, lean_object* v_givenNames_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1742_; uint8_t v___x_4497__boxed_1743_; uint8_t v_useNamesForExplicitOnly_boxed_1744_; lean_object* v_res_1745_; 
v_preserveBinderNames_boxed_1742_ = lean_unbox(v_preserveBinderNames_1732_);
v___x_4497__boxed_1743_ = lean_unbox(v___x_1733_);
v_useNamesForExplicitOnly_boxed_1744_ = lean_unbox(v_useNamesForExplicitOnly_1734_);
v_res_1745_ = l_Lean_Meta_introNCore___lam__0(v_mvarId_1729_, v___x_1730_, v___x_1731_, v_preserveBinderNames_boxed_1742_, v___x_4497__boxed_1743_, v_useNamesForExplicitOnly_boxed_1744_, v_n_1735_, v_givenNames_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore(lean_object* v_mvarId_1748_, lean_object* v_n_1749_, lean_object* v_givenNames_1750_, uint8_t v_useNamesForExplicitOnly_1751_, uint8_t v_preserveBinderNames_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = lean_nat_dec_eq(v_n_1749_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___f_1767_; lean_object* v___x_1768_; 
v___x_1760_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1755_);
v___x_1761_ = l_Lean_Meta_tactic_hygienic;
v___x_1762_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v___x_1760_, v___x_1761_);
lean_dec_ref(v___x_1760_);
v___x_1763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
v___x_1764_ = lean_box(v_preserveBinderNames_1752_);
v___x_1765_ = lean_box(v___x_1762_);
v___x_1766_ = lean_box(v_useNamesForExplicitOnly_1751_);
lean_inc(v_mvarId_1748_);
v___f_1767_ = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1767_, 0, v_mvarId_1748_);
lean_closure_set(v___f_1767_, 1, v___x_1763_);
lean_closure_set(v___f_1767_, 2, v___x_1758_);
lean_closure_set(v___f_1767_, 3, v___x_1764_);
lean_closure_set(v___f_1767_, 4, v___x_1765_);
lean_closure_set(v___f_1767_, 5, v___x_1766_);
lean_closure_set(v___f_1767_, 6, v_n_1749_);
lean_closure_set(v___f_1767_, 7, v_givenNames_1750_);
v___x_1768_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_1748_, v___f_1767_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
return v___x_1768_;
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec(v_givenNames_1750_);
lean_dec(v_n_1749_);
v___x_1769_ = ((lean_object*)(l_Lean_Meta_introNCore___closed__0));
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
lean_ctor_set(v___x_1770_, 1, v_mvarId_1748_);
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
return v___x_1771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___boxed(lean_object* v_mvarId_1772_, lean_object* v_n_1773_, lean_object* v_givenNames_1774_, lean_object* v_useNamesForExplicitOnly_1775_, lean_object* v_preserveBinderNames_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
uint8_t v_useNamesForExplicitOnly_boxed_1782_; uint8_t v_preserveBinderNames_boxed_1783_; lean_object* v_res_1784_; 
v_useNamesForExplicitOnly_boxed_1782_ = lean_unbox(v_useNamesForExplicitOnly_1775_);
v_preserveBinderNames_boxed_1783_ = lean_unbox(v_preserveBinderNames_1776_);
v_res_1784_ = l_Lean_Meta_introNCore(v_mvarId_1772_, v_n_1773_, v_givenNames_1774_, v_useNamesForExplicitOnly_boxed_1782_, v_preserveBinderNames_boxed_1783_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(lean_object* v_00_u03b1_1785_, lean_object* v_lctx_1786_, lean_object* v_x_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1786_, v_x_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1794_, lean_object* v_lctx_1795_, lean_object* v_x_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(v_00_u03b1_1794_, v_lctx_1795_, v_x_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(lean_object* v_e_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_1803_, v___y_1805_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___boxed(lean_object* v_e_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(v_e_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(lean_object* v_mvarId_1817_, lean_object* v_val_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1817_, v_val_1818_, v___y_1820_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___boxed(lean_object* v_mvarId_1825_, lean_object* v_val_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(v_mvarId_1825_, v_val_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1833_, lean_object* v_fvars_1834_, lean_object* v_j_1835_, lean_object* v_x_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1834_, v_j_1835_, v_x_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1843_, lean_object* v_fvars_1844_, lean_object* v_j_1845_, lean_object* v_x_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(v_00_u03b1_1843_, v_fvars_1844_, v_j_1845_, v_x_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___boxed(lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(v_x_1866_, v_x_1867_, v_x_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1870_, lean_object* v_x_1871_, size_t v_x_1872_, size_t v_x_1873_, lean_object* v_x_1874_, lean_object* v_x_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1871_, v_x_1872_, v_x_1873_, v_x_1874_, v_x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
size_t v_x_4750__boxed_1883_; size_t v_x_4751__boxed_1884_; lean_object* v_res_1885_; 
v_x_4750__boxed_1883_ = lean_unbox_usize(v_x_1879_);
lean_dec(v_x_1879_);
v_x_4751__boxed_1884_ = lean_unbox_usize(v_x_1880_);
lean_dec(v_x_1880_);
v_res_1885_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1877_, v_x_1878_, v_x_4750__boxed_1883_, v_x_4751__boxed_1884_, v_x_1881_, v_x_1882_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11(lean_object* v_00_u03b2_1886_, lean_object* v_n_1887_, lean_object* v_k_1888_, lean_object* v_v_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(v_n_1887_, v_k_1888_, v_v_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(lean_object* v_00_u03b2_1891_, size_t v_depth_1892_, lean_object* v_keys_1893_, lean_object* v_vals_1894_, lean_object* v_heq_1895_, lean_object* v_i_1896_, lean_object* v_entries_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_1892_, v_keys_1893_, v_vals_1894_, v_i_1896_, v_entries_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_1899_, lean_object* v_depth_1900_, lean_object* v_keys_1901_, lean_object* v_vals_1902_, lean_object* v_heq_1903_, lean_object* v_i_1904_, lean_object* v_entries_1905_){
_start:
{
size_t v_depth_boxed_1906_; lean_object* v_res_1907_; 
v_depth_boxed_1906_ = lean_unbox_usize(v_depth_1900_);
lean_dec(v_depth_1900_);
v_res_1907_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(v_00_u03b2_1899_, v_depth_boxed_1906_, v_keys_1901_, v_vals_1902_, v_heq_1903_, v_i_1904_, v_entries_1905_);
lean_dec_ref(v_vals_1902_);
lean_dec_ref(v_keys_1901_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1908_, lean_object* v_x_1909_, lean_object* v_x_1910_, lean_object* v_x_1911_, lean_object* v_x_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(v_x_1909_, v_x_1910_, v_x_1911_, v_x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introN(lean_object* v_mvarId_1914_, lean_object* v_n_1915_, lean_object* v_givenNames_1916_, uint8_t v_useNamesForExplicitOnly_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
uint8_t v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = 0;
v___x_1924_ = l_Lean_Meta_introNCore(v_mvarId_1914_, v_n_1915_, v_givenNames_1916_, v_useNamesForExplicitOnly_1917_, v___x_1923_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introN___boxed(lean_object* v_mvarId_1925_, lean_object* v_n_1926_, lean_object* v_givenNames_1927_, lean_object* v_useNamesForExplicitOnly_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
uint8_t v_useNamesForExplicitOnly_boxed_1934_; lean_object* v_res_1935_; 
v_useNamesForExplicitOnly_boxed_1934_ = lean_unbox(v_useNamesForExplicitOnly_1928_);
v_res_1935_ = l_Lean_MVarId_introN(v_mvarId_1925_, v_n_1926_, v_givenNames_1927_, v_useNamesForExplicitOnly_boxed_1934_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introNP(lean_object* v_mvarId_1936_, lean_object* v_n_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v___x_1943_; uint8_t v___x_1944_; uint8_t v___x_1945_; lean_object* v___x_1946_; 
v___x_1943_ = lean_box(0);
v___x_1944_ = 0;
v___x_1945_ = 1;
v___x_1946_ = l_Lean_Meta_introNCore(v_mvarId_1936_, v_n_1937_, v___x_1943_, v___x_1944_, v___x_1945_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introNP___boxed(lean_object* v_mvarId_1947_, lean_object* v_n_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_MVarId_introNP(v_mvarId_1947_, v_n_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro(lean_object* v_mvarId_1955_, lean_object* v_name_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; lean_object* v___x_1967_; 
v___x_1962_ = lean_box(0);
v___x_1963_ = lean_unsigned_to_nat(1u);
v___x_1964_ = lean_box(0);
v___x_1965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1965_, 0, v_name_1956_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = 0;
v___x_1967_ = l_Lean_Meta_introNCore(v_mvarId_1955_, v___x_1963_, v___x_1965_, v___x_1966_, v___x_1966_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1986_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_1986_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1986_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v_fst_1972_; lean_object* v_snd_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1985_; 
v_fst_1972_ = lean_ctor_get(v_a_1968_, 0);
v_snd_1973_ = lean_ctor_get(v_a_1968_, 1);
v_isSharedCheck_1985_ = !lean_is_exclusive(v_a_1968_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1975_ = v_a_1968_;
v_isShared_1976_ = v_isSharedCheck_1985_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_snd_1973_);
lean_inc(v_fst_1972_);
lean_dec(v_a_1968_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1985_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1977_ = lean_unsigned_to_nat(0u);
v___x_1978_ = lean_array_get(v___x_1962_, v_fst_1972_, v___x_1977_);
lean_dec(v_fst_1972_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1978_);
v___x_1980_ = v___x_1975_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_snd_1973_);
v___x_1980_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1982_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1980_);
v___x_1982_ = v___x_1970_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
v_a_1987_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1967_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1967_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_intro___boxed(lean_object* v_mvarId_1995_, lean_object* v_name_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_MVarId_intro(v_mvarId_1995_, v_name_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core(lean_object* v_mvarId_2003_, uint8_t v_preserveBinderNames_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; lean_object* v___x_2014_; 
v___x_2010_ = lean_box(0);
v___x_2011_ = lean_unsigned_to_nat(1u);
v___x_2012_ = lean_box(0);
v___x_2013_ = 0;
v___x_2014_ = l_Lean_Meta_introNCore(v_mvarId_2003_, v___x_2011_, v___x_2012_, v___x_2013_, v_preserveBinderNames_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2033_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2033_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2033_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v_fst_2019_; lean_object* v_snd_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2032_; 
v_fst_2019_ = lean_ctor_get(v_a_2015_, 0);
v_snd_2020_ = lean_ctor_get(v_a_2015_, 1);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_a_2015_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2022_ = v_a_2015_;
v_isShared_2023_ = v_isSharedCheck_2032_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_snd_2020_);
lean_inc(v_fst_2019_);
lean_dec(v_a_2015_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2032_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2024_ = lean_unsigned_to_nat(0u);
v___x_2025_ = lean_array_get(v___x_2010_, v_fst_2019_, v___x_2024_);
lean_dec(v_fst_2019_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2025_);
v___x_2027_ = v___x_2022_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_snd_2020_);
v___x_2027_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2029_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2027_);
v___x_2029_ = v___x_2017_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
v_a_2034_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2014_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2014_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core___boxed(lean_object* v_mvarId_2042_, lean_object* v_preserveBinderNames_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
uint8_t v_preserveBinderNames_boxed_2049_; lean_object* v_res_2050_; 
v_preserveBinderNames_boxed_2049_ = lean_unbox(v_preserveBinderNames_2043_);
v_res_2050_ = l_Lean_Meta_intro1Core(v_mvarId_2042_, v_preserveBinderNames_boxed_2049_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1(lean_object* v_mvarId_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
uint8_t v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = 0;
v___x_2058_ = l_Lean_Meta_intro1Core(v_mvarId_2051_, v___x_2057_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___boxed(lean_object* v_mvarId_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_MVarId_intro1(v_mvarId_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
lean_dec(v_a_2061_);
lean_dec_ref(v_a_2060_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1P(lean_object* v_mvarId_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
uint8_t v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = 1;
v___x_2073_ = l_Lean_Meta_intro1Core(v_mvarId_2066_, v___x_2072_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1P___boxed(lean_object* v_mvarId_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Lean_MVarId_intro1P(v_mvarId_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
lean_dec(v_a_2078_);
lean_dec_ref(v_a_2077_);
lean_dec(v_a_2076_);
lean_dec_ref(v_a_2075_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(lean_object* v_msgData_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; lean_object* v_env_2088_; uint8_t v___x_2089_; lean_object* v_env_2090_; lean_object* v___x_2091_; lean_object* v_toCold_2092_; lean_object* v_mctx_2093_; lean_object* v_lctx_2094_; lean_object* v_options_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2087_ = lean_st_ref_get(v___y_2085_);
v_env_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc_ref(v_env_2088_);
lean_dec(v___x_2087_);
v___x_2089_ = 0;
v_env_2090_ = l_Lean_Environment_setRecordingDeps(v_env_2088_, v___x_2089_);
v___x_2091_ = lean_st_ref_get(v___y_2083_);
v_toCold_2092_ = lean_ctor_get(v___y_2084_, 0);
v_mctx_2093_ = lean_ctor_get(v___x_2091_, 0);
lean_inc_ref(v_mctx_2093_);
lean_dec(v___x_2091_);
v_lctx_2094_ = lean_ctor_get(v___y_2082_, 2);
v_options_2095_ = lean_ctor_get(v_toCold_2092_, 2);
lean_inc_ref(v_options_2095_);
lean_inc_ref(v_lctx_2094_);
v___x_2096_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2096_, 0, v_env_2090_);
lean_ctor_set(v___x_2096_, 1, v_mctx_2093_);
lean_ctor_set(v___x_2096_, 2, v_lctx_2094_);
lean_ctor_set(v___x_2096_, 3, v_options_2095_);
v___x_2097_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
lean_ctor_set(v___x_2097_, 1, v_msgData_2081_);
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0___boxed(lean_object* v_msgData_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msgData_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(lean_object* v_msg_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_ref_2112_; lean_object* v___x_2113_; lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2122_; 
v_ref_2112_ = lean_ctor_get(v___y_2109_, 2);
v___x_2113_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msg_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2122_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2122_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; lean_object* v___x_2120_; 
lean_inc(v_ref_2112_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v_ref_2112_);
lean_ctor_set(v___x_2118_, 1, v_a_2114_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set_tag(v___x_2116_, 1);
lean_ctor_set(v___x_2116_, 0, v___x_2118_);
v___x_2120_ = v___x_2116_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg___boxed(lean_object* v_msg_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v_msg_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
return v_res_2129_;
}
}
static lean_object* _init_l_Lean_MVarId_intro1___00__lam__0___closed__1(void){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = ((lean_object*)(l_Lean_MVarId_intro1___00__lam__0___closed__0));
v___x_2132_ = l_Lean_stringToMessageData(v___x_2131_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__lam__0(lean_object* v_mvarId_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v___x_2139_; 
lean_inc(v_mvarId_2133_);
v___x_2139_ = l_Lean_MVarId_getType_x27(v_mvarId_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
if (lean_obj_tag(v_a_2140_) == 7)
{
lean_object* v_binderName_2141_; lean_object* v_binderType_2142_; lean_object* v_body_2143_; uint8_t v_binderInfo_2144_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; uint8_t v___x_2181_; 
v_binderName_2141_ = lean_ctor_get(v_a_2140_, 0);
lean_inc(v_binderName_2141_);
v_binderType_2142_ = lean_ctor_get(v_a_2140_, 1);
lean_inc_ref(v_binderType_2142_);
v_body_2143_ = lean_ctor_get(v_a_2140_, 2);
lean_inc_ref(v_body_2143_);
v_binderInfo_2144_ = lean_ctor_get_uint8(v_a_2140_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_2140_, 3);
v___x_2181_ = l_Lean_Expr_hasLooseBVars(v_body_2143_);
if (v___x_2181_ == 0)
{
v___y_2146_ = v___y_2134_;
v___y_2147_ = v___y_2135_;
v___y_2148_ = v___y_2136_;
v___y_2149_ = v___y_2137_;
goto v___jp_2145_;
}
else
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec_ref(v_body_2143_);
lean_dec_ref(v_binderType_2142_);
lean_dec(v_binderName_2141_);
v___x_2182_ = lean_obj_once(&l_Lean_MVarId_intro1___00__lam__0___closed__1, &l_Lean_MVarId_intro1___00__lam__0___closed__1_once, _init_l_Lean_MVarId_intro1___00__lam__0___closed__1);
v___x_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2183_, 0, v_mvarId_2133_);
v___x_2184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2182_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
v___x_2185_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v___x_2184_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2185_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
v___jp_2145_:
{
lean_object* v___x_2150_; 
lean_inc(v_mvarId_2133_);
v___x_2150_ = l_Lean_MVarId_getTag(v_mvarId_2133_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2152_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2150_, 1);
v___x_2152_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_body_2143_, v_a_2151_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2163_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc_n(v_a_2153_, 2);
lean_dec_ref_known(v___x_2152_, 1);
v___x_2154_ = l_Lean_Expr_lam___override(v_binderName_2141_, v_binderType_2142_, v_a_2153_, v_binderInfo_2144_);
v___x_2155_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_2133_, v___x_2154_, v___y_2147_);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2163_ == 0)
{
lean_object* v_unused_2164_; 
v_unused_2164_ = lean_ctor_get(v___x_2155_, 0);
lean_dec(v_unused_2164_);
v___x_2157_ = v___x_2155_;
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
else
{
lean_dec(v___x_2155_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2159_ = l_Lean_Expr_mvarId_x21(v_a_2153_);
lean_dec(v_a_2153_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2159_);
v___x_2161_ = v___x_2157_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v_binderType_2142_);
lean_dec(v_binderName_2141_);
lean_dec(v_mvarId_2133_);
v_a_2165_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2152_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2152_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec_ref(v_body_2143_);
lean_dec_ref(v_binderType_2142_);
lean_dec(v_binderName_2141_);
lean_dec(v_mvarId_2133_);
v_a_2173_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2150_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2150_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec(v_a_2140_);
v___x_2194_ = lean_obj_once(&l_Lean_MVarId_intro1___00__lam__0___closed__1, &l_Lean_MVarId_intro1___00__lam__0___closed__1_once, _init_l_Lean_MVarId_intro1___00__lam__0___closed__1);
v___x_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2195_, 0, v_mvarId_2133_);
v___x_2196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2194_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
v___x_2197_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v___x_2196_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
return v___x_2197_;
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v_mvarId_2133_);
v_a_2198_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2139_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2139_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__lam__0___boxed(lean_object* v_mvarId_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_MVarId_intro1___00__lam__0(v_mvarId_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1__(lean_object* v_mvarId_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v___f_2219_; lean_object* v___x_2220_; 
lean_inc(v_mvarId_2213_);
v___f_2219_ = lean_alloc_closure((void*)(l_Lean_MVarId_intro1___00__lam__0___boxed), 6, 1);
lean_closure_set(v___f_2219_, 0, v_mvarId_2213_);
v___x_2220_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_2213_, v___f_2219_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__boxed(lean_object* v_mvarId_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_MVarId_intro1__(v_mvarId_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(lean_object* v_00_u03b1_2228_, lean_object* v_msg_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v_msg_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___boxed(lean_object* v_00_u03b1_2236_, lean_object* v_msg_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(v_00_u03b1_2236_, v_msg_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntrosSize(lean_object* v_x_2244_){
_start:
{
switch(lean_obj_tag(v_x_2244_))
{
case 7:
{
lean_object* v_body_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v_body_2245_ = lean_ctor_get(v_x_2244_, 2);
v___x_2246_ = l_Lean_Meta_getIntrosSize(v_body_2245_);
v___x_2247_ = lean_unsigned_to_nat(1u);
v___x_2248_ = lean_nat_add(v___x_2246_, v___x_2247_);
lean_dec(v___x_2246_);
return v___x_2248_;
}
case 8:
{
lean_object* v_body_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v_body_2249_ = lean_ctor_get(v_x_2244_, 3);
v___x_2250_ = l_Lean_Meta_getIntrosSize(v_body_2249_);
v___x_2251_ = lean_unsigned_to_nat(1u);
v___x_2252_ = lean_nat_add(v___x_2250_, v___x_2251_);
lean_dec(v___x_2250_);
return v___x_2252_;
}
case 10:
{
lean_object* v_expr_2253_; 
v_expr_2253_ = lean_ctor_get(v_x_2244_, 1);
v_x_2244_ = v_expr_2253_;
goto _start;
}
default: 
{
lean_object* v___x_2255_; 
v___x_2255_ = lean_unsigned_to_nat(0u);
return v___x_2255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntrosSize___boxed(lean_object* v_x_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_Meta_getIntrosSize(v_x_2256_);
lean_dec_ref(v_x_2256_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intros(lean_object* v_mvarId_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v___x_2264_; 
lean_inc(v_mvarId_2258_);
v___x_2264_ = l_Lean_MVarId_getType(v_mvarId_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2266_; lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2281_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2264_, 1);
v___x_2266_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_a_2265_, v_a_2260_);
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2269_ = v___x_2266_;
v_isShared_2270_ = v_isSharedCheck_2281_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2266_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2281_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2271_ = l_Lean_Meta_getIntrosSize(v_a_2267_);
lean_dec(v_a_2267_);
v___x_2272_ = lean_unsigned_to_nat(0u);
v___x_2273_ = lean_nat_dec_eq(v___x_2271_, v___x_2272_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
lean_del_object(v___x_2269_);
v___x_2274_ = lean_box(0);
v___x_2275_ = l_Lean_Meta_introNCore(v_mvarId_2258_, v___x_2271_, v___x_2274_, v___x_2273_, v___x_2273_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
return v___x_2275_;
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2279_; 
lean_dec(v___x_2271_);
v___x_2276_ = ((lean_object*)(l_Lean_Meta_introNCore___closed__0));
v___x_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_ctor_set(v___x_2277_, 1, v_mvarId_2258_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v___x_2277_);
v___x_2279_ = v___x_2269_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec(v_mvarId_2258_);
v_a_2282_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2264_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2264_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intros___boxed(lean_object* v_mvarId_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_MVarId_intros(v_mvarId_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
return v_res_2296_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
