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
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0(lean_object* v_mvarId_1_, lean_object* v_type_2_, lean_object* v_fvars_3_, uint8_t v_isZero_4_, lean_object* v___x_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
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
lean_object* v_a_19_; lean_object* v___x_1304__overap_20_; lean_object* v___x_21_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_a_19_);
lean_dec_ref_known(v___x_18_, 1);
v___x_1304__overap_20_ = l_Lean_MVarId_assign___redArg(v___x_5_, v_mvarId_1_, v_a_19_);
v___x_21_ = lean_apply_5(v___x_1304__overap_20_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1_ = stack[0].m_obj;
lean_object* v_type_2_ = stack[1].m_obj;
lean_object* v_fvars_3_ = stack[2].m_obj;
uint8_t v_isZero_4_ = stack[3].m_num;
lean_object* v___x_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v___y_9_ = stack[8].m_obj;
lean_object* v_res_64_;
v_res_64_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0(v_mvarId_1_, v_type_2_, v_fvars_3_, v_isZero_4_, v___x_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0___boxed(lean_object* v_mvarId_65_, lean_object* v_type_66_, lean_object* v_fvars_67_, lean_object* v_isZero_68_, lean_object* v___x_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
uint8_t v_isZero_boxed_75_; lean_object* v_res_76_; 
v_isZero_boxed_75_ = lean_unbox(v_isZero_68_);
v_res_76_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0(v_mvarId_65_, v_type_66_, v_fvars_67_, v_isZero_boxed_75_, v___x_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
return v_res_76_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__2));
v___x_82_ = l_Lean_stringToMessageData(v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3);
v___x_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0(void){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_instMonadEIO___redArg();
return v___x_85_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0);
v___x_87_ = l_StateRefT_x27_instMonad___redArg(v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = l_Lean_Core_instMonadNameGeneratorCoreM;
v___x_94_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__7));
v___x_95_ = l_Lean_monadNameGeneratorLift___redArg(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9(void){
_start:
{
lean_object* v___x_97_; lean_object* v___f_98_; lean_object* v___x_99_; 
v___x_97_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8);
v___f_98_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__6));
v___x_99_ = l_Lean_monadNameGeneratorLift___redArg(v___f_98_, v___x_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___boxed(lean_object* v___x_100_, lean_object* v___x_101_, lean_object* v_type_102_, lean_object* v_mvarId_103_, lean_object* v_n_104_, lean_object* v_mkName_105_, lean_object* v_lctx_106_, lean_object* v_fvars_107_, lean_object* v___x_108_, lean_object* v_s_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1(v___x_100_, v___x_101_, v_type_102_, v_mvarId_103_, v_n_104_, v_mkName_105_, v_lctx_106_, v_fvars_107_, v___x_108_, v_s_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
lean_dec(v_n_104_);
return v_res_115_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(lean_object* v_mvarId_116_, lean_object* v_mkName_117_, lean_object* v_i_118_, lean_object* v_lctx_119_, lean_object* v_fvars_120_, lean_object* v_j_121_, lean_object* v_s_122_, lean_object* v_type_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v___x_129_; lean_object* v_toApplicative_130_; lean_object* v_toFunctor_131_; lean_object* v_toSeq_132_; lean_object* v_toSeqLeft_133_; lean_object* v_toSeqRight_134_; lean_object* v___f_135_; lean_object* v___f_136_; lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v_toApplicative_148_; lean_object* v_toFunctor_149_; lean_object* v_toSeq_150_; lean_object* v_toSeqLeft_151_; lean_object* v_toSeqRight_152_; lean_object* v___f_153_; lean_object* v___f_154_; lean_object* v___x_155_; lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v_toApplicative_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_283_; 
v___x_129_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
v_toApplicative_130_ = lean_ctor_get(v___x_129_, 0);
v_toFunctor_131_ = lean_ctor_get(v_toApplicative_130_, 0);
v_toSeq_132_ = lean_ctor_get(v_toApplicative_130_, 2);
v_toSeqLeft_133_ = lean_ctor_get(v_toApplicative_130_, 3);
v_toSeqRight_134_ = lean_ctor_get(v_toApplicative_130_, 4);
v___f_135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2));
v___f_136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_131_, 2);
v___f_137_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_137_, 0, v_toFunctor_131_);
v___f_138_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_138_, 0, v_toFunctor_131_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___f_137_);
lean_ctor_set(v___x_139_, 1, v___f_138_);
lean_inc(v_toSeqRight_134_);
v___f_140_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_140_, 0, v_toSeqRight_134_);
lean_inc(v_toSeqLeft_133_);
v___f_141_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_141_, 0, v_toSeqLeft_133_);
lean_inc(v_toSeq_132_);
v___f_142_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_142_, 0, v_toSeq_132_);
v___x_143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_143_, 0, v___x_139_);
lean_ctor_set(v___x_143_, 1, v___f_135_);
lean_ctor_set(v___x_143_, 2, v___f_142_);
lean_ctor_set(v___x_143_, 3, v___f_141_);
lean_ctor_set(v___x_143_, 4, v___f_140_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___f_136_);
v___x_145_ = l_StateRefT_x27_instMonad___redArg(v___x_144_);
v___x_146_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_146_, 0, lean_box(0));
lean_closure_set(v___x_146_, 1, lean_box(0));
lean_closure_set(v___x_146_, 2, v___x_145_);
v___x_147_ = l_instMonadControlTOfPure___redArg(v___x_146_);
v_toApplicative_148_ = lean_ctor_get(v___x_129_, 0);
v_toFunctor_149_ = lean_ctor_get(v_toApplicative_148_, 0);
v_toSeq_150_ = lean_ctor_get(v_toApplicative_148_, 2);
v_toSeqLeft_151_ = lean_ctor_get(v_toApplicative_148_, 3);
v_toSeqRight_152_ = lean_ctor_get(v_toApplicative_148_, 4);
lean_inc_ref_n(v_toFunctor_149_, 2);
v___f_153_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_153_, 0, v_toFunctor_149_);
v___f_154_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_154_, 0, v_toFunctor_149_);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v___f_153_);
lean_ctor_set(v___x_155_, 1, v___f_154_);
lean_inc(v_toSeqRight_152_);
v___f_156_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_156_, 0, v_toSeqRight_152_);
lean_inc(v_toSeqLeft_151_);
v___f_157_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_157_, 0, v_toSeqLeft_151_);
lean_inc(v_toSeq_150_);
v___f_158_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_158_, 0, v_toSeq_150_);
v___x_159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_159_, 0, v___x_155_);
lean_ctor_set(v___x_159_, 1, v___f_135_);
lean_ctor_set(v___x_159_, 2, v___f_158_);
lean_ctor_set(v___x_159_, 3, v___f_157_);
lean_ctor_set(v___x_159_, 4, v___f_156_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___f_136_);
v___x_161_ = l_StateRefT_x27_instMonad___redArg(v___x_160_);
v_toApplicative_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; 
v_unused_284_ = lean_ctor_get(v___x_161_, 1);
lean_dec(v_unused_284_);
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_283_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_toApplicative_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_283_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v_toFunctor_166_; lean_object* v_toSeq_167_; lean_object* v_toSeqLeft_168_; lean_object* v_toSeqRight_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_281_; 
v_toFunctor_166_ = lean_ctor_get(v_toApplicative_162_, 0);
v_toSeq_167_ = lean_ctor_get(v_toApplicative_162_, 2);
v_toSeqLeft_168_ = lean_ctor_get(v_toApplicative_162_, 3);
v_toSeqRight_169_ = lean_ctor_get(v_toApplicative_162_, 4);
v_isSharedCheck_281_ = !lean_is_exclusive(v_toApplicative_162_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; 
v_unused_282_ = lean_ctor_get(v_toApplicative_162_, 1);
lean_dec(v_unused_282_);
v___x_171_ = v_toApplicative_162_;
v_isShared_172_ = v_isSharedCheck_281_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_toSeqRight_169_);
lean_inc(v_toSeqLeft_168_);
lean_inc(v_toSeq_167_);
lean_inc(v_toFunctor_166_);
lean_dec(v_toApplicative_162_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_281_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___x_177_; lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___f_180_; lean_object* v___x_182_; 
v___f_173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4));
v___f_174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5));
lean_inc_ref(v_toFunctor_166_);
v___f_175_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_175_, 0, v_toFunctor_166_);
v___f_176_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_176_, 0, v_toFunctor_166_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v___f_175_);
lean_ctor_set(v___x_177_, 1, v___f_176_);
v___f_178_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_178_, 0, v_toSeqRight_169_);
v___f_179_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_179_, 0, v_toSeqLeft_168_);
v___f_180_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_180_, 0, v_toSeq_167_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 4, v___f_178_);
lean_ctor_set(v___x_171_, 3, v___f_179_);
lean_ctor_set(v___x_171_, 2, v___f_180_);
lean_ctor_set(v___x_171_, 1, v___f_173_);
lean_ctor_set(v___x_171_, 0, v___x_177_);
v___x_182_ = v___x_171_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___f_173_);
lean_ctor_set(v_reuseFailAlloc_280_, 2, v___f_180_);
lean_ctor_set(v_reuseFailAlloc_280_, 3, v___f_179_);
lean_ctor_set(v_reuseFailAlloc_280_, 4, v___f_178_);
v___x_182_ = v_reuseFailAlloc_280_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_184_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v___f_174_);
lean_ctor_set(v___x_164_, 0, v___x_182_);
v___x_184_ = v___x_164_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___f_174_);
v___x_184_ = v_reuseFailAlloc_279_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_zero_187_; uint8_t v_isZero_188_; 
v___x_185_ = l_Lean_Meta_instMonadMCtxMetaM;
v___x_186_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9);
v_zero_187_ = lean_unsigned_to_nat(0u);
v_isZero_188_ = lean_nat_dec_eq(v_i_118_, v_zero_187_);
if (v_isZero_188_ == 1)
{
lean_object* v___x_189_; lean_object* v_type_190_; lean_object* v___x_191_; lean_object* v___f_192_; lean_object* v___x_193_; lean_object* v___x_1273__overap_194_; lean_object* v___x_195_; 
lean_dec(v_s_122_);
lean_dec(v_i_118_);
lean_dec_ref(v_mkName_117_);
v___x_189_ = lean_array_get_size(v_fvars_120_);
v_type_190_ = lean_expr_instantiate_rev_range(v_type_123_, v_j_121_, v___x_189_, v_fvars_120_);
lean_dec_ref(v_type_123_);
v___x_191_ = lean_box(v_isZero_188_);
lean_inc_ref(v_fvars_120_);
v___f_192_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_192_, 0, v_mvarId_116_);
lean_closure_set(v___f_192_, 1, v_type_190_);
lean_closure_set(v___f_192_, 2, v_fvars_120_);
lean_closure_set(v___f_192_, 3, v___x_191_);
lean_closure_set(v___f_192_, 4, v___x_185_);
lean_inc_ref(v___x_184_);
lean_inc_ref(v___x_147_);
v___x_193_ = l_Lean_Meta_withNewLocalInstances___redArg(v___x_147_, v___x_184_, v_fvars_120_, v_j_121_, v___f_192_);
v___x_1273__overap_194_ = l_Lean_Meta_withLCtx_x27___redArg(v___x_147_, v___x_184_, v_lctx_119_, v___x_193_);
lean_inc(v_a_127_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
v___x_195_ = lean_apply_5(v___x_1273__overap_194_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, lean_box(0));
return v___x_195_;
}
else
{
lean_object* v_one_196_; lean_object* v_n_197_; 
v_one_196_ = lean_unsigned_to_nat(1u);
v_n_197_ = lean_nat_sub(v_i_118_, v_one_196_);
lean_dec(v_i_118_);
switch(lean_obj_tag(v_type_123_))
{
case 8:
{
lean_object* v_declName_198_; lean_object* v_type_199_; lean_object* v_value_200_; lean_object* v_body_201_; lean_object* v___x_202_; lean_object* v_type_203_; lean_object* v_type_204_; lean_object* v_val_205_; lean_object* v___x_1275__overap_206_; lean_object* v___x_207_; 
lean_dec_ref(v___x_147_);
v_declName_198_ = lean_ctor_get(v_type_123_, 0);
lean_inc(v_declName_198_);
v_type_199_ = lean_ctor_get(v_type_123_, 1);
lean_inc_ref(v_type_199_);
v_value_200_ = lean_ctor_get(v_type_123_, 2);
lean_inc_ref(v_value_200_);
v_body_201_ = lean_ctor_get(v_type_123_, 3);
lean_inc_ref(v_body_201_);
lean_dec_ref_known(v_type_123_, 4);
v___x_202_ = lean_array_get_size(v_fvars_120_);
v_type_203_ = lean_expr_instantiate_rev_range(v_type_199_, v_j_121_, v___x_202_, v_fvars_120_);
lean_dec_ref(v_type_199_);
v_type_204_ = l_Lean_Expr_headBeta(v_type_203_);
v_val_205_ = lean_expr_instantiate_rev_range(v_value_200_, v_j_121_, v___x_202_, v_fvars_120_);
lean_dec_ref(v_value_200_);
v___x_1275__overap_206_ = l_Lean_mkFreshFVarId___redArg(v___x_184_, v___x_186_);
lean_inc(v_a_127_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
v___x_207_ = lean_apply_5(v___x_1275__overap_206_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, lean_box(0));
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_207_, 1);
v___x_209_ = 1;
v___x_210_ = lean_box(v___x_209_);
lean_inc_ref(v_mkName_117_);
lean_inc(v_a_127_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
lean_inc_ref(v_lctx_119_);
v___x_211_ = lean_apply_9(v_mkName_117_, v_lctx_119_, v_declName_198_, v___x_210_, v_s_122_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, lean_box(0));
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v_fst_213_; lean_object* v_snd_214_; uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
v_fst_213_ = lean_ctor_get(v_a_212_, 0);
lean_inc(v_fst_213_);
v_snd_214_ = lean_ctor_get(v_a_212_, 1);
lean_inc(v_snd_214_);
lean_dec(v_a_212_);
v___x_215_ = 0;
lean_inc(v_a_208_);
v___x_216_ = l_Lean_LocalContext_mkLetDecl(v_lctx_119_, v_a_208_, v_fst_213_, v_type_204_, v_val_205_, v_isZero_188_, v___x_215_);
v___x_217_ = l_Lean_mkFVar(v_a_208_);
v___x_218_ = lean_array_push(v_fvars_120_, v___x_217_);
v_i_118_ = v_n_197_;
v_lctx_119_ = v___x_216_;
v_fvars_120_ = v___x_218_;
v_s_122_ = v_snd_214_;
v_type_123_ = v_body_201_;
goto _start;
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_dec(v_a_208_);
lean_dec_ref(v_val_205_);
lean_dec_ref(v_type_204_);
lean_dec_ref(v_body_201_);
lean_dec(v_n_197_);
lean_dec(v_j_121_);
lean_dec_ref(v_fvars_120_);
lean_dec_ref(v_lctx_119_);
lean_dec_ref(v_mkName_117_);
lean_dec(v_mvarId_116_);
v_a_220_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_211_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_211_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec_ref(v_val_205_);
lean_dec_ref(v_type_204_);
lean_dec_ref(v_body_201_);
lean_dec(v_declName_198_);
lean_dec(v_n_197_);
lean_dec(v_s_122_);
lean_dec(v_j_121_);
lean_dec_ref(v_fvars_120_);
lean_dec_ref(v_lctx_119_);
lean_dec_ref(v_mkName_117_);
lean_dec(v_mvarId_116_);
v_a_228_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_207_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_207_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
case 7:
{
lean_object* v_binderName_236_; lean_object* v_binderType_237_; lean_object* v_body_238_; uint8_t v_binderInfo_239_; lean_object* v___x_240_; lean_object* v_type_241_; lean_object* v_type_242_; lean_object* v___x_1277__overap_243_; lean_object* v___x_244_; 
lean_dec_ref(v___x_147_);
v_binderName_236_ = lean_ctor_get(v_type_123_, 0);
lean_inc(v_binderName_236_);
v_binderType_237_ = lean_ctor_get(v_type_123_, 1);
lean_inc_ref(v_binderType_237_);
v_body_238_ = lean_ctor_get(v_type_123_, 2);
lean_inc_ref(v_body_238_);
v_binderInfo_239_ = lean_ctor_get_uint8(v_type_123_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_123_, 3);
v___x_240_ = lean_array_get_size(v_fvars_120_);
v_type_241_ = lean_expr_instantiate_rev_range(v_binderType_237_, v_j_121_, v___x_240_, v_fvars_120_);
lean_dec_ref(v_binderType_237_);
v_type_242_ = l_Lean_Expr_headBeta(v_type_241_);
v___x_1277__overap_243_ = l_Lean_mkFreshFVarId___redArg(v___x_184_, v___x_186_);
lean_inc(v_a_127_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
v___x_244_ = lean_apply_5(v___x_1277__overap_243_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, lean_box(0));
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; uint8_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref_known(v___x_244_, 1);
v___x_246_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_239_);
v___x_247_ = lean_box(v___x_246_);
lean_inc_ref(v_mkName_117_);
lean_inc(v_a_127_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
lean_inc_ref(v_lctx_119_);
v___x_248_ = lean_apply_9(v_mkName_117_, v_lctx_119_, v_binderName_236_, v___x_247_, v_s_122_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, lean_box(0));
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v_fst_250_; lean_object* v_snd_251_; uint8_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_248_, 1);
v_fst_250_ = lean_ctor_get(v_a_249_, 0);
lean_inc(v_fst_250_);
v_snd_251_ = lean_ctor_get(v_a_249_, 1);
lean_inc(v_snd_251_);
lean_dec(v_a_249_);
v___x_252_ = 0;
lean_inc(v_a_245_);
v___x_253_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_119_, v_a_245_, v_fst_250_, v_type_242_, v_binderInfo_239_, v___x_252_);
v___x_254_ = l_Lean_mkFVar(v_a_245_);
v___x_255_ = lean_array_push(v_fvars_120_, v___x_254_);
v_i_118_ = v_n_197_;
v_lctx_119_ = v___x_253_;
v_fvars_120_ = v___x_255_;
v_s_122_ = v_snd_251_;
v_type_123_ = v_body_238_;
goto _start;
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
lean_dec(v_a_245_);
lean_dec_ref(v_type_242_);
lean_dec_ref(v_body_238_);
lean_dec(v_n_197_);
lean_dec(v_j_121_);
lean_dec_ref(v_fvars_120_);
lean_dec_ref(v_lctx_119_);
lean_dec_ref(v_mkName_117_);
lean_dec(v_mvarId_116_);
v_a_257_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_248_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_248_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec_ref(v_type_242_);
lean_dec_ref(v_body_238_);
lean_dec(v_binderName_236_);
lean_dec(v_n_197_);
lean_dec(v_s_122_);
lean_dec(v_j_121_);
lean_dec_ref(v_fvars_120_);
lean_dec_ref(v_lctx_119_);
lean_dec_ref(v_mkName_117_);
lean_dec(v_mvarId_116_);
v_a_265_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_244_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_244_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
default: 
{
lean_object* v___x_273_; lean_object* v_type_274_; lean_object* v___f_275_; lean_object* v___x_276_; lean_object* v___x_1283__overap_277_; lean_object* v___x_278_; 
v___x_273_ = lean_array_get_size(v_fvars_120_);
v_type_274_ = lean_expr_instantiate_rev_range(v_type_123_, v_j_121_, v___x_273_, v_fvars_120_);
lean_dec_ref(v_type_123_);
lean_inc_ref(v_fvars_120_);
lean_inc_ref(v_lctx_119_);
lean_inc_ref_n(v___x_184_, 2);
v___f_275_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___boxed), 15, 10);
lean_closure_set(v___f_275_, 0, v___x_184_);
lean_closure_set(v___f_275_, 1, v___x_185_);
lean_closure_set(v___f_275_, 2, v_type_274_);
lean_closure_set(v___f_275_, 3, v_mvarId_116_);
lean_closure_set(v___f_275_, 4, v_n_197_);
lean_closure_set(v___f_275_, 5, v_mkName_117_);
lean_closure_set(v___f_275_, 6, v_lctx_119_);
lean_closure_set(v___f_275_, 7, v_fvars_120_);
lean_closure_set(v___f_275_, 8, v___x_273_);
lean_closure_set(v___f_275_, 9, v_s_122_);
lean_inc_ref(v___x_147_);
v___x_276_ = l_Lean_Meta_withNewLocalInstances___redArg(v___x_147_, v___x_184_, v_fvars_120_, v_j_121_, v___f_275_);
v___x_1283__overap_277_ = l_Lean_Meta_withLCtx_x27___redArg(v___x_147_, v___x_184_, v_lctx_119_, v___x_276_);
lean_inc(v_a_127_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
v___x_278_ = lean_apply_5(v___x_1283__overap_277_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, lean_box(0));
return v___x_278_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_116_ = stack[0].m_obj;
lean_object* v_mkName_117_ = stack[1].m_obj;
lean_object* v_i_118_ = stack[2].m_obj;
lean_object* v_lctx_119_ = stack[3].m_obj;
lean_object* v_fvars_120_ = stack[4].m_obj;
lean_object* v_j_121_ = stack[5].m_obj;
lean_object* v_s_122_ = stack[6].m_obj;
lean_object* v_type_123_ = stack[7].m_obj;
lean_object* v_a_124_ = stack[8].m_obj;
lean_object* v_a_125_ = stack[9].m_obj;
lean_object* v_a_126_ = stack[10].m_obj;
lean_object* v_a_127_ = stack[11].m_obj;
lean_object* v_res_285_;
v_res_285_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_116_, v_mkName_117_, v_i_118_, v_lctx_119_, v_fvars_120_, v_j_121_, v_s_122_, v_type_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
stack->m_obj
 = v_res_285_;
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1(lean_object* v___x_286_, lean_object* v___x_287_, lean_object* v_type_288_, lean_object* v_mvarId_289_, lean_object* v_n_290_, lean_object* v_mkName_291_, lean_object* v_lctx_292_, lean_object* v_fvars_293_, lean_object* v___x_294_, lean_object* v_s_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_1331__overap_301_; lean_object* v___x_302_; 
v___x_1331__overap_301_ = l_Lean_instantiateMVars___redArg(v___x_286_, v___x_287_, v_type_288_);
lean_inc(v___y_299_);
lean_inc_ref(v___y_298_);
lean_inc(v___y_297_);
lean_inc_ref(v___y_296_);
v___x_302_ = lean_apply_5(v___x_1331__overap_301_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, lean_box(0));
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_304_; uint8_t v___y_306_; uint8_t v___x_327_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_303_);
lean_dec_ref_known(v___x_302_, 1);
v___x_304_ = l_Lean_Expr_cleanupAnnotations(v_a_303_);
v___x_327_ = l_Lean_Expr_isForall(v___x_304_);
if (v___x_327_ == 0)
{
uint8_t v___x_328_; 
v___x_328_ = l_Lean_Expr_isLet(v___x_304_);
v___y_306_ = v___x_328_;
goto v___jp_305_;
}
else
{
v___y_306_ = v___x_327_;
goto v___jp_305_;
}
v___jp_305_:
{
if (v___y_306_ == 0)
{
lean_object* v___x_307_; 
lean_inc(v___y_299_);
lean_inc_ref(v___y_298_);
lean_inc(v___y_297_);
lean_inc_ref(v___y_296_);
v___x_307_ = lean_whnf(v___x_304_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; uint8_t v___x_309_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_307_, 1);
v___x_309_ = l_Lean_Expr_isForall(v_a_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec(v_a_308_);
lean_dec(v_s_295_);
lean_dec(v___x_294_);
lean_dec_ref(v_fvars_293_);
lean_dec_ref(v_lctx_292_);
lean_dec_ref(v_mkName_291_);
v___x_310_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
v___x_311_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4);
v___x_312_ = l_Lean_Meta_throwTacticEx___redArg(v___x_310_, v_mvarId_289_, v___x_311_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
return v___x_312_;
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = lean_unsigned_to_nat(1u);
v___x_314_ = lean_nat_add(v_n_290_, v___x_313_);
v___x_315_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_289_, v_mkName_291_, v___x_314_, v_lctx_292_, v_fvars_293_, v___x_294_, v_s_295_, v_a_308_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
return v___x_315_;
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v_s_295_);
lean_dec(v___x_294_);
lean_dec_ref(v_fvars_293_);
lean_dec_ref(v_lctx_292_);
lean_dec_ref(v_mkName_291_);
lean_dec(v_mvarId_289_);
v_a_316_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_307_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_307_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = lean_unsigned_to_nat(1u);
v___x_325_ = lean_nat_add(v_n_290_, v___x_324_);
v___x_326_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_289_, v_mkName_291_, v___x_325_, v_lctx_292_, v_fvars_293_, v___x_294_, v_s_295_, v___x_304_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
return v___x_326_;
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v_s_295_);
lean_dec(v___x_294_);
lean_dec_ref(v_fvars_293_);
lean_dec_ref(v_lctx_292_);
lean_dec_ref(v_mkName_291_);
lean_dec(v_mvarId_289_);
v_a_329_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_302_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_302_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_286_ = stack[0].m_obj;
lean_object* v___x_287_ = stack[1].m_obj;
lean_object* v_type_288_ = stack[2].m_obj;
lean_object* v_mvarId_289_ = stack[3].m_obj;
lean_object* v_n_290_ = stack[4].m_obj;
lean_object* v_mkName_291_ = stack[5].m_obj;
lean_object* v_lctx_292_ = stack[6].m_obj;
lean_object* v_fvars_293_ = stack[7].m_obj;
lean_object* v___x_294_ = stack[8].m_obj;
lean_object* v_s_295_ = stack[9].m_obj;
lean_object* v___y_296_ = stack[10].m_obj;
lean_object* v___y_297_ = stack[11].m_obj;
lean_object* v___y_298_ = stack[12].m_obj;
lean_object* v___y_299_ = stack[13].m_obj;
lean_object* v_res_337_;
v_res_337_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1(v___x_286_, v___x_287_, v_type_288_, v_mvarId_289_, v_n_290_, v_mkName_291_, v_lctx_292_, v_fvars_293_, v___x_294_, v_s_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
stack->m_obj
 = v_res_337_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___boxed(lean_object* v_mvarId_338_, lean_object* v_mkName_339_, lean_object* v_i_340_, lean_object* v_lctx_341_, lean_object* v_fvars_342_, lean_object* v_j_343_, lean_object* v_s_344_, lean_object* v_type_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_338_, v_mkName_339_, v_i_340_, v_lctx_341_, v_fvars_342_, v_j_343_, v_s_344_, v_type_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
return v_res_351_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(lean_object* v_00_u03c3_352_, lean_object* v_mvarId_353_, lean_object* v_mkName_354_, lean_object* v_i_355_, lean_object* v_lctx_356_, lean_object* v_fvars_357_, lean_object* v_j_358_, lean_object* v_s_359_, lean_object* v_type_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_353_, v_mkName_354_, v_i_355_, v_lctx_356_, v_fvars_357_, v_j_358_, v_s_359_, v_type_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
return v___x_366_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_353_ = stack[1].m_obj;
lean_object* v_mkName_354_ = stack[2].m_obj;
lean_object* v_i_355_ = stack[3].m_obj;
lean_object* v_lctx_356_ = stack[4].m_obj;
lean_object* v_fvars_357_ = stack[5].m_obj;
lean_object* v_j_358_ = stack[6].m_obj;
lean_object* v_s_359_ = stack[7].m_obj;
lean_object* v_type_360_ = stack[8].m_obj;
lean_object* v_a_361_ = stack[9].m_obj;
lean_object* v_a_362_ = stack[10].m_obj;
lean_object* v_a_363_ = stack[11].m_obj;
lean_object* v_a_364_ = stack[12].m_obj;
lean_object* v_res_367_;
v_res_367_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(lean_box(0), v_mvarId_353_, v_mkName_354_, v_i_355_, v_lctx_356_, v_fvars_357_, v_j_358_, v_s_359_, v_type_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
stack->m_obj
 = v_res_367_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___boxed(lean_object* v_00_u03c3_368_, lean_object* v_mvarId_369_, lean_object* v_mkName_370_, lean_object* v_i_371_, lean_object* v_lctx_372_, lean_object* v_fvars_373_, lean_object* v_j_374_, lean_object* v_s_375_, lean_object* v_type_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(v_00_u03c3_368_, v_mvarId_369_, v_mkName_370_, v_i_371_, v_lctx_372_, v_fvars_373_, v_j_374_, v_s_375_, v_type_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
return v_res_382_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0(lean_object* v_mvarId_404_, lean_object* v___x_405_, lean_object* v_mkName_406_, lean_object* v_n_407_, lean_object* v_s_408_, lean_object* v___f_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; 
lean_inc(v_mvarId_404_);
v___x_415_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_404_, v___x_405_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v___x_416_; 
lean_dec_ref_known(v___x_415_, 1);
lean_inc(v_mvarId_404_);
v___x_416_ = l_Lean_MVarId_getType(v_mvarId_404_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v_lctx_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_416_, 1);
v_lctx_418_ = lean_ctor_get(v___y_410_, 2);
lean_inc_ref(v_lctx_418_);
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__0));
v___x_421_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_404_, v_mkName_406_, v_n_407_, v_lctx_418_, v___x_420_, v___x_419_, v_s_408_, v_a_417_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec_ref(v___y_410_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_442_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_442_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_442_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_442_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v_fst_426_; lean_object* v_snd_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_441_; 
v_fst_426_ = lean_ctor_get(v_a_422_, 0);
v_snd_427_ = lean_ctor_get(v_a_422_, 1);
v_isSharedCheck_441_ = !lean_is_exclusive(v_a_422_);
if (v_isSharedCheck_441_ == 0)
{
v___x_429_ = v_a_422_;
v_isShared_430_ = v_isSharedCheck_441_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_snd_427_);
lean_inc(v_fst_426_);
lean_dec(v_a_422_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_441_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; size_t v_sz_432_; size_t v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__10));
v_sz_432_ = lean_array_size(v_fst_426_);
v___x_433_ = ((size_t)0ULL);
v___x_434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_431_, v___f_409_, v_sz_432_, v___x_433_, v_fst_426_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_434_);
v___x_436_ = v___x_429_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_snd_427_);
v___x_436_ = v_reuseFailAlloc_440_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_438_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_436_);
v___x_438_ = v___x_424_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec_ref(v___f_409_);
v_a_443_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_421_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_421_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref(v___y_410_);
lean_dec_ref(v___f_409_);
lean_dec(v_s_408_);
lean_dec(v_n_407_);
lean_dec_ref(v_mkName_406_);
lean_dec(v_mvarId_404_);
v_a_451_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_416_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_416_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec_ref(v___y_410_);
lean_dec_ref(v___f_409_);
lean_dec(v_s_408_);
lean_dec(v_n_407_);
lean_dec_ref(v_mkName_406_);
lean_dec(v_mvarId_404_);
v_a_459_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_415_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_415_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_404_ = stack[0].m_obj;
lean_object* v___x_405_ = stack[1].m_obj;
lean_object* v_mkName_406_ = stack[2].m_obj;
lean_object* v_n_407_ = stack[3].m_obj;
lean_object* v_s_408_ = stack[4].m_obj;
lean_object* v___f_409_ = stack[5].m_obj;
lean_object* v___y_410_ = stack[6].m_obj;
lean_object* v___y_411_ = stack[7].m_obj;
lean_object* v___y_412_ = stack[8].m_obj;
lean_object* v___y_413_ = stack[9].m_obj;
lean_object* v_res_467_;
v_res_467_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0(v_mvarId_404_, v___x_405_, v_mkName_406_, v_n_407_, v_s_408_, v___f_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
stack->m_obj
 = v_res_467_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed(lean_object* v_mvarId_468_, lean_object* v___x_469_, lean_object* v_mkName_470_, lean_object* v_n_471_, lean_object* v_s_472_, lean_object* v___f_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0(v_mvarId_468_, v___x_469_, v_mkName_470_, v_n_471_, v_s_472_, v___f_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
return v_res_479_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg(lean_object* v_mvarId_481_, lean_object* v_n_482_, lean_object* v_mkName_483_, lean_object* v_s_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_490_; lean_object* v_toApplicative_491_; lean_object* v_toFunctor_492_; lean_object* v_toSeq_493_; lean_object* v_toSeqLeft_494_; lean_object* v_toSeqRight_495_; lean_object* v___f_496_; lean_object* v___f_497_; lean_object* v___f_498_; lean_object* v___f_499_; lean_object* v___x_500_; lean_object* v___f_501_; lean_object* v___f_502_; lean_object* v___f_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v_toApplicative_509_; lean_object* v_toFunctor_510_; lean_object* v_toSeq_511_; lean_object* v_toSeqLeft_512_; lean_object* v_toSeqRight_513_; lean_object* v___f_514_; lean_object* v___f_515_; lean_object* v___x_516_; lean_object* v___f_517_; lean_object* v___f_518_; lean_object* v___f_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v_toApplicative_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_555_; 
v___x_490_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
v_toApplicative_491_ = lean_ctor_get(v___x_490_, 0);
v_toFunctor_492_ = lean_ctor_get(v_toApplicative_491_, 0);
v_toSeq_493_ = lean_ctor_get(v_toApplicative_491_, 2);
v_toSeqLeft_494_ = lean_ctor_get(v_toApplicative_491_, 3);
v_toSeqRight_495_ = lean_ctor_get(v_toApplicative_491_, 4);
v___f_496_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2));
v___f_497_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_492_, 2);
v___f_498_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_498_, 0, v_toFunctor_492_);
v___f_499_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_499_, 0, v_toFunctor_492_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___f_498_);
lean_ctor_set(v___x_500_, 1, v___f_499_);
lean_inc(v_toSeqRight_495_);
v___f_501_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_501_, 0, v_toSeqRight_495_);
lean_inc(v_toSeqLeft_494_);
v___f_502_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_502_, 0, v_toSeqLeft_494_);
lean_inc(v_toSeq_493_);
v___f_503_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_503_, 0, v_toSeq_493_);
v___x_504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_504_, 0, v___x_500_);
lean_ctor_set(v___x_504_, 1, v___f_496_);
lean_ctor_set(v___x_504_, 2, v___f_503_);
lean_ctor_set(v___x_504_, 3, v___f_502_);
lean_ctor_set(v___x_504_, 4, v___f_501_);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v___f_497_);
v___x_506_ = l_StateRefT_x27_instMonad___redArg(v___x_505_);
v___x_507_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_507_, 0, lean_box(0));
lean_closure_set(v___x_507_, 1, lean_box(0));
lean_closure_set(v___x_507_, 2, v___x_506_);
v___x_508_ = l_instMonadControlTOfPure___redArg(v___x_507_);
v_toApplicative_509_ = lean_ctor_get(v___x_490_, 0);
v_toFunctor_510_ = lean_ctor_get(v_toApplicative_509_, 0);
v_toSeq_511_ = lean_ctor_get(v_toApplicative_509_, 2);
v_toSeqLeft_512_ = lean_ctor_get(v_toApplicative_509_, 3);
v_toSeqRight_513_ = lean_ctor_get(v_toApplicative_509_, 4);
lean_inc_ref_n(v_toFunctor_510_, 2);
v___f_514_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_514_, 0, v_toFunctor_510_);
v___f_515_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_515_, 0, v_toFunctor_510_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___f_514_);
lean_ctor_set(v___x_516_, 1, v___f_515_);
lean_inc(v_toSeqRight_513_);
v___f_517_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_517_, 0, v_toSeqRight_513_);
lean_inc(v_toSeqLeft_512_);
v___f_518_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_518_, 0, v_toSeqLeft_512_);
lean_inc(v_toSeq_511_);
v___f_519_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_519_, 0, v_toSeq_511_);
v___x_520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_520_, 0, v___x_516_);
lean_ctor_set(v___x_520_, 1, v___f_496_);
lean_ctor_set(v___x_520_, 2, v___f_519_);
lean_ctor_set(v___x_520_, 3, v___f_518_);
lean_ctor_set(v___x_520_, 4, v___f_517_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
lean_ctor_set(v___x_521_, 1, v___f_497_);
v___x_522_ = l_StateRefT_x27_instMonad___redArg(v___x_521_);
v_toApplicative_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v___x_522_, 1);
lean_dec(v_unused_556_);
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_555_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_toApplicative_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_555_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v_toFunctor_527_; lean_object* v_toSeq_528_; lean_object* v_toSeqLeft_529_; lean_object* v_toSeqRight_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_553_; 
v_toFunctor_527_ = lean_ctor_get(v_toApplicative_523_, 0);
v_toSeq_528_ = lean_ctor_get(v_toApplicative_523_, 2);
v_toSeqLeft_529_ = lean_ctor_get(v_toApplicative_523_, 3);
v_toSeqRight_530_ = lean_ctor_get(v_toApplicative_523_, 4);
v_isSharedCheck_553_ = !lean_is_exclusive(v_toApplicative_523_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; 
v_unused_554_ = lean_ctor_get(v_toApplicative_523_, 1);
lean_dec(v_unused_554_);
v___x_532_ = v_toApplicative_523_;
v_isShared_533_ = v_isSharedCheck_553_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_toSeqRight_530_);
lean_inc(v_toSeqLeft_529_);
lean_inc(v_toSeq_528_);
lean_inc(v_toFunctor_527_);
lean_dec(v_toApplicative_523_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_553_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___f_534_; lean_object* v___f_535_; lean_object* v___f_536_; lean_object* v___f_537_; lean_object* v___f_538_; lean_object* v___x_539_; lean_object* v___f_540_; lean_object* v___f_541_; lean_object* v___f_542_; lean_object* v___x_544_; 
v___f_534_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0));
v___f_535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4));
v___f_536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5));
lean_inc_ref(v_toFunctor_527_);
v___f_537_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_537_, 0, v_toFunctor_527_);
v___f_538_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_538_, 0, v_toFunctor_527_);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v___f_537_);
lean_ctor_set(v___x_539_, 1, v___f_538_);
v___f_540_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_540_, 0, v_toSeqRight_530_);
v___f_541_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_541_, 0, v_toSeqLeft_529_);
v___f_542_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_542_, 0, v_toSeq_528_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 4, v___f_540_);
lean_ctor_set(v___x_532_, 3, v___f_541_);
lean_ctor_set(v___x_532_, 2, v___f_542_);
lean_ctor_set(v___x_532_, 1, v___f_535_);
lean_ctor_set(v___x_532_, 0, v___x_539_);
v___x_544_ = v___x_532_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___f_535_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v___f_542_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v___f_541_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v___f_540_);
v___x_544_ = v_reuseFailAlloc_552_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_546_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v___f_536_);
lean_ctor_set(v___x_525_, 0, v___x_544_);
v___x_546_ = v___x_525_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___f_536_);
v___x_546_ = v_reuseFailAlloc_551_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; lean_object* v___f_548_; lean_object* v___x_534__overap_549_; lean_object* v___x_550_; 
v___x_547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
lean_inc(v_mvarId_481_);
v___f_548_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_548_, 0, v_mvarId_481_);
lean_closure_set(v___f_548_, 1, v___x_547_);
lean_closure_set(v___f_548_, 2, v_mkName_483_);
lean_closure_set(v___f_548_, 3, v_n_482_);
lean_closure_set(v___f_548_, 4, v_s_484_);
lean_closure_set(v___f_548_, 5, v___f_534_);
v___x_534__overap_549_ = l_Lean_MVarId_withContext___redArg(v___x_508_, v___x_546_, v_mvarId_481_, v___f_548_);
lean_inc(v_a_488_);
lean_inc_ref(v_a_487_);
lean_inc(v_a_486_);
lean_inc_ref(v_a_485_);
v___x_550_ = lean_apply_5(v___x_534__overap_549_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, lean_box(0));
return v___x_550_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_481_ = stack[0].m_obj;
lean_object* v_n_482_ = stack[1].m_obj;
lean_object* v_mkName_483_ = stack[2].m_obj;
lean_object* v_s_484_ = stack[3].m_obj;
lean_object* v_a_485_ = stack[4].m_obj;
lean_object* v_a_486_ = stack[5].m_obj;
lean_object* v_a_487_ = stack[6].m_obj;
lean_object* v_a_488_ = stack[7].m_obj;
lean_object* v_res_557_;
v_res_557_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg(v_mvarId_481_, v_n_482_, v_mkName_483_, v_s_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
stack->m_obj
 = v_res_557_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___boxed(lean_object* v_mvarId_558_, lean_object* v_n_559_, lean_object* v_mkName_560_, lean_object* v_s_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg(v_mvarId_558_, v_n_559_, v_mkName_560_, v_s_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
return v_res_567_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(lean_object* v_00_u03c3_568_, lean_object* v_mvarId_569_, lean_object* v_n_570_, lean_object* v_mkName_571_, lean_object* v_s_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_578_; lean_object* v_toApplicative_579_; lean_object* v_toFunctor_580_; lean_object* v_toSeq_581_; lean_object* v_toSeqLeft_582_; lean_object* v_toSeqRight_583_; lean_object* v___f_584_; lean_object* v___f_585_; lean_object* v___f_586_; lean_object* v___f_587_; lean_object* v___x_588_; lean_object* v___f_589_; lean_object* v___f_590_; lean_object* v___f_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v_toApplicative_597_; lean_object* v_toFunctor_598_; lean_object* v_toSeq_599_; lean_object* v_toSeqLeft_600_; lean_object* v_toSeqRight_601_; lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___x_604_; lean_object* v___f_605_; lean_object* v___f_606_; lean_object* v___f_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v_toApplicative_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_643_; 
v___x_578_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
v_toApplicative_579_ = lean_ctor_get(v___x_578_, 0);
v_toFunctor_580_ = lean_ctor_get(v_toApplicative_579_, 0);
v_toSeq_581_ = lean_ctor_get(v_toApplicative_579_, 2);
v_toSeqLeft_582_ = lean_ctor_get(v_toApplicative_579_, 3);
v_toSeqRight_583_ = lean_ctor_get(v_toApplicative_579_, 4);
v___f_584_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2));
v___f_585_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_580_, 2);
v___f_586_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_586_, 0, v_toFunctor_580_);
v___f_587_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_587_, 0, v_toFunctor_580_);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v___f_586_);
lean_ctor_set(v___x_588_, 1, v___f_587_);
lean_inc(v_toSeqRight_583_);
v___f_589_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_589_, 0, v_toSeqRight_583_);
lean_inc(v_toSeqLeft_582_);
v___f_590_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_590_, 0, v_toSeqLeft_582_);
lean_inc(v_toSeq_581_);
v___f_591_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_591_, 0, v_toSeq_581_);
v___x_592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_592_, 0, v___x_588_);
lean_ctor_set(v___x_592_, 1, v___f_584_);
lean_ctor_set(v___x_592_, 2, v___f_591_);
lean_ctor_set(v___x_592_, 3, v___f_590_);
lean_ctor_set(v___x_592_, 4, v___f_589_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v___f_585_);
v___x_594_ = l_StateRefT_x27_instMonad___redArg(v___x_593_);
v___x_595_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_595_, 0, lean_box(0));
lean_closure_set(v___x_595_, 1, lean_box(0));
lean_closure_set(v___x_595_, 2, v___x_594_);
v___x_596_ = l_instMonadControlTOfPure___redArg(v___x_595_);
v_toApplicative_597_ = lean_ctor_get(v___x_578_, 0);
v_toFunctor_598_ = lean_ctor_get(v_toApplicative_597_, 0);
v_toSeq_599_ = lean_ctor_get(v_toApplicative_597_, 2);
v_toSeqLeft_600_ = lean_ctor_get(v_toApplicative_597_, 3);
v_toSeqRight_601_ = lean_ctor_get(v_toApplicative_597_, 4);
lean_inc_ref_n(v_toFunctor_598_, 2);
v___f_602_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_602_, 0, v_toFunctor_598_);
v___f_603_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_603_, 0, v_toFunctor_598_);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___f_602_);
lean_ctor_set(v___x_604_, 1, v___f_603_);
lean_inc(v_toSeqRight_601_);
v___f_605_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_605_, 0, v_toSeqRight_601_);
lean_inc(v_toSeqLeft_600_);
v___f_606_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_606_, 0, v_toSeqLeft_600_);
lean_inc(v_toSeq_599_);
v___f_607_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_607_, 0, v_toSeq_599_);
v___x_608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_608_, 0, v___x_604_);
lean_ctor_set(v___x_608_, 1, v___f_584_);
lean_ctor_set(v___x_608_, 2, v___f_607_);
lean_ctor_set(v___x_608_, 3, v___f_606_);
lean_ctor_set(v___x_608_, 4, v___f_605_);
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___f_585_);
v___x_610_ = l_StateRefT_x27_instMonad___redArg(v___x_609_);
v_toApplicative_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; 
v_unused_644_ = lean_ctor_get(v___x_610_, 1);
lean_dec(v_unused_644_);
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_643_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_toApplicative_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_643_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_toFunctor_615_; lean_object* v_toSeq_616_; lean_object* v_toSeqLeft_617_; lean_object* v_toSeqRight_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_641_; 
v_toFunctor_615_ = lean_ctor_get(v_toApplicative_611_, 0);
v_toSeq_616_ = lean_ctor_get(v_toApplicative_611_, 2);
v_toSeqLeft_617_ = lean_ctor_get(v_toApplicative_611_, 3);
v_toSeqRight_618_ = lean_ctor_get(v_toApplicative_611_, 4);
v_isSharedCheck_641_ = !lean_is_exclusive(v_toApplicative_611_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; 
v_unused_642_ = lean_ctor_get(v_toApplicative_611_, 1);
lean_dec(v_unused_642_);
v___x_620_ = v_toApplicative_611_;
v_isShared_621_ = v_isSharedCheck_641_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_toSeqRight_618_);
lean_inc(v_toSeqLeft_617_);
lean_inc(v_toSeq_616_);
lean_inc(v_toFunctor_615_);
lean_dec(v_toApplicative_611_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_641_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___f_622_; lean_object* v___f_623_; lean_object* v___f_624_; lean_object* v___f_625_; lean_object* v___f_626_; lean_object* v___x_627_; lean_object* v___f_628_; lean_object* v___f_629_; lean_object* v___f_630_; lean_object* v___x_632_; 
v___f_622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0));
v___f_623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4));
v___f_624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5));
lean_inc_ref(v_toFunctor_615_);
v___f_625_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_625_, 0, v_toFunctor_615_);
v___f_626_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_626_, 0, v_toFunctor_615_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___f_625_);
lean_ctor_set(v___x_627_, 1, v___f_626_);
v___f_628_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_628_, 0, v_toSeqRight_618_);
v___f_629_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_629_, 0, v_toSeqLeft_617_);
v___f_630_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_630_, 0, v_toSeq_616_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 4, v___f_628_);
lean_ctor_set(v___x_620_, 3, v___f_629_);
lean_ctor_set(v___x_620_, 2, v___f_630_);
lean_ctor_set(v___x_620_, 1, v___f_623_);
lean_ctor_set(v___x_620_, 0, v___x_627_);
v___x_632_ = v___x_620_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___f_623_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v___f_630_);
lean_ctor_set(v_reuseFailAlloc_640_, 3, v___f_629_);
lean_ctor_set(v_reuseFailAlloc_640_, 4, v___f_628_);
v___x_632_ = v_reuseFailAlloc_640_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_634_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___f_624_);
lean_ctor_set(v___x_613_, 0, v___x_632_);
v___x_634_ = v___x_613_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___f_624_);
v___x_634_ = v_reuseFailAlloc_639_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v___f_636_; lean_object* v___x_622__overap_637_; lean_object* v___x_638_; 
v___x_635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
lean_inc(v_mvarId_569_);
v___f_636_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_636_, 0, v_mvarId_569_);
lean_closure_set(v___f_636_, 1, v___x_635_);
lean_closure_set(v___f_636_, 2, v_mkName_571_);
lean_closure_set(v___f_636_, 3, v_n_570_);
lean_closure_set(v___f_636_, 4, v_s_572_);
lean_closure_set(v___f_636_, 5, v___f_622_);
v___x_622__overap_637_ = l_Lean_MVarId_withContext___redArg(v___x_596_, v___x_634_, v_mvarId_569_, v___f_636_);
lean_inc(v_a_576_);
lean_inc_ref(v_a_575_);
lean_inc(v_a_574_);
lean_inc_ref(v_a_573_);
v___x_638_ = lean_apply_5(v___x_622__overap_637_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, lean_box(0));
return v___x_638_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_569_ = stack[1].m_obj;
lean_object* v_n_570_ = stack[2].m_obj;
lean_object* v_mkName_571_ = stack[3].m_obj;
lean_object* v_s_572_ = stack[4].m_obj;
lean_object* v_a_573_ = stack[5].m_obj;
lean_object* v_a_574_ = stack[6].m_obj;
lean_object* v_a_575_ = stack[7].m_obj;
lean_object* v_a_576_ = stack[8].m_obj;
lean_object* v_res_645_;
v_res_645_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(lean_box(0), v_mvarId_569_, v_n_570_, v_mkName_571_, v_s_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
stack->m_obj
 = v_res_645_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___boxed(lean_object* v_00_u03c3_646_, lean_object* v_mvarId_647_, lean_object* v_n_648_, lean_object* v_mkName_649_, lean_object* v_s_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(v_00_u03c3_646_, v_mvarId_647_, v_n_648_, v_mkName_649_, v_s_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
return v_res_656_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(lean_object* v_name_657_, lean_object* v_decl_658_, lean_object* v_ref_659_){
_start:
{
lean_object* v_defValue_661_; lean_object* v_descr_662_; lean_object* v_deprecation_x3f_663_; lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_defValue_661_ = lean_ctor_get(v_decl_658_, 0);
v_descr_662_ = lean_ctor_get(v_decl_658_, 1);
v_deprecation_x3f_663_ = lean_ctor_get(v_decl_658_, 2);
v___x_664_ = lean_alloc_ctor(1, 0, 1);
v___x_665_ = lean_unbox(v_defValue_661_);
lean_ctor_set_uint8(v___x_664_, 0, v___x_665_);
lean_inc(v_deprecation_x3f_663_);
lean_inc_ref(v_descr_662_);
lean_inc_n(v_name_657_, 2);
v___x_666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_666_, 0, v_name_657_);
lean_ctor_set(v___x_666_, 1, v_ref_659_);
lean_ctor_set(v___x_666_, 2, v___x_664_);
lean_ctor_set(v___x_666_, 3, v_descr_662_);
lean_ctor_set(v___x_666_, 4, v_deprecation_x3f_663_);
v___x_667_ = lean_register_option(v_name_657_, v___x_666_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_675_; 
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; 
v_unused_676_ = lean_ctor_get(v___x_667_, 0);
lean_dec(v_unused_676_);
v___x_669_ = v___x_667_;
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
else
{
lean_dec(v___x_667_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
lean_inc(v_defValue_661_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v_name_657_);
lean_ctor_set(v___x_671_, 1, v_defValue_661_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_671_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec(v_name_657_);
v_a_677_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_667_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_667_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_657_ = stack[0].m_obj;
lean_object* v_decl_658_ = stack[1].m_obj;
lean_object* v_ref_659_ = stack[2].m_obj;
lean_object* v_res_685_;
v_res_685_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(v_name_657_, v_decl_658_, v_ref_659_);
stack->m_obj
 = v_res_685_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_686_, lean_object* v_decl_687_, lean_object* v_ref_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(v_name_686_, v_decl_687_, v_ref_688_);
lean_dec_ref(v_decl_687_);
return v_res_690_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_));
v___x_711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_));
v___x_712_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_));
v___x_713_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(v___x_710_, v___x_711_, v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_714_;
v_res_714_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_();
stack->m_obj
 = v_res_714_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4____boxed(lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_();
return v_res_716_;
}
}
lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(lean_object* v_lctx_717_, lean_object* v_binderName_718_, uint8_t v_hygienic_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
if (v_hygienic_719_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = l_Lean_LocalContext_getUnusedName(v_lctx_717_, v_binderName_718_);
lean_dec(v_binderName_718_);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
else
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Core_mkFreshUserName(v_binderName_718_, v_a_720_, v_a_721_);
return v___x_725_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_717_ = stack[0].m_obj;
lean_object* v_binderName_718_ = stack[1].m_obj;
uint8_t v_hygienic_719_ = stack[2].m_num;
lean_object* v_a_720_ = stack[3].m_obj;
lean_object* v_a_721_ = stack[4].m_obj;
lean_object* v_res_726_;
v_res_726_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_717_, v_binderName_718_, v_hygienic_719_, v_a_720_, v_a_721_);
stack->m_obj
 = v_res_726_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg___boxed(lean_object* v_lctx_727_, lean_object* v_binderName_728_, lean_object* v_hygienic_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
uint8_t v_hygienic_boxed_733_; lean_object* v_res_734_; 
v_hygienic_boxed_733_ = lean_unbox(v_hygienic_729_);
v_res_734_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_727_, v_binderName_728_, v_hygienic_boxed_733_, v_a_730_, v_a_731_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec_ref(v_lctx_727_);
return v_res_734_;
}
}
lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore(lean_object* v_lctx_735_, lean_object* v_binderName_736_, uint8_t v_hygienic_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_735_, v_binderName_736_, v_hygienic_737_, v_a_740_, v_a_741_);
return v___x_743_;
}
}
LEAN_EXPORT void l_Lean_Meta_mkFreshBinderNameForTacticCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_735_ = stack[0].m_obj;
lean_object* v_binderName_736_ = stack[1].m_obj;
uint8_t v_hygienic_737_ = stack[2].m_num;
lean_object* v_a_738_ = stack[3].m_obj;
lean_object* v_a_739_ = stack[4].m_obj;
lean_object* v_a_740_ = stack[5].m_obj;
lean_object* v_a_741_ = stack[6].m_obj;
lean_object* v_res_744_;
v_res_744_ = l_Lean_Meta_mkFreshBinderNameForTacticCore(v_lctx_735_, v_binderName_736_, v_hygienic_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
stack->m_obj
 = v_res_744_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore___boxed(lean_object* v_lctx_745_, lean_object* v_binderName_746_, lean_object* v_hygienic_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
uint8_t v_hygienic_boxed_753_; lean_object* v_res_754_; 
v_hygienic_boxed_753_ = lean_unbox(v_hygienic_747_);
v_res_754_ = l_Lean_Meta_mkFreshBinderNameForTacticCore(v_lctx_745_, v_binderName_746_, v_hygienic_boxed_753_, v_a_748_, v_a_749_, v_a_750_, v_a_751_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec_ref(v_lctx_745_);
return v_res_754_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(lean_object* v_opts_755_, lean_object* v_opt_756_){
_start:
{
lean_object* v_name_757_; lean_object* v_defValue_758_; lean_object* v_map_759_; lean_object* v___x_760_; 
v_name_757_ = lean_ctor_get(v_opt_756_, 0);
v_defValue_758_ = lean_ctor_get(v_opt_756_, 1);
v_map_759_ = lean_ctor_get(v_opts_755_, 0);
v___x_760_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_759_, v_name_757_);
if (lean_obj_tag(v___x_760_) == 0)
{
uint8_t v___x_761_; 
v___x_761_ = lean_unbox(v_defValue_758_);
return v___x_761_;
}
else
{
lean_object* v_val_762_; 
v_val_762_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_val_762_);
lean_dec_ref_known(v___x_760_, 1);
if (lean_obj_tag(v_val_762_) == 1)
{
uint8_t v_v_763_; 
v_v_763_ = lean_ctor_get_uint8(v_val_762_, 0);
lean_dec_ref_known(v_val_762_, 0);
return v_v_763_;
}
else
{
uint8_t v___x_764_; 
lean_dec(v_val_762_);
v___x_764_ = lean_unbox(v_defValue_758_);
return v___x_764_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_755_ = stack[0].m_obj;
lean_object* v_opt_756_ = stack[1].m_obj;
uint8_t v_res_765_;
v_res_765_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v_opts_755_, v_opt_756_);
stack->m_num = v_res_765_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0___boxed(lean_object* v_opts_766_, lean_object* v_opt_767_){
_start:
{
uint8_t v_res_768_; lean_object* v_r_769_; 
v_res_768_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v_opts_766_, v_opt_767_);
lean_dec_ref(v_opt_767_);
lean_dec_ref(v_opts_766_);
v_r_769_ = lean_box(v_res_768_);
return v_r_769_;
}
}
lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg(lean_object* v_binderName_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_lctx_775_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; 
v_lctx_775_ = lean_ctor_get(v_a_771_, 2);
v___x_776_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_772_);
v___x_777_ = l_Lean_Meta_tactic_hygienic;
v___x_778_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v___x_776_, v___x_777_);
lean_dec_ref(v___x_776_);
v___x_779_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_775_, v_binderName_770_, v___x_778_, v_a_772_, v_a_773_);
return v___x_779_;
}
}
LEAN_EXPORT void l_Lean_Meta_mkFreshBinderNameForTactic___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderName_770_ = stack[0].m_obj;
lean_object* v_a_771_ = stack[1].m_obj;
lean_object* v_a_772_ = stack[2].m_obj;
lean_object* v_a_773_ = stack[3].m_obj;
lean_object* v_res_780_;
v_res_780_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_binderName_770_, v_a_771_, v_a_772_, v_a_773_);
stack->m_obj
 = v_res_780_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg___boxed(lean_object* v_binderName_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_binderName_781_, v_a_782_, v_a_783_, v_a_784_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec_ref(v_a_782_);
return v_res_786_;
}
}
lean_object* l_Lean_Meta_mkFreshBinderNameForTactic(lean_object* v_binderName_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_binderName_787_, v_a_788_, v_a_790_, v_a_791_);
return v___x_793_;
}
}
LEAN_EXPORT void l_Lean_Meta_mkFreshBinderNameForTactic_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderName_787_ = stack[0].m_obj;
lean_object* v_a_788_ = stack[1].m_obj;
lean_object* v_a_789_ = stack[2].m_obj;
lean_object* v_a_790_ = stack[3].m_obj;
lean_object* v_a_791_ = stack[4].m_obj;
lean_object* v_res_794_;
v_res_794_ = l_Lean_Meta_mkFreshBinderNameForTactic(v_binderName_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
stack->m_obj
 = v_res_794_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___boxed(lean_object* v_binderName_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_Meta_mkFreshBinderNameForTactic(v_binderName_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
return v_res_801_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(uint8_t v_preserveBinderNames_805_, uint8_t v_hygienic_806_, lean_object* v_lctx_807_, lean_object* v_binderName_808_, lean_object* v_rest_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_binderName_814_; lean_object* v___y_815_; lean_object* v___y_816_; uint8_t v___x_837_; 
v___x_837_ = l_Lean_Name_isAnonymous(v_binderName_808_);
if (v___x_837_ == 0)
{
v_binderName_814_ = v_binderName_808_;
v___y_815_ = v_a_810_;
v___y_816_ = v_a_811_;
goto v___jp_813_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec(v_binderName_808_);
v___x_838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__1));
v___x_839_ = l_Lean_Core_mkFreshUserName(v___x_838_, v_a_810_, v_a_811_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
v_binderName_814_ = v_a_840_;
v___y_815_ = v_a_810_;
v___y_816_ = v_a_811_;
goto v___jp_813_;
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec(v_rest_809_);
v_a_841_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_839_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_839_);
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
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
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
v___jp_813_:
{
if (v_preserveBinderNames_805_ == 0)
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_807_, v_binderName_814_, v_hygienic_806_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_826_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_826_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_826_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_826_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v_a_818_);
lean_ctor_set(v___x_822_, 1, v_rest_809_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_822_);
v___x_824_ = v___x_820_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_rest_809_);
v_a_827_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_817_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_817_);
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
else
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v_binderName_814_);
lean_ctor_set(v___x_835_, 1, v_rest_809_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_preserveBinderNames_805_ = stack[0].m_num;
uint8_t v_hygienic_806_ = stack[1].m_num;
lean_object* v_lctx_807_ = stack[2].m_obj;
lean_object* v_binderName_808_ = stack[3].m_obj;
lean_object* v_rest_809_ = stack[4].m_obj;
lean_object* v_a_810_ = stack[5].m_obj;
lean_object* v_a_811_ = stack[6].m_obj;
lean_object* v_res_849_;
v_res_849_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_805_, v_hygienic_806_, v_lctx_807_, v_binderName_808_, v_rest_809_, v_a_810_, v_a_811_);
stack->m_obj
 = v_res_849_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___boxed(lean_object* v_preserveBinderNames_850_, lean_object* v_hygienic_851_, lean_object* v_lctx_852_, lean_object* v_binderName_853_, lean_object* v_rest_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
uint8_t v_preserveBinderNames_boxed_858_; uint8_t v_hygienic_boxed_859_; lean_object* v_res_860_; 
v_preserveBinderNames_boxed_858_ = lean_unbox(v_preserveBinderNames_850_);
v_hygienic_boxed_859_ = lean_unbox(v_hygienic_851_);
v_res_860_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_boxed_858_, v_hygienic_boxed_859_, v_lctx_852_, v_binderName_853_, v_rest_854_, v_a_855_, v_a_856_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec_ref(v_lctx_852_);
return v_res_860_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(uint8_t v_preserveBinderNames_861_, uint8_t v_hygienic_862_, lean_object* v_lctx_863_, lean_object* v_binderName_864_, lean_object* v_rest_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_861_, v_hygienic_862_, v_lctx_863_, v_binderName_864_, v_rest_865_, v_a_868_, v_a_869_);
return v___x_871_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName_0interp(lean_interpreter_value* stack)
{
uint8_t v_preserveBinderNames_861_ = stack[0].m_num;
uint8_t v_hygienic_862_ = stack[1].m_num;
lean_object* v_lctx_863_ = stack[2].m_obj;
lean_object* v_binderName_864_ = stack[3].m_obj;
lean_object* v_rest_865_ = stack[4].m_obj;
lean_object* v_a_866_ = stack[5].m_obj;
lean_object* v_a_867_ = stack[6].m_obj;
lean_object* v_a_868_ = stack[7].m_obj;
lean_object* v_a_869_ = stack[8].m_obj;
lean_object* v_res_872_;
v_res_872_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(v_preserveBinderNames_861_, v_hygienic_862_, v_lctx_863_, v_binderName_864_, v_rest_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
stack->m_obj
 = v_res_872_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___boxed(lean_object* v_preserveBinderNames_873_, lean_object* v_hygienic_874_, lean_object* v_lctx_875_, lean_object* v_binderName_876_, lean_object* v_rest_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
uint8_t v_preserveBinderNames_boxed_883_; uint8_t v_hygienic_boxed_884_; lean_object* v_res_885_; 
v_preserveBinderNames_boxed_883_ = lean_unbox(v_preserveBinderNames_873_);
v_hygienic_boxed_884_ = lean_unbox(v_hygienic_874_);
v_res_885_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(v_preserveBinderNames_boxed_883_, v_hygienic_boxed_884_, v_lctx_875_, v_binderName_876_, v_rest_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec_ref(v_lctx_875_);
return v_res_885_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(uint8_t v_preserveBinderNames_890_, uint8_t v_hygienic_891_, uint8_t v_useNamesForExplicitOnly_892_, lean_object* v_lctx_893_, lean_object* v_binderName_894_, uint8_t v_isExplicit_895_, lean_object* v_x_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
if (lean_obj_tag(v_x_896_) == 0)
{
lean_object* v___x_900_; 
v___x_900_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_890_, v_hygienic_891_, v_lctx_893_, v_binderName_894_, v_x_896_, v_a_897_, v_a_898_);
return v___x_900_;
}
else
{
lean_object* v_head_901_; lean_object* v_tail_902_; 
v_head_901_ = lean_ctor_get(v_x_896_, 0);
v_tail_902_ = lean_ctor_get(v_x_896_, 1);
if (v_useNamesForExplicitOnly_892_ == 0)
{
lean_inc(v_tail_902_);
lean_inc(v_head_901_);
lean_dec_ref_known(v_x_896_, 2);
goto v___jp_903_;
}
else
{
if (v_isExplicit_895_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_890_, v_hygienic_891_, v_lctx_893_, v_binderName_894_, v_x_896_, v_a_897_, v_a_898_);
return v___x_909_;
}
else
{
lean_inc(v_tail_902_);
lean_inc(v_head_901_);
lean_dec_ref_known(v_x_896_, 2);
goto v___jp_903_;
}
}
v___jp_903_:
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__1));
v___x_905_ = lean_name_eq(v_head_901_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; 
lean_dec(v_binderName_894_);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v_head_901_);
lean_ctor_set(v___x_906_, 1, v_tail_902_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
else
{
lean_object* v___x_908_; 
lean_dec(v_head_901_);
v___x_908_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_890_, v_hygienic_891_, v_lctx_893_, v_binderName_894_, v_tail_902_, v_a_897_, v_a_898_);
return v___x_908_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_preserveBinderNames_890_ = stack[0].m_num;
uint8_t v_hygienic_891_ = stack[1].m_num;
uint8_t v_useNamesForExplicitOnly_892_ = stack[2].m_num;
lean_object* v_lctx_893_ = stack[3].m_obj;
lean_object* v_binderName_894_ = stack[4].m_obj;
uint8_t v_isExplicit_895_ = stack[5].m_num;
lean_object* v_x_896_ = stack[6].m_obj;
lean_object* v_a_897_ = stack[7].m_obj;
lean_object* v_a_898_ = stack[8].m_obj;
lean_object* v_res_910_;
v_res_910_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_890_, v_hygienic_891_, v_useNamesForExplicitOnly_892_, v_lctx_893_, v_binderName_894_, v_isExplicit_895_, v_x_896_, v_a_897_, v_a_898_);
stack->m_obj
 = v_res_910_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___boxed(lean_object* v_preserveBinderNames_911_, lean_object* v_hygienic_912_, lean_object* v_useNamesForExplicitOnly_913_, lean_object* v_lctx_914_, lean_object* v_binderName_915_, lean_object* v_isExplicit_916_, lean_object* v_x_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
uint8_t v_preserveBinderNames_boxed_921_; uint8_t v_hygienic_boxed_922_; uint8_t v_useNamesForExplicitOnly_boxed_923_; uint8_t v_isExplicit_boxed_924_; lean_object* v_res_925_; 
v_preserveBinderNames_boxed_921_ = lean_unbox(v_preserveBinderNames_911_);
v_hygienic_boxed_922_ = lean_unbox(v_hygienic_912_);
v_useNamesForExplicitOnly_boxed_923_ = lean_unbox(v_useNamesForExplicitOnly_913_);
v_isExplicit_boxed_924_ = lean_unbox(v_isExplicit_916_);
v_res_925_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_boxed_921_, v_hygienic_boxed_922_, v_useNamesForExplicitOnly_boxed_923_, v_lctx_914_, v_binderName_915_, v_isExplicit_boxed_924_, v_x_917_, v_a_918_, v_a_919_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec_ref(v_lctx_914_);
return v_res_925_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(uint8_t v_preserveBinderNames_926_, uint8_t v_hygienic_927_, uint8_t v_useNamesForExplicitOnly_928_, lean_object* v_lctx_929_, lean_object* v_binderName_930_, uint8_t v_isExplicit_931_, lean_object* v_x_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_926_, v_hygienic_927_, v_useNamesForExplicitOnly_928_, v_lctx_929_, v_binderName_930_, v_isExplicit_931_, v_x_932_, v_a_935_, v_a_936_);
return v___x_938_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_0interp(lean_interpreter_value* stack)
{
uint8_t v_preserveBinderNames_926_ = stack[0].m_num;
uint8_t v_hygienic_927_ = stack[1].m_num;
uint8_t v_useNamesForExplicitOnly_928_ = stack[2].m_num;
lean_object* v_lctx_929_ = stack[3].m_obj;
lean_object* v_binderName_930_ = stack[4].m_obj;
uint8_t v_isExplicit_931_ = stack[5].m_num;
lean_object* v_x_932_ = stack[6].m_obj;
lean_object* v_a_933_ = stack[7].m_obj;
lean_object* v_a_934_ = stack[8].m_obj;
lean_object* v_a_935_ = stack[9].m_obj;
lean_object* v_a_936_ = stack[10].m_obj;
lean_object* v_res_939_;
v_res_939_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(v_preserveBinderNames_926_, v_hygienic_927_, v_useNamesForExplicitOnly_928_, v_lctx_929_, v_binderName_930_, v_isExplicit_931_, v_x_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
stack->m_obj
 = v_res_939_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___boxed(lean_object* v_preserveBinderNames_940_, lean_object* v_hygienic_941_, lean_object* v_useNamesForExplicitOnly_942_, lean_object* v_lctx_943_, lean_object* v_binderName_944_, lean_object* v_isExplicit_945_, lean_object* v_x_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
uint8_t v_preserveBinderNames_boxed_952_; uint8_t v_hygienic_boxed_953_; uint8_t v_useNamesForExplicitOnly_boxed_954_; uint8_t v_isExplicit_boxed_955_; lean_object* v_res_956_; 
v_preserveBinderNames_boxed_952_ = lean_unbox(v_preserveBinderNames_940_);
v_hygienic_boxed_953_ = lean_unbox(v_hygienic_941_);
v_useNamesForExplicitOnly_boxed_954_ = lean_unbox(v_useNamesForExplicitOnly_942_);
v_isExplicit_boxed_955_ = lean_unbox(v_isExplicit_945_);
v_res_956_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(v_preserveBinderNames_boxed_952_, v_hygienic_boxed_953_, v_useNamesForExplicitOnly_boxed_954_, v_lctx_943_, v_binderName_944_, v_isExplicit_boxed_955_, v_x_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec_ref(v_lctx_943_);
return v_res_956_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(lean_object* v_mvarId_957_, lean_object* v_x_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_957_, v_x_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v_a_973_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_964_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_964_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_957_ = stack[0].m_obj;
lean_object* v_x_958_ = stack[1].m_obj;
lean_object* v___y_959_ = stack[2].m_obj;
lean_object* v___y_960_ = stack[3].m_obj;
lean_object* v___y_961_ = stack[4].m_obj;
lean_object* v___y_962_ = stack[5].m_obj;
lean_object* v_res_981_;
v_res_981_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_957_, v_x_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
stack->m_obj
 = v_res_981_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg___boxed(lean_object* v_mvarId_982_, lean_object* v_x_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_982_, v_x_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_989_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(lean_object* v_00_u03b1_990_, lean_object* v_mvarId_991_, lean_object* v_x_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_991_, v_x_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
return v___x_998_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_991_ = stack[1].m_obj;
lean_object* v_x_992_ = stack[2].m_obj;
lean_object* v___y_993_ = stack[3].m_obj;
lean_object* v___y_994_ = stack[4].m_obj;
lean_object* v___y_995_ = stack[5].m_obj;
lean_object* v___y_996_ = stack[6].m_obj;
lean_object* v_res_999_;
v_res_999_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(lean_box(0), v_mvarId_991_, v_x_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
stack->m_obj
 = v_res_999_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___boxed(lean_object* v_00_u03b1_1000_, lean_object* v_mvarId_1001_, lean_object* v_x_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(v_00_u03b1_1000_, v_mvarId_1001_, v_x_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
return v_res_1008_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(size_t v_sz_1009_, size_t v_i_1010_, lean_object* v_bs_1011_){
_start:
{
uint8_t v___x_1012_; 
v___x_1012_ = lean_usize_dec_lt(v_i_1010_, v_sz_1009_);
if (v___x_1012_ == 0)
{
return v_bs_1011_;
}
else
{
lean_object* v_v_1013_; lean_object* v___x_1014_; lean_object* v_bs_x27_1015_; lean_object* v___x_1016_; size_t v___x_1017_; size_t v___x_1018_; lean_object* v___x_1019_; 
v_v_1013_ = lean_array_uget(v_bs_1011_, v_i_1010_);
v___x_1014_ = lean_unsigned_to_nat(0u);
v_bs_x27_1015_ = lean_array_uset(v_bs_1011_, v_i_1010_, v___x_1014_);
v___x_1016_ = l_Lean_Expr_fvarId_x21(v_v_1013_);
lean_dec(v_v_1013_);
v___x_1017_ = ((size_t)1ULL);
v___x_1018_ = lean_usize_add(v_i_1010_, v___x_1017_);
v___x_1019_ = lean_array_uset(v_bs_x27_1015_, v_i_1010_, v___x_1016_);
v_i_1010_ = v___x_1018_;
v_bs_1011_ = v___x_1019_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1009_ = stack[0].m_num;
size_t v_i_1010_ = stack[1].m_num;
lean_object* v_bs_1011_ = stack[2].m_obj;
lean_object* v_res_1021_;
v_res_1021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(v_sz_1009_, v_i_1010_, v_bs_1011_);
stack->m_obj
 = v_res_1021_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1___boxed(lean_object* v_sz_1022_, lean_object* v_i_1023_, lean_object* v_bs_1024_){
_start:
{
size_t v_sz_boxed_1025_; size_t v_i_boxed_1026_; lean_object* v_res_1027_; 
v_sz_boxed_1025_ = lean_unbox_usize(v_sz_1022_);
lean_dec(v_sz_1022_);
v_i_boxed_1026_ = lean_unbox_usize(v_i_1023_);
lean_dec(v_i_1023_);
v_res_1027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(v_sz_boxed_1025_, v_i_boxed_1026_, v_bs_1024_);
return v_res_1027_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(lean_object* v_e_1028_, lean_object* v___y_1029_){
_start:
{
uint8_t v___x_1031_; 
v___x_1031_ = l_Lean_Expr_hasMVar(v_e_1028_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v_e_1028_);
return v___x_1032_;
}
else
{
lean_object* v___x_1033_; lean_object* v_mctx_1034_; lean_object* v___x_1035_; lean_object* v_fst_1036_; lean_object* v_snd_1037_; lean_object* v___x_1038_; lean_object* v_cache_1039_; lean_object* v_zetaDeltaFVarIds_1040_; lean_object* v_postponed_1041_; lean_object* v_diag_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1051_; 
v___x_1033_ = lean_st_ref_get(v___y_1029_);
v_mctx_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc_ref(v_mctx_1034_);
lean_dec(v___x_1033_);
v___x_1035_ = l_Lean_instantiateMVarsCore(v_mctx_1034_, v_e_1028_);
v_fst_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_fst_1036_);
v_snd_1037_ = lean_ctor_get(v___x_1035_, 1);
lean_inc(v_snd_1037_);
lean_dec_ref(v___x_1035_);
v___x_1038_ = lean_st_ref_take(v___y_1029_);
v_cache_1039_ = lean_ctor_get(v___x_1038_, 1);
v_zetaDeltaFVarIds_1040_ = lean_ctor_get(v___x_1038_, 2);
v_postponed_1041_ = lean_ctor_get(v___x_1038_, 3);
v_diag_1042_ = lean_ctor_get(v___x_1038_, 4);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; 
v_unused_1052_ = lean_ctor_get(v___x_1038_, 0);
lean_dec(v_unused_1052_);
v___x_1044_ = v___x_1038_;
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_diag_1042_);
lean_inc(v_postponed_1041_);
lean_inc(v_zetaDeltaFVarIds_1040_);
lean_inc(v_cache_1039_);
lean_dec(v___x_1038_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v_snd_1037_);
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_snd_1037_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_cache_1039_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_zetaDeltaFVarIds_1040_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v_postponed_1041_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v_diag_1042_);
v___x_1047_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_st_ref_put(v___y_1029_, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v_fst_1036_);
return v___x_1049_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1028_ = stack[0].m_obj;
lean_object* v___y_1029_ = stack[1].m_obj;
lean_object* v_res_1053_;
v_res_1053_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_1028_, v___y_1029_);
stack->m_obj
 = v_res_1053_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg___boxed(lean_object* v_e_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_1054_, v___y_1055_);
lean_dec(v___y_1055_);
return v_res_1057_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; lean_object* v_ngen_1061_; lean_object* v_namePrefix_1062_; lean_object* v_idx_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1093_; 
v___x_1060_ = lean_st_ref_get(v___y_1058_);
v_ngen_1061_ = lean_ctor_get(v___x_1060_, 2);
lean_inc_ref(v_ngen_1061_);
lean_dec(v___x_1060_);
v_namePrefix_1062_ = lean_ctor_get(v_ngen_1061_, 0);
v_idx_1063_ = lean_ctor_get(v_ngen_1061_, 1);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_ngen_1061_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1065_ = v_ngen_1061_;
v_isShared_1066_ = v_isSharedCheck_1093_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_idx_1063_);
lean_inc(v_namePrefix_1062_);
lean_dec(v_ngen_1061_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1093_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v_r_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
lean_inc(v_idx_1063_);
lean_inc(v_namePrefix_1062_);
v_r_1067_ = l_Lean_Name_num___override(v_namePrefix_1062_, v_idx_1063_);
v___x_1068_ = lean_unsigned_to_nat(1u);
v___x_1069_ = lean_nat_add(v_idx_1063_, v___x_1068_);
lean_dec(v_idx_1063_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 1, v___x_1069_);
v___x_1071_ = v___x_1065_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_namePrefix_1062_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v_env_1073_; lean_object* v_nextMacroScope_1074_; lean_object* v_auxDeclNGen_1075_; lean_object* v_traceState_1076_; lean_object* v_cache_1077_; lean_object* v_recordedDeps_1078_; lean_object* v_messages_1079_; lean_object* v_infoState_1080_; lean_object* v_snapshotTasks_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1090_; 
v___x_1072_ = lean_st_ref_take(v___y_1058_);
v_env_1073_ = lean_ctor_get(v___x_1072_, 0);
v_nextMacroScope_1074_ = lean_ctor_get(v___x_1072_, 1);
v_auxDeclNGen_1075_ = lean_ctor_get(v___x_1072_, 3);
v_traceState_1076_ = lean_ctor_get(v___x_1072_, 4);
v_cache_1077_ = lean_ctor_get(v___x_1072_, 5);
v_recordedDeps_1078_ = lean_ctor_get(v___x_1072_, 6);
v_messages_1079_ = lean_ctor_get(v___x_1072_, 7);
v_infoState_1080_ = lean_ctor_get(v___x_1072_, 8);
v_snapshotTasks_1081_ = lean_ctor_get(v___x_1072_, 9);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v___x_1072_, 2);
lean_dec(v_unused_1091_);
v___x_1083_ = v___x_1072_;
v_isShared_1084_ = v_isSharedCheck_1090_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_snapshotTasks_1081_);
lean_inc(v_infoState_1080_);
lean_inc(v_messages_1079_);
lean_inc(v_recordedDeps_1078_);
lean_inc(v_cache_1077_);
lean_inc(v_traceState_1076_);
lean_inc(v_auxDeclNGen_1075_);
lean_inc(v_nextMacroScope_1074_);
lean_inc(v_env_1073_);
lean_dec(v___x_1072_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1090_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 2, v___x_1071_);
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_env_1073_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_nextMacroScope_1074_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_auxDeclNGen_1075_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v_traceState_1076_);
lean_ctor_set(v_reuseFailAlloc_1089_, 5, v_cache_1077_);
lean_ctor_set(v_reuseFailAlloc_1089_, 6, v_recordedDeps_1078_);
lean_ctor_set(v_reuseFailAlloc_1089_, 7, v_messages_1079_);
lean_ctor_set(v_reuseFailAlloc_1089_, 8, v_infoState_1080_);
lean_ctor_set(v_reuseFailAlloc_1089_, 9, v_snapshotTasks_1081_);
v___x_1086_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_st_ref_put(v___y_1058_, v___x_1086_);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_r_1067_);
return v___x_1088_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1058_ = stack[0].m_obj;
lean_object* v_res_1094_;
v_res_1094_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1058_);
stack->m_obj
 = v_res_1094_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1095_);
lean_dec(v___y_1095_);
return v_res_1097_;
}
}
lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___x_1103_; lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v___x_1103_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1101_);
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1098_ = stack[0].m_obj;
lean_object* v___y_1099_ = stack[1].m_obj;
lean_object* v___y_1100_ = stack[2].m_obj;
lean_object* v___y_1101_ = stack[3].m_obj;
lean_object* v_res_1112_;
v_res_1112_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
stack->m_obj
 = v_res_1112_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3___boxed(lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
return v_res_1118_;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(lean_object* v_fvars_1119_, lean_object* v_j_1120_, lean_object* v_x_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp(lean_box(0), v_fvars_1119_, v_j_1120_, v_x_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
v_a_1136_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1127_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1127_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1119_ = stack[0].m_obj;
lean_object* v_j_1120_ = stack[1].m_obj;
lean_object* v_x_1121_ = stack[2].m_obj;
lean_object* v___y_1122_ = stack[3].m_obj;
lean_object* v___y_1123_ = stack[4].m_obj;
lean_object* v___y_1124_ = stack[5].m_obj;
lean_object* v___y_1125_ = stack[6].m_obj;
lean_object* v_res_1144_;
v_res_1144_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1119_, v_j_1120_, v_x_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
stack->m_obj
 = v_res_1144_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_fvars_1145_, lean_object* v_j_1146_, lean_object* v_x_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1145_, v_j_1146_, v_x_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1153_;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(lean_object* v_fvars_1154_, lean_object* v_j_1155_, lean_object* v_x_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1154_, v_j_1155_, v_x_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
v_a_1171_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1162_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1162_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1154_ = stack[0].m_obj;
lean_object* v_j_1155_ = stack[1].m_obj;
lean_object* v_x_1156_ = stack[2].m_obj;
lean_object* v___y_1157_ = stack[3].m_obj;
lean_object* v___y_1158_ = stack[4].m_obj;
lean_object* v___y_1159_ = stack[5].m_obj;
lean_object* v___y_1160_ = stack[6].m_obj;
lean_object* v_res_1179_;
v_res_1179_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(v_fvars_1154_, v_j_1155_, v_x_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
stack->m_obj
 = v_res_1179_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg___boxed(lean_object* v_fvars_1180_, lean_object* v_j_1181_, lean_object* v_x_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(v_fvars_1180_, v_j_1181_, v_x_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
return v_res_1188_;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1(lean_object* v_00_u03b1_1189_, lean_object* v_fvars_1190_, lean_object* v_j_1191_, lean_object* v_x_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(v_fvars_1190_, v_j_1191_, v_x_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
return v___x_1198_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1190_ = stack[1].m_obj;
lean_object* v_j_1191_ = stack[2].m_obj;
lean_object* v_x_1192_ = stack[3].m_obj;
lean_object* v___y_1193_ = stack[4].m_obj;
lean_object* v___y_1194_ = stack[5].m_obj;
lean_object* v___y_1195_ = stack[6].m_obj;
lean_object* v___y_1196_ = stack[7].m_obj;
lean_object* v_res_1199_;
v_res_1199_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1(lean_box(0), v_fvars_1190_, v_j_1191_, v_x_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
stack->m_obj
 = v_res_1199_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1200_, lean_object* v_fvars_1201_, lean_object* v_j_1202_, lean_object* v_x_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1(v_00_u03b1_1200_, v_fvars_1201_, v_j_1202_, v_x_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(lean_object* v_x_1210_, lean_object* v_x_1211_, lean_object* v_x_1212_, lean_object* v_x_1213_){
_start:
{
lean_object* v_ks_1214_; lean_object* v_vs_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1239_; 
v_ks_1214_ = lean_ctor_get(v_x_1210_, 0);
v_vs_1215_ = lean_ctor_get(v_x_1210_, 1);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_x_1210_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1217_ = v_x_1210_;
v_isShared_1218_ = v_isSharedCheck_1239_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_vs_1215_);
lean_inc(v_ks_1214_);
lean_dec(v_x_1210_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1239_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = lean_array_get_size(v_ks_1214_);
v___x_1220_ = lean_nat_dec_lt(v_x_1211_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
lean_dec(v_x_1211_);
v___x_1221_ = lean_array_push(v_ks_1214_, v_x_1212_);
v___x_1222_ = lean_array_push(v_vs_1215_, v_x_1213_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v___x_1222_);
lean_ctor_set(v___x_1217_, 0, v___x_1221_);
v___x_1224_ = v___x_1217_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
else
{
lean_object* v_k_x27_1226_; uint8_t v___x_1227_; 
v_k_x27_1226_ = lean_array_fget_borrowed(v_ks_1214_, v_x_1211_);
v___x_1227_ = l_Lean_instBEqMVarId_beq(v_x_1212_, v_k_x27_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1229_; 
if (v_isShared_1218_ == 0)
{
v___x_1229_ = v___x_1217_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_ks_1214_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_vs_1215_);
v___x_1229_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = lean_nat_add(v_x_1211_, v___x_1230_);
lean_dec(v_x_1211_);
v_x_1210_ = v___x_1229_;
v_x_1211_ = v___x_1231_;
goto _start;
}
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1234_ = lean_array_fset(v_ks_1214_, v_x_1211_, v_x_1212_);
v___x_1235_ = lean_array_fset(v_vs_1215_, v_x_1211_, v_x_1213_);
lean_dec(v_x_1211_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v___x_1235_);
lean_ctor_set(v___x_1217_, 0, v___x_1234_);
v___x_1237_ = v___x_1217_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(lean_object* v_n_1240_, lean_object* v_k_1241_, lean_object* v_v_1242_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(v_n_1240_, v___x_1243_, v_k_1241_, v_v_1242_);
return v___x_1244_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1245_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_1246_, size_t v_x_1247_, size_t v_x_1248_, lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
if (lean_obj_tag(v_x_1246_) == 0)
{
lean_object* v_es_1251_; size_t v___x_1252_; size_t v___x_1253_; lean_object* v_j_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_es_1251_ = lean_ctor_get(v_x_1246_, 0);
v___x_1252_ = ((size_t)31ULL);
v___x_1253_ = lean_usize_land(v_x_1247_, v___x_1252_);
v_j_1254_ = lean_usize_to_nat(v___x_1253_);
v___x_1255_ = lean_array_get_size(v_es_1251_);
v___x_1256_ = lean_nat_dec_lt(v_j_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_dec(v_j_1254_);
lean_dec(v_x_1250_);
lean_dec(v_x_1249_);
return v_x_1246_;
}
else
{
lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1295_; 
lean_inc_ref(v_es_1251_);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_x_1246_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; 
v_unused_1296_ = lean_ctor_get(v_x_1246_, 0);
lean_dec(v_unused_1296_);
v___x_1258_ = v_x_1246_;
v_isShared_1259_ = v_isSharedCheck_1295_;
goto v_resetjp_1257_;
}
else
{
lean_dec(v_x_1246_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1295_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v_v_1260_; lean_object* v___x_1261_; lean_object* v_xs_x27_1262_; lean_object* v___y_1264_; 
v_v_1260_ = lean_array_fget(v_es_1251_, v_j_1254_);
v___x_1261_ = lean_box(0);
v_xs_x27_1262_ = lean_array_fset(v_es_1251_, v_j_1254_, v___x_1261_);
switch(lean_obj_tag(v_v_1260_))
{
case 0:
{
lean_object* v_key_1269_; lean_object* v_val_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1280_; 
v_key_1269_ = lean_ctor_get(v_v_1260_, 0);
v_val_1270_ = lean_ctor_get(v_v_1260_, 1);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_v_1260_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1272_ = v_v_1260_;
v_isShared_1273_ = v_isSharedCheck_1280_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_val_1270_);
lean_inc(v_key_1269_);
lean_dec(v_v_1260_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1280_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
uint8_t v___x_1274_; 
v___x_1274_ = l_Lean_instBEqMVarId_beq(v_x_1249_, v_key_1269_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_del_object(v___x_1272_);
v___x_1275_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1269_, v_val_1270_, v_x_1249_, v_x_1250_);
v___x_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
v___y_1264_ = v___x_1276_;
goto v___jp_1263_;
}
else
{
lean_object* v___x_1278_; 
lean_dec(v_val_1270_);
lean_dec(v_key_1269_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 1, v_x_1250_);
lean_ctor_set(v___x_1272_, 0, v_x_1249_);
v___x_1278_ = v___x_1272_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_x_1249_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_x_1250_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
v___y_1264_ = v___x_1278_;
goto v___jp_1263_;
}
}
}
}
case 1:
{
lean_object* v_node_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1293_; 
v_node_1281_ = lean_ctor_get(v_v_1260_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_v_1260_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1283_ = v_v_1260_;
v_isShared_1284_ = v_isSharedCheck_1293_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_node_1281_);
lean_dec(v_v_1260_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1293_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
size_t v___x_1285_; size_t v___x_1286_; size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1285_ = ((size_t)5ULL);
v___x_1286_ = lean_usize_shift_right(v_x_1247_, v___x_1285_);
v___x_1287_ = ((size_t)1ULL);
v___x_1288_ = lean_usize_add(v_x_1248_, v___x_1287_);
v___x_1289_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_node_1281_, v___x_1286_, v___x_1288_, v_x_1249_, v_x_1250_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1289_);
v___x_1291_ = v___x_1283_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
v___y_1264_ = v___x_1291_;
goto v___jp_1263_;
}
}
}
default: 
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v_x_1249_);
lean_ctor_set(v___x_1294_, 1, v_x_1250_);
v___y_1264_ = v___x_1294_;
goto v___jp_1263_;
}
}
v___jp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1265_ = lean_array_fset(v_xs_x27_1262_, v_j_1254_, v___y_1264_);
lean_dec(v_j_1254_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 0, v___x_1265_);
v___x_1267_ = v___x_1258_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
else
{
lean_object* v_ks_1297_; lean_object* v_vs_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1316_; 
v_ks_1297_ = lean_ctor_get(v_x_1246_, 0);
v_vs_1298_ = lean_ctor_get(v_x_1246_, 1);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_x_1246_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1300_ = v_x_1246_;
v_isShared_1301_ = v_isSharedCheck_1316_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_vs_1298_);
lean_inc(v_ks_1297_);
lean_dec(v_x_1246_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1316_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_ks_1297_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_vs_1298_);
v___x_1303_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v_newNode_1304_; size_t v___x_1305_; uint8_t v___x_1306_; 
v_newNode_1304_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(v___x_1303_, v_x_1249_, v_x_1250_);
v___x_1305_ = ((size_t)7ULL);
v___x_1306_ = lean_usize_dec_le(v___x_1305_, v_x_1248_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1307_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1304_);
v___x_1308_ = lean_unsigned_to_nat(4u);
v___x_1309_ = lean_nat_dec_lt(v___x_1307_, v___x_1308_);
lean_dec(v___x_1307_);
if (v___x_1309_ == 0)
{
lean_object* v_ks_1310_; lean_object* v_vs_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v_ks_1310_ = lean_ctor_get(v_newNode_1304_, 0);
lean_inc_ref(v_ks_1310_);
v_vs_1311_ = lean_ctor_get(v_newNode_1304_, 1);
lean_inc_ref(v_vs_1311_);
lean_dec_ref(v_newNode_1304_);
v___x_1312_ = lean_unsigned_to_nat(0u);
v___x_1313_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0);
v___x_1314_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_x_1248_, v_ks_1310_, v_vs_1311_, v___x_1312_, v___x_1313_);
lean_dec_ref(v_vs_1311_);
lean_dec_ref(v_ks_1310_);
return v___x_1314_;
}
else
{
return v_newNode_1304_;
}
}
else
{
return v_newNode_1304_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1246_ = stack[0].m_obj;
size_t v_x_1247_ = stack[1].m_num;
size_t v_x_1248_ = stack[2].m_num;
lean_object* v_x_1249_ = stack[3].m_obj;
lean_object* v_x_1250_ = stack[4].m_obj;
lean_object* v_res_1317_;
v_res_1317_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1246_, v_x_1247_, v_x_1248_, v_x_1249_, v_x_1250_);
stack->m_obj
 = v_res_1317_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(size_t v_depth_1318_, lean_object* v_keys_1319_, lean_object* v_vals_1320_, lean_object* v_i_1321_, lean_object* v_entries_1322_){
_start:
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = lean_array_get_size(v_keys_1319_);
v___x_1324_ = lean_nat_dec_lt(v_i_1321_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_dec(v_i_1321_);
return v_entries_1322_;
}
else
{
lean_object* v_k_1325_; lean_object* v_v_1326_; uint64_t v___x_1327_; size_t v_h_1328_; size_t v___x_1329_; lean_object* v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; size_t v___x_1333_; size_t v_h_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v_k_1325_ = lean_array_fget_borrowed(v_keys_1319_, v_i_1321_);
v_v_1326_ = lean_array_fget_borrowed(v_vals_1320_, v_i_1321_);
v___x_1327_ = l_Lean_instHashableMVarId_hash(v_k_1325_);
v_h_1328_ = lean_uint64_to_usize(v___x_1327_);
v___x_1329_ = ((size_t)5ULL);
v___x_1330_ = lean_unsigned_to_nat(1u);
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_sub(v_depth_1318_, v___x_1331_);
v___x_1333_ = lean_usize_mul(v___x_1329_, v___x_1332_);
v_h_1334_ = lean_usize_shift_right(v_h_1328_, v___x_1333_);
v___x_1335_ = lean_nat_add(v_i_1321_, v___x_1330_);
lean_dec(v_i_1321_);
lean_inc(v_v_1326_);
lean_inc(v_k_1325_);
v___x_1336_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_entries_1322_, v_h_1334_, v_depth_1318_, v_k_1325_, v_v_1326_);
v_i_1321_ = v___x_1335_;
v_entries_1322_ = v___x_1336_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1318_ = stack[0].m_num;
lean_object* v_keys_1319_ = stack[1].m_obj;
lean_object* v_vals_1320_ = stack[2].m_obj;
lean_object* v_i_1321_ = stack[3].m_obj;
lean_object* v_entries_1322_ = stack[4].m_obj;
lean_object* v_res_1338_;
v_res_1338_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_1318_, v_keys_1319_, v_vals_1320_, v_i_1321_, v_entries_1322_);
stack->m_obj
 = v_res_1338_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_depth_1339_, lean_object* v_keys_1340_, lean_object* v_vals_1341_, lean_object* v_i_1342_, lean_object* v_entries_1343_){
_start:
{
size_t v_depth_boxed_1344_; lean_object* v_res_1345_; 
v_depth_boxed_1344_ = lean_unbox_usize(v_depth_1339_);
lean_dec(v_depth_1339_);
v_res_1345_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_boxed_1344_, v_keys_1340_, v_vals_1341_, v_i_1342_, v_entries_1343_);
lean_dec_ref(v_vals_1341_);
lean_dec_ref(v_keys_1340_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_x_1346_, lean_object* v_x_1347_, lean_object* v_x_1348_, lean_object* v_x_1349_, lean_object* v_x_1350_){
_start:
{
size_t v_x_4088__boxed_1351_; size_t v_x_4089__boxed_1352_; lean_object* v_res_1353_; 
v_x_4088__boxed_1351_ = lean_unbox_usize(v_x_1347_);
lean_dec(v_x_1347_);
v_x_4089__boxed_1352_ = lean_unbox_usize(v_x_1348_);
lean_dec(v_x_1348_);
v_res_1353_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1346_, v_x_4088__boxed_1351_, v_x_4089__boxed_1352_, v_x_1349_, v_x_1350_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1354_, lean_object* v_x_1355_, lean_object* v_x_1356_){
_start:
{
uint64_t v___x_1357_; size_t v___x_1358_; size_t v___x_1359_; lean_object* v___x_1360_; 
v___x_1357_ = l_Lean_instHashableMVarId_hash(v_x_1355_);
v___x_1358_ = lean_uint64_to_usize(v___x_1357_);
v___x_1359_ = ((size_t)1ULL);
v___x_1360_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1354_, v___x_1358_, v___x_1359_, v_x_1355_, v_x_1356_);
return v___x_1360_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(lean_object* v_mvarId_1361_, lean_object* v_val_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___x_1365_; lean_object* v_mctx_1366_; lean_object* v_cache_1367_; lean_object* v_zetaDeltaFVarIds_1368_; lean_object* v_postponed_1369_; lean_object* v_diag_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1400_; 
v___x_1365_ = lean_st_ref_take(v___y_1363_);
v_mctx_1366_ = lean_ctor_get(v___x_1365_, 0);
v_cache_1367_ = lean_ctor_get(v___x_1365_, 1);
v_zetaDeltaFVarIds_1368_ = lean_ctor_get(v___x_1365_, 2);
v_postponed_1369_ = lean_ctor_get(v___x_1365_, 3);
v_diag_1370_ = lean_ctor_get(v___x_1365_, 4);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1372_ = v___x_1365_;
v_isShared_1373_ = v_isSharedCheck_1400_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_diag_1370_);
lean_inc(v_postponed_1369_);
lean_inc(v_zetaDeltaFVarIds_1368_);
lean_inc(v_cache_1367_);
lean_inc(v_mctx_1366_);
lean_dec(v___x_1365_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1400_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v_depth_1374_; lean_object* v_levelAssignDepth_1375_; lean_object* v_lmvarCounter_1376_; lean_object* v_mvarCounter_1377_; lean_object* v_lDecls_1378_; lean_object* v_decls_1379_; lean_object* v_userNames_1380_; lean_object* v_lAssignment_1381_; lean_object* v_eAssignment_1382_; lean_object* v_dAssignment_1383_; lean_object* v_instanceTypedMVars_1384_; lean_object* v_synthNormMemo_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1399_; 
v_depth_1374_ = lean_ctor_get(v_mctx_1366_, 0);
v_levelAssignDepth_1375_ = lean_ctor_get(v_mctx_1366_, 1);
v_lmvarCounter_1376_ = lean_ctor_get(v_mctx_1366_, 2);
v_mvarCounter_1377_ = lean_ctor_get(v_mctx_1366_, 3);
v_lDecls_1378_ = lean_ctor_get(v_mctx_1366_, 4);
v_decls_1379_ = lean_ctor_get(v_mctx_1366_, 5);
v_userNames_1380_ = lean_ctor_get(v_mctx_1366_, 6);
v_lAssignment_1381_ = lean_ctor_get(v_mctx_1366_, 7);
v_eAssignment_1382_ = lean_ctor_get(v_mctx_1366_, 8);
v_dAssignment_1383_ = lean_ctor_get(v_mctx_1366_, 9);
v_instanceTypedMVars_1384_ = lean_ctor_get(v_mctx_1366_, 10);
v_synthNormMemo_1385_ = lean_ctor_get(v_mctx_1366_, 11);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_mctx_1366_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1387_ = v_mctx_1366_;
v_isShared_1388_ = v_isSharedCheck_1399_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_synthNormMemo_1385_);
lean_inc(v_instanceTypedMVars_1384_);
lean_inc(v_dAssignment_1383_);
lean_inc(v_eAssignment_1382_);
lean_inc(v_lAssignment_1381_);
lean_inc(v_userNames_1380_);
lean_inc(v_decls_1379_);
lean_inc(v_lDecls_1378_);
lean_inc(v_mvarCounter_1377_);
lean_inc(v_lmvarCounter_1376_);
lean_inc(v_levelAssignDepth_1375_);
lean_inc(v_depth_1374_);
lean_dec(v_mctx_1366_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1399_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(v_eAssignment_1382_, v_mvarId_1361_, v_val_1362_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 8, v___x_1390_);
v___x_1392_ = v___x_1387_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_depth_1374_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_levelAssignDepth_1375_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_lmvarCounter_1376_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v_mvarCounter_1377_);
lean_ctor_set(v_reuseFailAlloc_1398_, 4, v_lDecls_1378_);
lean_ctor_set(v_reuseFailAlloc_1398_, 5, v_decls_1379_);
lean_ctor_set(v_reuseFailAlloc_1398_, 6, v_userNames_1380_);
lean_ctor_set(v_reuseFailAlloc_1398_, 7, v_lAssignment_1381_);
lean_ctor_set(v_reuseFailAlloc_1398_, 8, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1398_, 9, v_dAssignment_1383_);
lean_ctor_set(v_reuseFailAlloc_1398_, 10, v_instanceTypedMVars_1384_);
lean_ctor_set(v_reuseFailAlloc_1398_, 11, v_synthNormMemo_1385_);
v___x_1392_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1394_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1392_);
v___x_1394_ = v___x_1372_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_cache_1367_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_zetaDeltaFVarIds_1368_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_postponed_1369_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v_diag_1370_);
v___x_1394_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_st_ref_put(v___y_1363_, v___x_1394_);
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1389_);
return v___x_1396_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1361_ = stack[0].m_obj;
lean_object* v_val_1362_ = stack[1].m_obj;
lean_object* v___y_1363_ = stack[2].m_obj;
lean_object* v_res_1401_;
v_res_1401_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1361_, v_val_1362_, v___y_1363_);
stack->m_obj
 = v_res_1401_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg___boxed(lean_object* v_mvarId_1402_, lean_object* v_val_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1402_, v_val_1403_, v___y_1404_);
lean_dec(v___y_1404_);
return v_res_1406_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(lean_object* v_mvarId_1407_, lean_object* v_type_1408_, lean_object* v_fvars_1409_, uint8_t v_isZero_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___x_1416_; 
lean_inc(v_mvarId_1407_);
v___x_1416_ = l_Lean_MVarId_getTag(v_mvarId_1407_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v___x_1418_ = l_Lean_Expr_headBeta(v_type_1408_);
v___x_1419_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1418_, v_a_1417_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; uint8_t v___x_1421_; uint8_t v___x_1422_; lean_object* v___x_1423_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc_n(v_a_1420_, 2);
lean_dec_ref_known(v___x_1419_, 1);
v___x_1421_ = 0;
v___x_1422_ = 1;
v___x_1423_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1409_, v_a_1420_, v___x_1421_, v_isZero_1410_, v___x_1421_, v_isZero_1410_, v___x_1422_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1425_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1423_, 1);
v___x_1425_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1407_, v_a_1424_, v___y_1412_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1434_; 
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1434_ == 0)
{
lean_object* v_unused_1435_; 
v_unused_1435_ = lean_ctor_get(v___x_1425_, 0);
lean_dec(v_unused_1435_);
v___x_1427_ = v___x_1425_;
v_isShared_1428_ = v_isSharedCheck_1434_;
goto v_resetjp_1426_;
}
else
{
lean_dec(v___x_1425_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1434_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1429_ = l_Lean_Expr_mvarId_x21(v_a_1420_);
lean_dec(v_a_1420_);
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v_fvars_1409_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1430_);
v___x_1432_ = v___x_1427_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec(v_a_1420_);
lean_dec_ref(v_fvars_1409_);
v_a_1436_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1425_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1425_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec(v_a_1420_);
lean_dec_ref(v_fvars_1409_);
lean_dec(v_mvarId_1407_);
v_a_1444_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1423_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1423_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec_ref(v_fvars_1409_);
lean_dec(v_mvarId_1407_);
v_a_1452_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1419_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1419_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec_ref(v_fvars_1409_);
lean_dec_ref(v_type_1408_);
lean_dec(v_mvarId_1407_);
v_a_1460_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1416_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1416_);
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
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1407_ = stack[0].m_obj;
lean_object* v_type_1408_ = stack[1].m_obj;
lean_object* v_fvars_1409_ = stack[2].m_obj;
uint8_t v_isZero_1410_ = stack[3].m_num;
lean_object* v___y_1411_ = stack[4].m_obj;
lean_object* v___y_1412_ = stack[5].m_obj;
lean_object* v___y_1413_ = stack[6].m_obj;
lean_object* v___y_1414_ = stack[7].m_obj;
lean_object* v_res_1468_;
v_res_1468_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(v_mvarId_1407_, v_type_1408_, v_fvars_1409_, v_isZero_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
stack->m_obj
 = v_res_1468_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0___boxed(lean_object* v_mvarId_1469_, lean_object* v_type_1470_, lean_object* v_fvars_1471_, lean_object* v_isZero_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
uint8_t v_isZero_boxed_1478_; lean_object* v_res_1479_; 
v_isZero_boxed_1478_ = lean_unbox(v_isZero_1472_);
v_res_1479_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(v_mvarId_1469_, v_type_1470_, v_fvars_1471_, v_isZero_boxed_1478_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
return v_res_1479_;
}
}
lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(lean_object* v_lctx_1480_, lean_object* v_x_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_keyedConfig_1487_; uint8_t v_trackZetaDelta_1488_; lean_object* v_zetaDeltaSet_1489_; lean_object* v_localInstances_1490_; lean_object* v_defEqCtx_x3f_1491_; lean_object* v_synthPendingDepth_1492_; lean_object* v_customCanUnfoldPredicate_x3f_1493_; uint8_t v_univApprox_1494_; uint8_t v_inTypeClassResolution_1495_; uint8_t v_cacheInferType_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_keyedConfig_1487_ = lean_ctor_get(v___y_1482_, 0);
v_trackZetaDelta_1488_ = lean_ctor_get_uint8(v___y_1482_, sizeof(void*)*7);
v_zetaDeltaSet_1489_ = lean_ctor_get(v___y_1482_, 1);
v_localInstances_1490_ = lean_ctor_get(v___y_1482_, 3);
v_defEqCtx_x3f_1491_ = lean_ctor_get(v___y_1482_, 4);
v_synthPendingDepth_1492_ = lean_ctor_get(v___y_1482_, 5);
v_customCanUnfoldPredicate_x3f_1493_ = lean_ctor_get(v___y_1482_, 6);
v_univApprox_1494_ = lean_ctor_get_uint8(v___y_1482_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1495_ = lean_ctor_get_uint8(v___y_1482_, sizeof(void*)*7 + 2);
v_cacheInferType_1496_ = lean_ctor_get_uint8(v___y_1482_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_1493_);
lean_inc(v_synthPendingDepth_1492_);
lean_inc(v_defEqCtx_x3f_1491_);
lean_inc_ref(v_localInstances_1490_);
lean_inc(v_zetaDeltaSet_1489_);
lean_inc_ref(v_keyedConfig_1487_);
v___x_1497_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1497_, 0, v_keyedConfig_1487_);
lean_ctor_set(v___x_1497_, 1, v_zetaDeltaSet_1489_);
lean_ctor_set(v___x_1497_, 2, v_lctx_1480_);
lean_ctor_set(v___x_1497_, 3, v_localInstances_1490_);
lean_ctor_set(v___x_1497_, 4, v_defEqCtx_x3f_1491_);
lean_ctor_set(v___x_1497_, 5, v_synthPendingDepth_1492_);
lean_ctor_set(v___x_1497_, 6, v_customCanUnfoldPredicate_x3f_1493_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*7, v_trackZetaDelta_1488_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*7 + 1, v_univApprox_1494_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1495_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*7 + 3, v_cacheInferType_1496_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
v___x_1498_ = lean_apply_5(v_x_1481_, v___x_1497_, v___y_1483_, v___y_1484_, v___y_1485_, lean_box(0));
return v___x_1498_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1480_ = stack[0].m_obj;
lean_object* v_x_1481_ = stack[1].m_obj;
lean_object* v___y_1482_ = stack[2].m_obj;
lean_object* v___y_1483_ = stack[3].m_obj;
lean_object* v___y_1484_ = stack[4].m_obj;
lean_object* v___y_1485_ = stack[5].m_obj;
lean_object* v_res_1499_;
v_res_1499_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1480_, v_x_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
stack->m_obj
 = v_res_1499_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg___boxed(lean_object* v_lctx_1500_, lean_object* v_x_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1500_, v_x_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed(lean_object* v_type_1508_, lean_object* v_mvarId_1509_, lean_object* v_n_1510_, lean_object* v_preserveBinderNames_1511_, lean_object* v___x_1512_, lean_object* v_useNamesForExplicitOnly_1513_, lean_object* v_lctx_1514_, lean_object* v_fvars_1515_, lean_object* v___x_1516_, lean_object* v_s_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1523_; uint8_t v___x_4633__boxed_1524_; uint8_t v_useNamesForExplicitOnly_boxed_1525_; lean_object* v_res_1526_; 
v_preserveBinderNames_boxed_1523_ = lean_unbox(v_preserveBinderNames_1511_);
v___x_4633__boxed_1524_ = lean_unbox(v___x_1512_);
v_useNamesForExplicitOnly_boxed_1525_ = lean_unbox(v_useNamesForExplicitOnly_1513_);
v_res_1526_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(v_type_1508_, v_mvarId_1509_, v_n_1510_, v_preserveBinderNames_boxed_1523_, v___x_4633__boxed_1524_, v_useNamesForExplicitOnly_boxed_1525_, v_lctx_1514_, v_fvars_1515_, v___x_1516_, v_s_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v_n_1510_);
return v_res_1526_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(uint8_t v_preserveBinderNames_1527_, uint8_t v___x_1528_, uint8_t v_useNamesForExplicitOnly_1529_, lean_object* v_mvarId_1530_, lean_object* v_i_1531_, lean_object* v_lctx_1532_, lean_object* v_fvars_1533_, lean_object* v_j_1534_, lean_object* v_s_1535_, lean_object* v_type_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_zero_1542_; uint8_t v_isZero_1543_; 
v_zero_1542_ = lean_unsigned_to_nat(0u);
v_isZero_1543_ = lean_nat_dec_eq(v_i_1531_, v_zero_1542_);
if (v_isZero_1543_ == 1)
{
lean_object* v___x_1544_; lean_object* v_type_1545_; lean_object* v___x_1546_; lean_object* v___f_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec(v_s_1535_);
lean_dec(v_i_1531_);
v___x_1544_ = lean_array_get_size(v_fvars_1533_);
v_type_1545_ = lean_expr_instantiate_rev_range(v_type_1536_, v_j_1534_, v___x_1544_, v_fvars_1533_);
lean_dec_ref(v_type_1536_);
v___x_1546_ = lean_box(v_isZero_1543_);
lean_inc_ref(v_fvars_1533_);
v___f_1547_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1547_, 0, v_mvarId_1530_);
lean_closure_set(v___f_1547_, 1, v_type_1545_);
lean_closure_set(v___f_1547_, 2, v_fvars_1533_);
lean_closure_set(v___f_1547_, 3, v___x_1546_);
v___x_1548_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed), 9, 4);
lean_closure_set(v___x_1548_, 0, lean_box(0));
lean_closure_set(v___x_1548_, 1, v_fvars_1533_);
lean_closure_set(v___x_1548_, 2, v_j_1534_);
lean_closure_set(v___x_1548_, 3, v___f_1547_);
v___x_1549_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1532_, v___x_1548_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
return v___x_1549_;
}
else
{
lean_object* v_one_1550_; lean_object* v_n_1551_; 
v_one_1550_ = lean_unsigned_to_nat(1u);
v_n_1551_ = lean_nat_sub(v_i_1531_, v_one_1550_);
lean_dec(v_i_1531_);
switch(lean_obj_tag(v_type_1536_))
{
case 8:
{
lean_object* v_declName_1552_; lean_object* v_type_1553_; lean_object* v_value_1554_; lean_object* v_body_1555_; lean_object* v___x_1556_; lean_object* v_type_1557_; lean_object* v_type_1558_; lean_object* v_val_1559_; lean_object* v___x_1560_; 
v_declName_1552_ = lean_ctor_get(v_type_1536_, 0);
lean_inc(v_declName_1552_);
v_type_1553_ = lean_ctor_get(v_type_1536_, 1);
lean_inc_ref(v_type_1553_);
v_value_1554_ = lean_ctor_get(v_type_1536_, 2);
lean_inc_ref(v_value_1554_);
v_body_1555_ = lean_ctor_get(v_type_1536_, 3);
lean_inc_ref(v_body_1555_);
lean_dec_ref_known(v_type_1536_, 4);
v___x_1556_ = lean_array_get_size(v_fvars_1533_);
v_type_1557_ = lean_expr_instantiate_rev_range(v_type_1553_, v_j_1534_, v___x_1556_, v_fvars_1533_);
lean_dec_ref(v_type_1553_);
v_type_1558_ = l_Lean_Expr_headBeta(v_type_1557_);
v_val_1559_ = lean_expr_instantiate_rev_range(v_value_1554_, v_j_1534_, v___x_1556_, v_fvars_1533_);
lean_dec_ref(v_value_1554_);
v___x_1560_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v___x_1562_ = 1;
v___x_1563_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_1527_, v___x_1528_, v_useNamesForExplicitOnly_1529_, v_lctx_1532_, v_declName_1552_, v___x_1562_, v_s_1535_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v_fst_1565_; lean_object* v_snd_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v_fst_1565_ = lean_ctor_get(v_a_1564_, 0);
lean_inc(v_fst_1565_);
v_snd_1566_ = lean_ctor_get(v_a_1564_, 1);
lean_inc(v_snd_1566_);
lean_dec(v_a_1564_);
v___x_1567_ = 0;
lean_inc(v_a_1561_);
v___x_1568_ = l_Lean_LocalContext_mkLetDecl(v_lctx_1532_, v_a_1561_, v_fst_1565_, v_type_1558_, v_val_1559_, v_isZero_1543_, v___x_1567_);
v___x_1569_ = l_Lean_mkFVar(v_a_1561_);
v___x_1570_ = lean_array_push(v_fvars_1533_, v___x_1569_);
v_i_1531_ = v_n_1551_;
v_lctx_1532_ = v___x_1568_;
v_fvars_1533_ = v___x_1570_;
v_s_1535_ = v_snd_1566_;
v_type_1536_ = v_body_1555_;
goto _start;
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v_a_1561_);
lean_dec_ref(v_val_1559_);
lean_dec_ref(v_type_1558_);
lean_dec_ref(v_body_1555_);
lean_dec(v_n_1551_);
lean_dec(v_j_1534_);
lean_dec_ref(v_fvars_1533_);
lean_dec_ref(v_lctx_1532_);
lean_dec(v_mvarId_1530_);
v_a_1572_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1563_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1563_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec_ref(v_val_1559_);
lean_dec_ref(v_type_1558_);
lean_dec_ref(v_body_1555_);
lean_dec(v_declName_1552_);
lean_dec(v_n_1551_);
lean_dec(v_s_1535_);
lean_dec(v_j_1534_);
lean_dec_ref(v_fvars_1533_);
lean_dec_ref(v_lctx_1532_);
lean_dec(v_mvarId_1530_);
v_a_1580_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1560_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1560_);
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
case 7:
{
lean_object* v_binderName_1588_; lean_object* v_binderType_1589_; lean_object* v_body_1590_; uint8_t v_binderInfo_1591_; lean_object* v___x_1592_; lean_object* v_type_1593_; lean_object* v_type_1594_; lean_object* v___x_1595_; 
v_binderName_1588_ = lean_ctor_get(v_type_1536_, 0);
lean_inc(v_binderName_1588_);
v_binderType_1589_ = lean_ctor_get(v_type_1536_, 1);
lean_inc_ref(v_binderType_1589_);
v_body_1590_ = lean_ctor_get(v_type_1536_, 2);
lean_inc_ref(v_body_1590_);
v_binderInfo_1591_ = lean_ctor_get_uint8(v_type_1536_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_1536_, 3);
v___x_1592_ = lean_array_get_size(v_fvars_1533_);
v_type_1593_ = lean_expr_instantiate_rev_range(v_binderType_1589_, v_j_1534_, v___x_1592_, v_fvars_1533_);
lean_dec_ref(v_binderType_1589_);
v_type_1594_ = l_Lean_Expr_headBeta(v_type_1593_);
v___x_1595_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; uint8_t v___x_1597_; lean_object* v___x_1598_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1595_, 1);
v___x_1597_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_1591_);
v___x_1598_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_1527_, v___x_1528_, v_useNamesForExplicitOnly_1529_, v_lctx_1532_, v_binderName_1588_, v___x_1597_, v_s_1535_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v_fst_1600_; lean_object* v_snd_1601_; uint8_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v_fst_1600_ = lean_ctor_get(v_a_1599_, 0);
lean_inc(v_fst_1600_);
v_snd_1601_ = lean_ctor_get(v_a_1599_, 1);
lean_inc(v_snd_1601_);
lean_dec(v_a_1599_);
v___x_1602_ = 0;
lean_inc(v_a_1596_);
v___x_1603_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_1532_, v_a_1596_, v_fst_1600_, v_type_1594_, v_binderInfo_1591_, v___x_1602_);
v___x_1604_ = l_Lean_mkFVar(v_a_1596_);
v___x_1605_ = lean_array_push(v_fvars_1533_, v___x_1604_);
v_i_1531_ = v_n_1551_;
v_lctx_1532_ = v___x_1603_;
v_fvars_1533_ = v___x_1605_;
v_s_1535_ = v_snd_1601_;
v_type_1536_ = v_body_1590_;
goto _start;
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec(v_a_1596_);
lean_dec_ref(v_type_1594_);
lean_dec_ref(v_body_1590_);
lean_dec(v_n_1551_);
lean_dec(v_j_1534_);
lean_dec_ref(v_fvars_1533_);
lean_dec_ref(v_lctx_1532_);
lean_dec(v_mvarId_1530_);
v_a_1607_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1598_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1598_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec_ref(v_type_1594_);
lean_dec_ref(v_body_1590_);
lean_dec(v_binderName_1588_);
lean_dec(v_n_1551_);
lean_dec(v_s_1535_);
lean_dec(v_j_1534_);
lean_dec_ref(v_fvars_1533_);
lean_dec_ref(v_lctx_1532_);
lean_dec(v_mvarId_1530_);
v_a_1615_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1595_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1595_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
default: 
{
lean_object* v___x_1623_; lean_object* v_type_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___f_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1623_ = lean_array_get_size(v_fvars_1533_);
v_type_1624_ = lean_expr_instantiate_rev_range(v_type_1536_, v_j_1534_, v___x_1623_, v_fvars_1533_);
lean_dec_ref(v_type_1536_);
v___x_1625_ = lean_box(v_preserveBinderNames_1527_);
v___x_1626_ = lean_box(v___x_1528_);
v___x_1627_ = lean_box(v_useNamesForExplicitOnly_1529_);
lean_inc_ref(v_fvars_1533_);
lean_inc_ref(v_lctx_1532_);
v___f_1628_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed), 15, 10);
lean_closure_set(v___f_1628_, 0, v_type_1624_);
lean_closure_set(v___f_1628_, 1, v_mvarId_1530_);
lean_closure_set(v___f_1628_, 2, v_n_1551_);
lean_closure_set(v___f_1628_, 3, v___x_1625_);
lean_closure_set(v___f_1628_, 4, v___x_1626_);
lean_closure_set(v___f_1628_, 5, v___x_1627_);
lean_closure_set(v___f_1628_, 6, v_lctx_1532_);
lean_closure_set(v___f_1628_, 7, v_fvars_1533_);
lean_closure_set(v___f_1628_, 8, v___x_1623_);
lean_closure_set(v___f_1628_, 9, v_s_1535_);
v___x_1629_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed), 9, 4);
lean_closure_set(v___x_1629_, 0, lean_box(0));
lean_closure_set(v___x_1629_, 1, v_fvars_1533_);
lean_closure_set(v___x_1629_, 2, v_j_1534_);
lean_closure_set(v___x_1629_, 3, v___f_1628_);
v___x_1630_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1532_, v___x_1629_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
return v___x_1630_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_preserveBinderNames_1527_ = stack[0].m_num;
uint8_t v___x_1528_ = stack[1].m_num;
uint8_t v_useNamesForExplicitOnly_1529_ = stack[2].m_num;
lean_object* v_mvarId_1530_ = stack[3].m_obj;
lean_object* v_i_1531_ = stack[4].m_obj;
lean_object* v_lctx_1532_ = stack[5].m_obj;
lean_object* v_fvars_1533_ = stack[6].m_obj;
lean_object* v_j_1534_ = stack[7].m_obj;
lean_object* v_s_1535_ = stack[8].m_obj;
lean_object* v_type_1536_ = stack[9].m_obj;
lean_object* v_a_1537_ = stack[10].m_obj;
lean_object* v_a_1538_ = stack[11].m_obj;
lean_object* v_a_1539_ = stack[12].m_obj;
lean_object* v_a_1540_ = stack[13].m_obj;
lean_object* v_res_1631_;
v_res_1631_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1527_, v___x_1528_, v_useNamesForExplicitOnly_1529_, v_mvarId_1530_, v_i_1531_, v_lctx_1532_, v_fvars_1533_, v_j_1534_, v_s_1535_, v_type_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
stack->m_obj
 = v_res_1631_;
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(lean_object* v_type_1632_, lean_object* v_mvarId_1633_, lean_object* v_n_1634_, uint8_t v_preserveBinderNames_1635_, uint8_t v___x_1636_, uint8_t v_useNamesForExplicitOnly_1637_, lean_object* v_lctx_1638_, lean_object* v_fvars_1639_, lean_object* v___x_1640_, lean_object* v_s_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_type_1632_, v___y_1643_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1649_; uint8_t v___y_1651_; uint8_t v___x_1672_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = l_Lean_Expr_cleanupAnnotations(v_a_1648_);
v___x_1672_ = l_Lean_Expr_isForall(v___x_1649_);
if (v___x_1672_ == 0)
{
uint8_t v___x_1673_; 
v___x_1673_ = l_Lean_Expr_isLet(v___x_1649_);
v___y_1651_ = v___x_1673_;
goto v___jp_1650_;
}
else
{
v___y_1651_ = v___x_1672_;
goto v___jp_1650_;
}
v___jp_1650_:
{
if (v___y_1651_ == 0)
{
lean_object* v___x_1652_; 
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1644_);
lean_inc(v___y_1643_);
lean_inc_ref(v___y_1642_);
v___x_1652_ = lean_whnf(v___x_1649_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; uint8_t v___x_1654_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1652_, 1);
v___x_1654_ = l_Lean_Expr_isForall(v_a_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_dec(v_a_1653_);
lean_dec(v_s_1641_);
lean_dec(v___x_1640_);
lean_dec_ref(v_fvars_1639_);
lean_dec_ref(v_lctx_1638_);
v___x_1655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
v___x_1656_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4);
v___x_1657_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1655_, v_mvarId_1633_, v___x_1656_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
return v___x_1657_;
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1658_ = lean_unsigned_to_nat(1u);
v___x_1659_ = lean_nat_add(v_n_1634_, v___x_1658_);
v___x_1660_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1635_, v___x_1636_, v_useNamesForExplicitOnly_1637_, v_mvarId_1633_, v___x_1659_, v_lctx_1638_, v_fvars_1639_, v___x_1640_, v_s_1641_, v_a_1653_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
return v___x_1660_;
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v_s_1641_);
lean_dec(v___x_1640_);
lean_dec_ref(v_fvars_1639_);
lean_dec_ref(v_lctx_1638_);
lean_dec(v_mvarId_1633_);
v_a_1661_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1652_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1652_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_unsigned_to_nat(1u);
v___x_1670_ = lean_nat_add(v_n_1634_, v___x_1669_);
v___x_1671_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1635_, v___x_1636_, v_useNamesForExplicitOnly_1637_, v_mvarId_1633_, v___x_1670_, v_lctx_1638_, v_fvars_1639_, v___x_1640_, v_s_1641_, v___x_1649_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
return v___x_1671_;
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v_s_1641_);
lean_dec(v___x_1640_);
lean_dec_ref(v_fvars_1639_);
lean_dec_ref(v_lctx_1638_);
lean_dec(v_mvarId_1633_);
v_a_1674_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1647_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1647_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1632_ = stack[0].m_obj;
lean_object* v_mvarId_1633_ = stack[1].m_obj;
lean_object* v_n_1634_ = stack[2].m_obj;
uint8_t v_preserveBinderNames_1635_ = stack[3].m_num;
uint8_t v___x_1636_ = stack[4].m_num;
uint8_t v_useNamesForExplicitOnly_1637_ = stack[5].m_num;
lean_object* v_lctx_1638_ = stack[6].m_obj;
lean_object* v_fvars_1639_ = stack[7].m_obj;
lean_object* v___x_1640_ = stack[8].m_obj;
lean_object* v_s_1641_ = stack[9].m_obj;
lean_object* v___y_1642_ = stack[10].m_obj;
lean_object* v___y_1643_ = stack[11].m_obj;
lean_object* v___y_1644_ = stack[12].m_obj;
lean_object* v___y_1645_ = stack[13].m_obj;
lean_object* v_res_1682_;
v_res_1682_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(v_type_1632_, v_mvarId_1633_, v_n_1634_, v_preserveBinderNames_1635_, v___x_1636_, v_useNamesForExplicitOnly_1637_, v_lctx_1638_, v_fvars_1639_, v___x_1640_, v_s_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
stack->m_obj
 = v_res_1682_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___boxed(lean_object* v_preserveBinderNames_1683_, lean_object* v___x_1684_, lean_object* v_useNamesForExplicitOnly_1685_, lean_object* v_mvarId_1686_, lean_object* v_i_1687_, lean_object* v_lctx_1688_, lean_object* v_fvars_1689_, lean_object* v_j_1690_, lean_object* v_s_1691_, lean_object* v_type_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1698_; uint8_t v___x_4666__boxed_1699_; uint8_t v_useNamesForExplicitOnly_boxed_1700_; lean_object* v_res_1701_; 
v_preserveBinderNames_boxed_1698_ = lean_unbox(v_preserveBinderNames_1683_);
v___x_4666__boxed_1699_ = lean_unbox(v___x_1684_);
v_useNamesForExplicitOnly_boxed_1700_ = lean_unbox(v_useNamesForExplicitOnly_1685_);
v_res_1701_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_boxed_1698_, v___x_4666__boxed_1699_, v_useNamesForExplicitOnly_boxed_1700_, v_mvarId_1686_, v_i_1687_, v_lctx_1688_, v_fvars_1689_, v_j_1690_, v_s_1691_, v_type_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
return v_res_1701_;
}
}
lean_object* l_Lean_Meta_introNCore___lam__0(lean_object* v_mvarId_1702_, lean_object* v___x_1703_, lean_object* v___x_1704_, uint8_t v_preserveBinderNames_1705_, uint8_t v___x_1706_, uint8_t v_useNamesForExplicitOnly_1707_, lean_object* v_n_1708_, lean_object* v_givenNames_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; 
lean_inc(v_mvarId_1702_);
v___x_1715_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1702_, v___x_1703_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v___x_1716_; 
lean_dec_ref_known(v___x_1715_, 1);
lean_inc(v_mvarId_1702_);
v___x_1716_ = l_Lean_MVarId_getType(v_mvarId_1702_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v_lctx_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
v_lctx_1718_ = lean_ctor_get(v___y_1710_, 2);
lean_inc_ref(v_lctx_1718_);
v___x_1719_ = lean_mk_empty_array_with_capacity(v___x_1704_);
v___x_1720_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_1705_, v___x_1706_, v_useNamesForExplicitOnly_1707_, v_mvarId_1702_, v_n_1708_, v_lctx_1718_, v___x_1719_, v___x_1704_, v_givenNames_1709_, v_a_1717_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec_ref(v___y_1710_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1740_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1723_ = v___x_1720_;
v_isShared_1724_ = v_isSharedCheck_1740_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1720_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1740_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_fst_1725_; lean_object* v_snd_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1739_; 
v_fst_1725_ = lean_ctor_get(v_a_1721_, 0);
v_snd_1726_ = lean_ctor_get(v_a_1721_, 1);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_a_1721_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1728_ = v_a_1721_;
v_isShared_1729_ = v_isSharedCheck_1739_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_snd_1726_);
lean_inc(v_fst_1725_);
lean_dec(v_a_1721_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1739_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
size_t v_sz_1730_; size_t v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1734_; 
v_sz_1730_ = lean_array_size(v_fst_1725_);
v___x_1731_ = ((size_t)0ULL);
v___x_1732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(v_sz_1730_, v___x_1731_, v_fst_1725_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1732_);
v___x_1734_ = v___x_1728_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_snd_1726_);
v___x_1734_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1736_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1734_);
v___x_1736_ = v___x_1723_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1734_);
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
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
v_a_1741_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1720_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1720_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_dec_ref(v___y_1710_);
lean_dec(v_givenNames_1709_);
lean_dec(v_n_1708_);
lean_dec(v___x_1704_);
lean_dec(v_mvarId_1702_);
v_a_1749_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1716_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1716_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec_ref(v___y_1710_);
lean_dec(v_givenNames_1709_);
lean_dec(v_n_1708_);
lean_dec(v___x_1704_);
lean_dec(v_mvarId_1702_);
v_a_1757_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1715_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1715_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_introNCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1702_ = stack[0].m_obj;
lean_object* v___x_1703_ = stack[1].m_obj;
lean_object* v___x_1704_ = stack[2].m_obj;
uint8_t v_preserveBinderNames_1705_ = stack[3].m_num;
uint8_t v___x_1706_ = stack[4].m_num;
uint8_t v_useNamesForExplicitOnly_1707_ = stack[5].m_num;
lean_object* v_n_1708_ = stack[6].m_obj;
lean_object* v_givenNames_1709_ = stack[7].m_obj;
lean_object* v___y_1710_ = stack[8].m_obj;
lean_object* v___y_1711_ = stack[9].m_obj;
lean_object* v___y_1712_ = stack[10].m_obj;
lean_object* v___y_1713_ = stack[11].m_obj;
lean_object* v_res_1765_;
v_res_1765_ = l_Lean_Meta_introNCore___lam__0(v_mvarId_1702_, v___x_1703_, v___x_1704_, v_preserveBinderNames_1705_, v___x_1706_, v_useNamesForExplicitOnly_1707_, v_n_1708_, v_givenNames_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
stack->m_obj
 = v_res_1765_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___lam__0___boxed(lean_object* v_mvarId_1766_, lean_object* v___x_1767_, lean_object* v___x_1768_, lean_object* v_preserveBinderNames_1769_, lean_object* v___x_1770_, lean_object* v_useNamesForExplicitOnly_1771_, lean_object* v_n_1772_, lean_object* v_givenNames_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
uint8_t v_preserveBinderNames_boxed_1779_; uint8_t v___x_5030__boxed_1780_; uint8_t v_useNamesForExplicitOnly_boxed_1781_; lean_object* v_res_1782_; 
v_preserveBinderNames_boxed_1779_ = lean_unbox(v_preserveBinderNames_1769_);
v___x_5030__boxed_1780_ = lean_unbox(v___x_1770_);
v_useNamesForExplicitOnly_boxed_1781_ = lean_unbox(v_useNamesForExplicitOnly_1771_);
v_res_1782_ = l_Lean_Meta_introNCore___lam__0(v_mvarId_1766_, v___x_1767_, v___x_1768_, v_preserveBinderNames_boxed_1779_, v___x_5030__boxed_1780_, v_useNamesForExplicitOnly_boxed_1781_, v_n_1772_, v_givenNames_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
return v_res_1782_;
}
}
lean_object* l_Lean_Meta_introNCore(lean_object* v_mvarId_1785_, lean_object* v_n_1786_, lean_object* v_givenNames_1787_, uint8_t v_useNamesForExplicitOnly_1788_, uint8_t v_preserveBinderNames_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_nat_dec_eq(v_n_1786_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___f_1804_; lean_object* v___x_1805_; 
v___x_1797_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1792_);
v___x_1798_ = l_Lean_Meta_tactic_hygienic;
v___x_1799_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(v___x_1797_, v___x_1798_);
lean_dec_ref(v___x_1797_);
v___x_1800_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1));
v___x_1801_ = lean_box(v_preserveBinderNames_1789_);
v___x_1802_ = lean_box(v___x_1799_);
v___x_1803_ = lean_box(v_useNamesForExplicitOnly_1788_);
lean_inc(v_mvarId_1785_);
v___f_1804_ = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1804_, 0, v_mvarId_1785_);
lean_closure_set(v___f_1804_, 1, v___x_1800_);
lean_closure_set(v___f_1804_, 2, v___x_1795_);
lean_closure_set(v___f_1804_, 3, v___x_1801_);
lean_closure_set(v___f_1804_, 4, v___x_1802_);
lean_closure_set(v___f_1804_, 5, v___x_1803_);
lean_closure_set(v___f_1804_, 6, v_n_1786_);
lean_closure_set(v___f_1804_, 7, v_givenNames_1787_);
v___x_1805_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_1785_, v___f_1804_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec(v_givenNames_1787_);
lean_dec(v_n_1786_);
v___x_1806_ = ((lean_object*)(l_Lean_Meta_introNCore___closed__0));
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set(v___x_1807_, 1, v_mvarId_1785_);
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
return v___x_1808_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_introNCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1785_ = stack[0].m_obj;
lean_object* v_n_1786_ = stack[1].m_obj;
lean_object* v_givenNames_1787_ = stack[2].m_obj;
uint8_t v_useNamesForExplicitOnly_1788_ = stack[3].m_num;
uint8_t v_preserveBinderNames_1789_ = stack[4].m_num;
lean_object* v_a_1790_ = stack[5].m_obj;
lean_object* v_a_1791_ = stack[6].m_obj;
lean_object* v_a_1792_ = stack[7].m_obj;
lean_object* v_a_1793_ = stack[8].m_obj;
lean_object* v_res_1809_;
v_res_1809_ = l_Lean_Meta_introNCore(v_mvarId_1785_, v_n_1786_, v_givenNames_1787_, v_useNamesForExplicitOnly_1788_, v_preserveBinderNames_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
stack->m_obj
 = v_res_1809_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___boxed(lean_object* v_mvarId_1810_, lean_object* v_n_1811_, lean_object* v_givenNames_1812_, lean_object* v_useNamesForExplicitOnly_1813_, lean_object* v_preserveBinderNames_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
uint8_t v_useNamesForExplicitOnly_boxed_1820_; uint8_t v_preserveBinderNames_boxed_1821_; lean_object* v_res_1822_; 
v_useNamesForExplicitOnly_boxed_1820_ = lean_unbox(v_useNamesForExplicitOnly_1813_);
v_preserveBinderNames_boxed_1821_ = lean_unbox(v_preserveBinderNames_1814_);
v_res_1822_ = l_Lean_Meta_introNCore(v_mvarId_1810_, v_n_1811_, v_givenNames_1812_, v_useNamesForExplicitOnly_boxed_1820_, v_preserveBinderNames_boxed_1821_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
return v_res_1822_;
}
}
lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(lean_object* v_00_u03b1_1823_, lean_object* v_lctx_1824_, lean_object* v_x_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_1824_, v_x_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
return v___x_1831_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1824_ = stack[1].m_obj;
lean_object* v_x_1825_ = stack[2].m_obj;
lean_object* v___y_1826_ = stack[3].m_obj;
lean_object* v___y_1827_ = stack[4].m_obj;
lean_object* v___y_1828_ = stack[5].m_obj;
lean_object* v___y_1829_ = stack[6].m_obj;
lean_object* v_res_1832_;
v_res_1832_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(lean_box(0), v_lctx_1824_, v_x_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
stack->m_obj
 = v_res_1832_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1833_, lean_object* v_lctx_1834_, lean_object* v_x_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(v_00_u03b1_1833_, v_lctx_1834_, v_x_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
return v_res_1841_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(lean_object* v_e_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_1842_, v___y_1844_);
return v___x_1848_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1842_ = stack[0].m_obj;
lean_object* v___y_1843_ = stack[1].m_obj;
lean_object* v___y_1844_ = stack[2].m_obj;
lean_object* v___y_1845_ = stack[3].m_obj;
lean_object* v___y_1846_ = stack[4].m_obj;
lean_object* v_res_1849_;
v_res_1849_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(v_e_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
stack->m_obj
 = v_res_1849_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___boxed(lean_object* v_e_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(v_e_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
return v_res_1856_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(lean_object* v_mvarId_1857_, lean_object* v_val_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_1857_, v_val_1858_, v___y_1860_);
return v___x_1864_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1857_ = stack[0].m_obj;
lean_object* v_val_1858_ = stack[1].m_obj;
lean_object* v___y_1859_ = stack[2].m_obj;
lean_object* v___y_1860_ = stack[3].m_obj;
lean_object* v___y_1861_ = stack[4].m_obj;
lean_object* v___y_1862_ = stack[5].m_obj;
lean_object* v_res_1865_;
v_res_1865_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(v_mvarId_1857_, v_val_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
stack->m_obj
 = v_res_1865_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___boxed(lean_object* v_mvarId_1866_, lean_object* v_val_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(v_mvarId_1866_, v_val_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
return v_res_1873_;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1874_, lean_object* v_fvars_1875_, lean_object* v_j_1876_, lean_object* v_x_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_1875_, v_j_1876_, v_x_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1875_ = stack[1].m_obj;
lean_object* v_j_1876_ = stack[2].m_obj;
lean_object* v_x_1877_ = stack[3].m_obj;
lean_object* v___y_1878_ = stack[4].m_obj;
lean_object* v___y_1879_ = stack[5].m_obj;
lean_object* v___y_1880_ = stack[6].m_obj;
lean_object* v___y_1881_ = stack[7].m_obj;
lean_object* v_res_1884_;
v_res_1884_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(lean_box(0), v_fvars_1875_, v_j_1876_, v_x_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
stack->m_obj
 = v_res_1884_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1885_, lean_object* v_fvars_1886_, lean_object* v_j_1887_, lean_object* v_x_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(v_00_u03b1_1885_, v_fvars_1886_, v_j_1887_, v_x_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
return v_res_1894_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_1898_);
return v___x_1900_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1895_ = stack[0].m_obj;
lean_object* v___y_1896_ = stack[1].m_obj;
lean_object* v___y_1897_ = stack[2].m_obj;
lean_object* v___y_1898_ = stack[3].m_obj;
lean_object* v_res_1901_;
v_res_1901_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
stack->m_obj
 = v_res_1901_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___boxed(lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1908_, lean_object* v_x_1909_, lean_object* v_x_1910_, lean_object* v_x_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(v_x_1909_, v_x_1910_, v_x_1911_);
return v___x_1912_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1913_, lean_object* v_x_1914_, size_t v_x_1915_, size_t v_x_1916_, lean_object* v_x_1917_, lean_object* v_x_1918_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1914_, v_x_1915_, v_x_1916_, v_x_1917_, v_x_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1914_ = stack[1].m_obj;
size_t v_x_1915_ = stack[2].m_num;
size_t v_x_1916_ = stack[3].m_num;
lean_object* v_x_1917_ = stack[4].m_obj;
lean_object* v_x_1918_ = stack[5].m_obj;
lean_object* v_res_1920_;
v_res_1920_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(lean_box(0), v_x_1914_, v_x_1915_, v_x_1916_, v_x_1917_, v_x_1918_);
stack->m_obj
 = v_res_1920_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1921_, lean_object* v_x_1922_, lean_object* v_x_1923_, lean_object* v_x_1924_, lean_object* v_x_1925_, lean_object* v_x_1926_){
_start:
{
size_t v_x_5424__boxed_1927_; size_t v_x_5425__boxed_1928_; lean_object* v_res_1929_; 
v_x_5424__boxed_1927_ = lean_unbox_usize(v_x_1923_);
lean_dec(v_x_1923_);
v_x_5425__boxed_1928_ = lean_unbox_usize(v_x_1924_);
lean_dec(v_x_1924_);
v_res_1929_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1921_, v_x_1922_, v_x_5424__boxed_1927_, v_x_5425__boxed_1928_, v_x_1925_, v_x_1926_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11(lean_object* v_00_u03b2_1930_, lean_object* v_n_1931_, lean_object* v_k_1932_, lean_object* v_v_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(v_n_1931_, v_k_1932_, v_v_1933_);
return v___x_1934_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(lean_object* v_00_u03b2_1935_, size_t v_depth_1936_, lean_object* v_keys_1937_, lean_object* v_vals_1938_, lean_object* v_heq_1939_, lean_object* v_i_1940_, lean_object* v_entries_1941_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_1936_, v_keys_1937_, v_vals_1938_, v_i_1940_, v_entries_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1936_ = stack[1].m_num;
lean_object* v_keys_1937_ = stack[2].m_obj;
lean_object* v_vals_1938_ = stack[3].m_obj;
lean_object* v_i_1940_ = stack[5].m_obj;
lean_object* v_entries_1941_ = stack[6].m_obj;
lean_object* v_res_1943_;
v_res_1943_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(lean_box(0), v_depth_1936_, v_keys_1937_, v_vals_1938_, lean_box(0), v_i_1940_, v_entries_1941_);
stack->m_obj
 = v_res_1943_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_1944_, lean_object* v_depth_1945_, lean_object* v_keys_1946_, lean_object* v_vals_1947_, lean_object* v_heq_1948_, lean_object* v_i_1949_, lean_object* v_entries_1950_){
_start:
{
size_t v_depth_boxed_1951_; lean_object* v_res_1952_; 
v_depth_boxed_1951_ = lean_unbox_usize(v_depth_1945_);
lean_dec(v_depth_1945_);
v_res_1952_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(v_00_u03b2_1944_, v_depth_boxed_1951_, v_keys_1946_, v_vals_1947_, v_heq_1948_, v_i_1949_, v_entries_1950_);
lean_dec_ref(v_vals_1947_);
lean_dec_ref(v_keys_1946_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1953_, lean_object* v_x_1954_, lean_object* v_x_1955_, lean_object* v_x_1956_, lean_object* v_x_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(v_x_1954_, v_x_1955_, v_x_1956_, v_x_1957_);
return v___x_1958_;
}
}
lean_object* l_Lean_MVarId_introN(lean_object* v_mvarId_1959_, lean_object* v_n_1960_, lean_object* v_givenNames_1961_, uint8_t v_useNamesForExplicitOnly_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
uint8_t v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = 0;
v___x_1969_ = l_Lean_Meta_introNCore(v_mvarId_1959_, v_n_1960_, v_givenNames_1961_, v_useNamesForExplicitOnly_1962_, v___x_1968_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_);
return v___x_1969_;
}
}
LEAN_EXPORT void l_Lean_MVarId_introN_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1959_ = stack[0].m_obj;
lean_object* v_n_1960_ = stack[1].m_obj;
lean_object* v_givenNames_1961_ = stack[2].m_obj;
uint8_t v_useNamesForExplicitOnly_1962_ = stack[3].m_num;
lean_object* v_a_1963_ = stack[4].m_obj;
lean_object* v_a_1964_ = stack[5].m_obj;
lean_object* v_a_1965_ = stack[6].m_obj;
lean_object* v_a_1966_ = stack[7].m_obj;
lean_object* v_res_1970_;
v_res_1970_ = l_Lean_MVarId_introN(v_mvarId_1959_, v_n_1960_, v_givenNames_1961_, v_useNamesForExplicitOnly_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_);
stack->m_obj
 = v_res_1970_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introN___boxed(lean_object* v_mvarId_1971_, lean_object* v_n_1972_, lean_object* v_givenNames_1973_, lean_object* v_useNamesForExplicitOnly_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
uint8_t v_useNamesForExplicitOnly_boxed_1980_; lean_object* v_res_1981_; 
v_useNamesForExplicitOnly_boxed_1980_ = lean_unbox(v_useNamesForExplicitOnly_1974_);
v_res_1981_ = l_Lean_MVarId_introN(v_mvarId_1971_, v_n_1972_, v_givenNames_1973_, v_useNamesForExplicitOnly_boxed_1980_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
return v_res_1981_;
}
}
lean_object* l_Lean_MVarId_introNP(lean_object* v_mvarId_1982_, lean_object* v_n_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
lean_object* v___x_1989_; uint8_t v___x_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; 
v___x_1989_ = lean_box(0);
v___x_1990_ = 0;
v___x_1991_ = 1;
v___x_1992_ = l_Lean_Meta_introNCore(v_mvarId_1982_, v_n_1983_, v___x_1989_, v___x_1990_, v___x_1991_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
return v___x_1992_;
}
}
LEAN_EXPORT void l_Lean_MVarId_introNP_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1982_ = stack[0].m_obj;
lean_object* v_n_1983_ = stack[1].m_obj;
lean_object* v_a_1984_ = stack[2].m_obj;
lean_object* v_a_1985_ = stack[3].m_obj;
lean_object* v_a_1986_ = stack[4].m_obj;
lean_object* v_a_1987_ = stack[5].m_obj;
lean_object* v_res_1993_;
v_res_1993_ = l_Lean_MVarId_introNP(v_mvarId_1982_, v_n_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
stack->m_obj
 = v_res_1993_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introNP___boxed(lean_object* v_mvarId_1994_, lean_object* v_n_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_MVarId_introNP(v_mvarId_1994_, v_n_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
lean_dec(v_a_1997_);
lean_dec_ref(v_a_1996_);
return v_res_2001_;
}
}
lean_object* l_Lean_MVarId_intro(lean_object* v_mvarId_2002_, lean_object* v_name_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; lean_object* v___x_2014_; 
v___x_2009_ = lean_box(0);
v___x_2010_ = lean_unsigned_to_nat(1u);
v___x_2011_ = lean_box(0);
v___x_2012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2012_, 0, v_name_2003_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
v___x_2013_ = 0;
v___x_2014_ = l_Lean_Meta_introNCore(v_mvarId_2002_, v___x_2010_, v___x_2012_, v___x_2013_, v___x_2013_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
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
v___x_2025_ = lean_array_get(v___x_2009_, v_fst_2019_, v___x_2024_);
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
LEAN_EXPORT void l_Lean_MVarId_intro_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2002_ = stack[0].m_obj;
lean_object* v_name_2003_ = stack[1].m_obj;
lean_object* v_a_2004_ = stack[2].m_obj;
lean_object* v_a_2005_ = stack[3].m_obj;
lean_object* v_a_2006_ = stack[4].m_obj;
lean_object* v_a_2007_ = stack[5].m_obj;
lean_object* v_res_2042_;
v_res_2042_ = l_Lean_MVarId_intro(v_mvarId_2002_, v_name_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
stack->m_obj
 = v_res_2042_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro___boxed(lean_object* v_mvarId_2043_, lean_object* v_name_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lean_MVarId_intro(v_mvarId_2043_, v_name_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
lean_dec(v_a_2048_);
lean_dec_ref(v_a_2047_);
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2045_);
return v_res_2050_;
}
}
lean_object* l_Lean_Meta_intro1Core(lean_object* v_mvarId_2051_, uint8_t v_preserveBinderNames_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; lean_object* v___x_2062_; 
v___x_2058_ = lean_box(0);
v___x_2059_ = lean_unsigned_to_nat(1u);
v___x_2060_ = lean_box(0);
v___x_2061_ = 0;
v___x_2062_ = l_Lean_Meta_introNCore(v_mvarId_2051_, v___x_2059_, v___x_2060_, v___x_2061_, v_preserveBinderNames_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2081_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2081_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2081_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v_fst_2067_; lean_object* v_snd_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2080_; 
v_fst_2067_ = lean_ctor_get(v_a_2063_, 0);
v_snd_2068_ = lean_ctor_get(v_a_2063_, 1);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_a_2063_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2070_ = v_a_2063_;
v_isShared_2071_ = v_isSharedCheck_2080_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_snd_2068_);
lean_inc(v_fst_2067_);
lean_dec(v_a_2063_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2080_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2072_ = lean_unsigned_to_nat(0u);
v___x_2073_ = lean_array_get(v___x_2058_, v_fst_2067_, v___x_2072_);
lean_dec(v_fst_2067_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2073_);
v___x_2075_ = v___x_2070_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_snd_2068_);
v___x_2075_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2077_; 
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2075_);
v___x_2077_ = v___x_2065_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
v_a_2082_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2062_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2062_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_intro1Core_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2051_ = stack[0].m_obj;
uint8_t v_preserveBinderNames_2052_ = stack[1].m_num;
lean_object* v_a_2053_ = stack[2].m_obj;
lean_object* v_a_2054_ = stack[3].m_obj;
lean_object* v_a_2055_ = stack[4].m_obj;
lean_object* v_a_2056_ = stack[5].m_obj;
lean_object* v_res_2090_;
v_res_2090_ = l_Lean_Meta_intro1Core(v_mvarId_2051_, v_preserveBinderNames_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
stack->m_obj
 = v_res_2090_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core___boxed(lean_object* v_mvarId_2091_, lean_object* v_preserveBinderNames_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
uint8_t v_preserveBinderNames_boxed_2098_; lean_object* v_res_2099_; 
v_preserveBinderNames_boxed_2098_ = lean_unbox(v_preserveBinderNames_2092_);
v_res_2099_ = l_Lean_Meta_intro1Core(v_mvarId_2091_, v_preserveBinderNames_boxed_2098_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
return v_res_2099_;
}
}
lean_object* l_Lean_MVarId_intro1(lean_object* v_mvarId_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
uint8_t v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = 0;
v___x_2107_ = l_Lean_Meta_intro1Core(v_mvarId_2100_, v___x_2106_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
return v___x_2107_;
}
}
LEAN_EXPORT void l_Lean_MVarId_intro1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2100_ = stack[0].m_obj;
lean_object* v_a_2101_ = stack[1].m_obj;
lean_object* v_a_2102_ = stack[2].m_obj;
lean_object* v_a_2103_ = stack[3].m_obj;
lean_object* v_a_2104_ = stack[4].m_obj;
lean_object* v_res_2108_;
v_res_2108_ = l_Lean_MVarId_intro1(v_mvarId_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
stack->m_obj
 = v_res_2108_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___boxed(lean_object* v_mvarId_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Lean_MVarId_intro1(v_mvarId_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
lean_dec(v_a_2113_);
lean_dec_ref(v_a_2112_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
return v_res_2115_;
}
}
lean_object* l_Lean_MVarId_intro1P(lean_object* v_mvarId_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
uint8_t v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = 1;
v___x_2123_ = l_Lean_Meta_intro1Core(v_mvarId_2116_, v___x_2122_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
return v___x_2123_;
}
}
LEAN_EXPORT void l_Lean_MVarId_intro1P_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2116_ = stack[0].m_obj;
lean_object* v_a_2117_ = stack[1].m_obj;
lean_object* v_a_2118_ = stack[2].m_obj;
lean_object* v_a_2119_ = stack[3].m_obj;
lean_object* v_a_2120_ = stack[4].m_obj;
lean_object* v_res_2124_;
v_res_2124_ = l_Lean_MVarId_intro1P(v_mvarId_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
stack->m_obj
 = v_res_2124_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1P___boxed(lean_object* v_mvarId_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_MVarId_intro1P(v_mvarId_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
lean_dec(v_a_2129_);
lean_dec_ref(v_a_2128_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
return v_res_2131_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(lean_object* v_msgData_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; lean_object* v_env_2139_; uint8_t v___x_2140_; lean_object* v_env_2141_; lean_object* v___x_2142_; lean_object* v_toCold_2143_; lean_object* v_mctx_2144_; lean_object* v_lctx_2145_; lean_object* v_options_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2138_ = lean_st_ref_get(v___y_2136_);
v_env_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc_ref(v_env_2139_);
lean_dec(v___x_2138_);
v___x_2140_ = 0;
v_env_2141_ = l_Lean_Environment_setRecordingDeps(v_env_2139_, v___x_2140_);
v___x_2142_ = lean_st_ref_get(v___y_2134_);
v_toCold_2143_ = lean_ctor_get(v___y_2135_, 0);
v_mctx_2144_ = lean_ctor_get(v___x_2142_, 0);
lean_inc_ref(v_mctx_2144_);
lean_dec(v___x_2142_);
v_lctx_2145_ = lean_ctor_get(v___y_2133_, 2);
v_options_2146_ = lean_ctor_get(v_toCold_2143_, 2);
lean_inc_ref(v_options_2146_);
lean_inc_ref(v_lctx_2145_);
v___x_2147_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2147_, 0, v_env_2141_);
lean_ctor_set(v___x_2147_, 1, v_mctx_2144_);
lean_ctor_set(v___x_2147_, 2, v_lctx_2145_);
lean_ctor_set(v___x_2147_, 3, v_options_2146_);
v___x_2148_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
lean_ctor_set(v___x_2148_, 1, v_msgData_2132_);
v___x_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2132_ = stack[0].m_obj;
lean_object* v___y_2133_ = stack[1].m_obj;
lean_object* v___y_2134_ = stack[2].m_obj;
lean_object* v___y_2135_ = stack[3].m_obj;
lean_object* v___y_2136_ = stack[4].m_obj;
lean_object* v_res_2150_;
v_res_2150_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msgData_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
stack->m_obj
 = v_res_2150_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0___boxed(lean_object* v_msgData_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msgData_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
return v_res_2157_;
}
}
lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(lean_object* v_msg_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_ref_2164_; lean_object* v___x_2165_; lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2174_; 
v_ref_2164_ = lean_ctor_get(v___y_2161_, 2);
v___x_2165_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msg_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2168_ = v___x_2165_;
v_isShared_2169_ = v_isSharedCheck_2174_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2165_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2174_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; lean_object* v___x_2172_; 
lean_inc(v_ref_2164_);
v___x_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2170_, 0, v_ref_2164_);
lean_ctor_set(v___x_2170_, 1, v_a_2166_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set_tag(v___x_2168_, 1);
lean_ctor_set(v___x_2168_, 0, v___x_2170_);
v___x_2172_ = v___x_2168_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2158_ = stack[0].m_obj;
lean_object* v___y_2159_ = stack[1].m_obj;
lean_object* v___y_2160_ = stack[2].m_obj;
lean_object* v___y_2161_ = stack[3].m_obj;
lean_object* v___y_2162_ = stack[4].m_obj;
lean_object* v_res_2175_;
v_res_2175_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v_msg_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
stack->m_obj
 = v_res_2175_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg___boxed(lean_object* v_msg_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v_msg_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
return v_res_2182_;
}
}
static lean_object* _init_l_Lean_MVarId_intro1___00__lam__0___closed__1(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = ((lean_object*)(l_Lean_MVarId_intro1___00__lam__0___closed__0));
v___x_2185_ = l_Lean_stringToMessageData(v___x_2184_);
return v___x_2185_;
}
}
lean_object* l_Lean_MVarId_intro1___00__lam__0(lean_object* v_mvarId_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v___x_2192_; 
lean_inc(v_mvarId_2186_);
v___x_2192_ = l_Lean_MVarId_getType_x27(v_mvarId_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
if (lean_obj_tag(v_a_2193_) == 7)
{
lean_object* v_binderName_2194_; lean_object* v_binderType_2195_; lean_object* v_body_2196_; uint8_t v_binderInfo_2197_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; uint8_t v___x_2234_; 
v_binderName_2194_ = lean_ctor_get(v_a_2193_, 0);
lean_inc(v_binderName_2194_);
v_binderType_2195_ = lean_ctor_get(v_a_2193_, 1);
lean_inc_ref(v_binderType_2195_);
v_body_2196_ = lean_ctor_get(v_a_2193_, 2);
lean_inc_ref(v_body_2196_);
v_binderInfo_2197_ = lean_ctor_get_uint8(v_a_2193_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_2193_, 3);
v___x_2234_ = l_Lean_Expr_hasLooseBVars(v_body_2196_);
if (v___x_2234_ == 0)
{
v___y_2199_ = v___y_2187_;
v___y_2200_ = v___y_2188_;
v___y_2201_ = v___y_2189_;
v___y_2202_ = v___y_2190_;
goto v___jp_2198_;
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref(v_body_2196_);
lean_dec_ref(v_binderType_2195_);
lean_dec(v_binderName_2194_);
v___x_2235_ = lean_obj_once(&l_Lean_MVarId_intro1___00__lam__0___closed__1, &l_Lean_MVarId_intro1___00__lam__0___closed__1_once, _init_l_Lean_MVarId_intro1___00__lam__0___closed__1);
v___x_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2236_, 0, v_mvarId_2186_);
v___x_2237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2235_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v___x_2237_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
v___jp_2198_:
{
lean_object* v___x_2203_; 
lean_inc(v_mvarId_2186_);
v___x_2203_ = l_Lean_MVarId_getTag(v_mvarId_2186_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2205_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v___x_2205_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_body_2196_, v_a_2204_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2216_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc_n(v_a_2206_, 2);
lean_dec_ref_known(v___x_2205_, 1);
v___x_2207_ = l_Lean_Expr_lam___override(v_binderName_2194_, v_binderType_2195_, v_a_2206_, v_binderInfo_2197_);
v___x_2208_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_2186_, v___x_2207_, v___y_2200_);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; 
v_unused_2217_ = lean_ctor_get(v___x_2208_, 0);
lean_dec(v_unused_2217_);
v___x_2210_ = v___x_2208_;
v_isShared_2211_ = v_isSharedCheck_2216_;
goto v_resetjp_2209_;
}
else
{
lean_dec(v___x_2208_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2216_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2212_ = l_Lean_Expr_mvarId_x21(v_a_2206_);
lean_dec(v_a_2206_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v___x_2212_);
v___x_2214_ = v___x_2210_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_binderType_2195_);
lean_dec(v_binderName_2194_);
lean_dec(v_mvarId_2186_);
v_a_2218_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2205_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2205_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec_ref(v_body_2196_);
lean_dec_ref(v_binderType_2195_);
lean_dec(v_binderName_2194_);
lean_dec(v_mvarId_2186_);
v_a_2226_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2203_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2203_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
lean_dec(v_a_2193_);
v___x_2247_ = lean_obj_once(&l_Lean_MVarId_intro1___00__lam__0___closed__1, &l_Lean_MVarId_intro1___00__lam__0___closed__1_once, _init_l_Lean_MVarId_intro1___00__lam__0___closed__1);
v___x_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2248_, 0, v_mvarId_2186_);
v___x_2249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2247_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v___x_2249_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
return v___x_2250_;
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec(v_mvarId_2186_);
v_a_2251_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2192_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2192_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_intro1___00__lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2186_ = stack[0].m_obj;
lean_object* v___y_2187_ = stack[1].m_obj;
lean_object* v___y_2188_ = stack[2].m_obj;
lean_object* v___y_2189_ = stack[3].m_obj;
lean_object* v___y_2190_ = stack[4].m_obj;
lean_object* v_res_2259_;
v_res_2259_ = l_Lean_MVarId_intro1___00__lam__0(v_mvarId_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
stack->m_obj
 = v_res_2259_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__lam__0___boxed(lean_object* v_mvarId_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_MVarId_intro1___00__lam__0(v_mvarId_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
return v_res_2266_;
}
}
lean_object* l_Lean_MVarId_intro1__(lean_object* v_mvarId_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v___f_2273_; lean_object* v___x_2274_; 
lean_inc(v_mvarId_2267_);
v___f_2273_ = lean_alloc_closure((void*)(l_Lean_MVarId_intro1___00__lam__0___boxed), 6, 1);
lean_closure_set(v___f_2273_, 0, v_mvarId_2267_);
v___x_2274_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(v_mvarId_2267_, v___f_2273_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
return v___x_2274_;
}
}
LEAN_EXPORT void l_Lean_MVarId_intro1___0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2267_ = stack[0].m_obj;
lean_object* v_a_2268_ = stack[1].m_obj;
lean_object* v_a_2269_ = stack[2].m_obj;
lean_object* v_a_2270_ = stack[3].m_obj;
lean_object* v_a_2271_ = stack[4].m_obj;
lean_object* v_res_2275_;
v_res_2275_ = l_Lean_MVarId_intro1__(v_mvarId_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
stack->m_obj
 = v_res_2275_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1___00__boxed(lean_object* v_mvarId_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_MVarId_intro1__(v_mvarId_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
lean_dec(v_a_2280_);
lean_dec_ref(v_a_2279_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
return v_res_2282_;
}
}
lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(lean_object* v_00_u03b1_2283_, lean_object* v_msg_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(v_msg_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
return v___x_2290_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2284_ = stack[1].m_obj;
lean_object* v___y_2285_ = stack[2].m_obj;
lean_object* v___y_2286_ = stack[3].m_obj;
lean_object* v___y_2287_ = stack[4].m_obj;
lean_object* v___y_2288_ = stack[5].m_obj;
lean_object* v_res_2291_;
v_res_2291_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(lean_box(0), v_msg_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
stack->m_obj
 = v_res_2291_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___boxed(lean_object* v_00_u03b1_2292_, lean_object* v_msg_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(v_00_u03b1_2292_, v_msg_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntrosSize(lean_object* v_x_2300_){
_start:
{
switch(lean_obj_tag(v_x_2300_))
{
case 7:
{
lean_object* v_body_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v_body_2301_ = lean_ctor_get(v_x_2300_, 2);
v___x_2302_ = l_Lean_Meta_getIntrosSize(v_body_2301_);
v___x_2303_ = lean_unsigned_to_nat(1u);
v___x_2304_ = lean_nat_add(v___x_2302_, v___x_2303_);
lean_dec(v___x_2302_);
return v___x_2304_;
}
case 8:
{
lean_object* v_body_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_body_2305_ = lean_ctor_get(v_x_2300_, 3);
v___x_2306_ = l_Lean_Meta_getIntrosSize(v_body_2305_);
v___x_2307_ = lean_unsigned_to_nat(1u);
v___x_2308_ = lean_nat_add(v___x_2306_, v___x_2307_);
lean_dec(v___x_2306_);
return v___x_2308_;
}
case 10:
{
lean_object* v_expr_2309_; 
v_expr_2309_ = lean_ctor_get(v_x_2300_, 1);
v_x_2300_ = v_expr_2309_;
goto _start;
}
default: 
{
lean_object* v___x_2311_; 
v___x_2311_ = lean_unsigned_to_nat(0u);
return v___x_2311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntrosSize___boxed(lean_object* v_x_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_Meta_getIntrosSize(v_x_2312_);
lean_dec_ref(v_x_2312_);
return v_res_2313_;
}
}
lean_object* l_Lean_MVarId_intros(lean_object* v_mvarId_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v___x_2320_; 
lean_inc(v_mvarId_2314_);
v___x_2320_ = l_Lean_MVarId_getType(v_mvarId_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2322_; lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2337_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2322_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_a_2321_, v_a_2316_);
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2337_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2337_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2327_ = l_Lean_Meta_getIntrosSize(v_a_2323_);
lean_dec(v_a_2323_);
v___x_2328_ = lean_unsigned_to_nat(0u);
v___x_2329_ = lean_nat_dec_eq(v___x_2327_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_del_object(v___x_2325_);
v___x_2330_ = lean_box(0);
v___x_2331_ = l_Lean_Meta_introNCore(v_mvarId_2314_, v___x_2327_, v___x_2330_, v___x_2329_, v___x_2329_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
return v___x_2331_;
}
else
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
lean_dec(v___x_2327_);
v___x_2332_ = ((lean_object*)(l_Lean_Meta_introNCore___closed__0));
v___x_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
lean_ctor_set(v___x_2333_, 1, v_mvarId_2314_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2333_);
v___x_2335_ = v___x_2325_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec(v_mvarId_2314_);
v_a_2338_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2320_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2320_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_intros_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2314_ = stack[0].m_obj;
lean_object* v_a_2315_ = stack[1].m_obj;
lean_object* v_a_2316_ = stack[2].m_obj;
lean_object* v_a_2317_ = stack[3].m_obj;
lean_object* v_a_2318_ = stack[4].m_obj;
lean_object* v_res_2346_;
v_res_2346_ = l_Lean_MVarId_intros(v_mvarId_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
stack->m_obj
 = v_res_2346_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intros___boxed(lean_object* v_mvarId_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_MVarId_intros(v_mvarId_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
return v_res_2353_;
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
