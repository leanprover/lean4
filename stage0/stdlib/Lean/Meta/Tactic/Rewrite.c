// Lean compiler output
// Module: Lean.Meta.Tactic.Rewrite
// Imports: Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Meta.KAbstract Lean.Meta.Check Lean.Meta.Tactic.Util Lean.Meta.Tactic.Apply Lean.Meta.BinderNameHint
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__37;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__39;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__35;
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__31;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__49;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__0;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_MVarId_rewrite_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__27;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_MVarId_rewrite_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_MVarId_rewrite_spec__12___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__20;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__2;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__42;
lean_object* l_Lean_MessageData_note(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__7;
lean_object* l_Lean_Expr_resolveBinderNameHint(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__32;
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__17;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__9;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__11;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__14;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__36;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__8;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__38;
uint8_t l_Lean_Expr_hasBinderNameHint(lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__43;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__44;
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_MVarId_rewrite_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_rewrite_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__21;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__45;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13_spec__13___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__29;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__40;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__26;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__28;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Array_contains___at___Lean_MVarId_rewrite_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__46;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tactic_skipAssignedInstances;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__41;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_MVarId_rewrite_spec__7___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_rewrite_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__12;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__34;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__18;
static lean_object* l_Lean_MVarId_rewrite___closed__0;
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__15;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__23;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___Lean_MVarId_rewrite_spec__8(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__24;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Array_contains___at___Lean_MVarId_rewrite_spec__8_spec__8(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__22;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__13;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__47;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__16;
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_MVarId_rewrite_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__33;
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint64_t l_Lean_hashMVarId____x40_Lean_Expr_4051099792____hygCtx___hyg_35_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_rewrite_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__25;
size_t lean_usize_add(size_t, size_t);
static size_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__1;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__48;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__30;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_rewrite_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__3;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lean_MVarId_rewrite_spec__12(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_contains___at___Lean_MVarId_rewrite_spec__8___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13_spec__13(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_MVarId_rewrite_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__10;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__19;
uint8_t l_Lean_beqMVarId____x40_Lean_Expr_4051099792____hygCtx___hyg_18_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_beqMVarId____x40_Lean_Expr_4051099792____hygCtx___hyg_18_(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_5, x_6);
return x_7;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__1;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_beqMVarId____x40_Lean_Expr_4051099792____hygCtx___hyg_18_(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_hashMVarId____x40_Lean_Expr_4051099792____hygCtx___hyg_35_(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 7);
lean_inc_ref(x_9);
lean_dec_ref(x_6);
x_10 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0___redArg(x_9, x_1);
x_11 = lean_box(x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_6, 7);
lean_inc_ref(x_13);
lean_dec_ref(x_6);
x_14 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0___redArg(x_13, x_1);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVarsCore(x_9, x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_st_ref_take(x_2, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_12);
x_18 = lean_st_ref_set(x_2, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_ctor_get(x_14, 2);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_st_ref_set(x_2, x_27, x_15);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_MVarId_rewrite_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
lean_inc_ref(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
lean_inc_ref(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_3, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_4, 2);
lean_inc(x_35);
lean_inc_ref(x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_1);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_rewrite_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_MVarId_rewrite_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_rewrite_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___Lean_MVarId_rewrite_spec__5___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_MVarId_rewrite_spec__7(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Expr_mvarId_x21(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Array_contains___at___Lean_MVarId_rewrite_spec__8_spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_beqMVarId____x40_Lean_Expr_4051099792____hygCtx___hyg_18_(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___Lean_MVarId_rewrite_spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Array_contains___at___Lean_MVarId_rewrite_spec__8_spec__8(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = l_Array_contains___at___Lean_MVarId_rewrite_spec__8(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_push(x_5, x_12);
x_6 = x_14;
goto block_10;
}
else
{
lean_dec(x_12);
x_6 = x_5;
goto block_10;
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_2, x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_array_uget(x_1, x_2);
x_21 = l_Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0___redArg(x_17, x_6, x_9);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec_ref(x_21);
x_18 = x_24;
goto block_20;
}
else
{
lean_object* x_25; 
lean_dec(x_17);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec_ref(x_21);
x_10 = x_4;
x_11 = x_25;
goto block_15;
}
block_20:
{
lean_object* x_19; 
x_19 = lean_array_push(x_4, x_17);
x_10 = x_19;
x_11 = x_18;
goto block_15;
}
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_9);
return x_26;
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lean_MVarId_rewrite_spec__12(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_find(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec_ref(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13_spec__13___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13_spec__13___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13_spec__13___redArg___lam__0), 7, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13_spec__13(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13_spec__13___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = 0;
x_11 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13_spec__13___redArg(x_1, x_9, x_2, x_3, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_MVarId_rewrite_spec__15___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_MVarId_rewrite_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___Lean_MVarId_rewrite_spec__15___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_expr_instantiate1(x_1, x_3);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_10 = lean_infer_type(x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_Meta_isExprDefEq(x_11, x_2, x_4, x_5, x_6, x_7, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid rewrite argument: Expected an equality or iff proof or definition name, but", 83, 83);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("is ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrArg", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_tactic_skipAssignedInstances;
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Motive is dependent:", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The rewrite tactic cannot substitute terms on which the type of the target expression depends. The type of the expression", 121, 121);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\ndepends on the value", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("motive is not type correct:", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__16;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nError: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__18;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nExplanation: The rewrite tactic rewrites an expression 'e' using an equality 'a = b' by the following process. First, it looks for all 'a' in 'e'. Second, it tries to abstract these occurrences of 'a' to create a function 'm := fun _a => ...', called the *motive*, with the property that 'm a' is definitionally equal to 'e'. Third, we observe that '", 352, 352);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__20;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' implies that 'm a = m b', which can be used with lemmas such as '", 67, 67);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__22;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mpr", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__25;
x_2 = l_Lean_MVarId_rewrite___lam__1___closed__24;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' to change the goal. However, if 'e' depends on specific properties of 'a', then the motive 'm' might not typecheck.\n\nPossible solutions: use rewrite's 'occs' configuration option to limit which occurrences are rewritten, or use 'simp' or 'conv' mode, which have strategies for certain kinds of dependencies (these tactics can handle proofs and '", 347, 347);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__27;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Decidable", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__29;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' instances whose types depend on the rewritten term, and 'simp' can apply user-defined '@[congr]' theorems as well).", 117, 117);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__31;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_a", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__33;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Did not find an occurrence of the pattern", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__35;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nin the target expression", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__37;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid rewrite argument: The pattern to be substituted is a metavariable (`", 76, 76);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__39;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`) in this equality", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__41;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a value of type", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a proof of", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Iff", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__45;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("propext", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__47;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_rewrite___lam__1___closed__48;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_69; 
lean_inc(x_2);
lean_inc(x_1);
x_69 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec_ref(x_69);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_3);
x_71 = lean_infer_type(x_3, x_7, x_8, x_9, x_10, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4___redArg(x_72, x_8, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
x_78 = lean_box(0);
x_79 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_80 = l_Lean_Meta_forallMetaTelescopeReducing(x_75, x_78, x_79, x_7, x_8, x_9, x_10, x_76);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_589; lean_object* x_590; lean_object* x_591; uint8_t x_592; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec_ref(x_80);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_85 = x_81;
} else {
 lean_dec_ref(x_81);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_88 = x_82;
} else {
 lean_dec_ref(x_82);
 x_88 = lean_box(0);
}
lean_inc_ref(x_3);
x_589 = l_Lean_mkAppN(x_3, x_84);
x_590 = l_Lean_MVarId_rewrite___lam__1___closed__46;
x_591 = lean_unsigned_to_nat(2u);
x_592 = l_Lean_Expr_isAppOfArity(x_87, x_590, x_591);
if (x_592 == 0)
{
x_539 = x_589;
x_540 = x_87;
x_541 = x_7;
x_542 = x_8;
x_543 = x_9;
x_544 = x_10;
x_545 = x_83;
goto block_588;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_593 = l_Lean_Expr_appFn_x21(x_87);
x_594 = l_Lean_Expr_appArg_x21(x_593);
lean_dec_ref(x_593);
x_595 = l_Lean_Expr_appArg_x21(x_87);
lean_dec(x_87);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_595);
lean_inc_ref(x_594);
x_596 = l_Lean_Meta_mkEq(x_594, x_595, x_7, x_8, x_9, x_10, x_83);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_596, 1);
lean_inc(x_598);
lean_dec_ref(x_596);
x_599 = l_Lean_MVarId_rewrite___lam__1___closed__49;
x_600 = l_Lean_mkApp3(x_599, x_594, x_595, x_589);
x_539 = x_600;
x_540 = x_597;
x_541 = x_7;
x_542 = x_8;
x_543 = x_9;
x_544 = x_10;
x_545 = x_598;
goto block_588;
}
else
{
uint8_t x_601; 
lean_dec_ref(x_595);
lean_dec_ref(x_594);
lean_dec_ref(x_589);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_601 = !lean_is_exclusive(x_596);
if (x_601 == 0)
{
return x_596;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_596, 0);
x_603 = lean_ctor_get(x_596, 1);
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_596);
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
return x_604;
}
}
}
block_116:
{
uint8_t x_97; lean_object* x_98; 
x_97 = 0;
lean_inc(x_89);
lean_inc_ref(x_90);
lean_inc(x_91);
lean_inc_ref(x_92);
x_98 = l_Lean_Meta_postprocessAppMVars(x_2, x_1, x_84, x_86, x_96, x_97, x_92, x_91, x_90, x_89, x_95);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = lean_array_size(x_84);
x_101 = 0;
x_102 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_MVarId_rewrite_spec__7(x_100, x_101, x_84);
x_103 = lean_unsigned_to_nat(0u);
x_104 = lean_array_get_size(x_102);
x_105 = l_Lean_MVarId_rewrite___lam__1___closed__6;
x_106 = lean_nat_dec_lt(x_103, x_104);
if (x_106 == 0)
{
lean_dec(x_104);
lean_dec_ref(x_102);
x_45 = x_89;
x_46 = x_90;
x_47 = x_91;
x_48 = x_101;
x_49 = x_92;
x_50 = x_93;
x_51 = x_103;
x_52 = x_94;
x_53 = x_105;
x_54 = x_99;
goto block_68;
}
else
{
uint8_t x_107; 
x_107 = lean_nat_dec_le(x_104, x_104);
if (x_107 == 0)
{
lean_dec(x_104);
lean_dec_ref(x_102);
x_45 = x_89;
x_46 = x_90;
x_47 = x_91;
x_48 = x_101;
x_49 = x_92;
x_50 = x_93;
x_51 = x_103;
x_52 = x_94;
x_53 = x_105;
x_54 = x_99;
goto block_68;
}
else
{
size_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_usize_of_nat(x_104);
lean_dec(x_104);
x_109 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__11(x_102, x_101, x_108, x_105, x_92, x_91, x_90, x_89, x_99);
lean_dec_ref(x_102);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec_ref(x_109);
x_45 = x_89;
x_46 = x_90;
x_47 = x_91;
x_48 = x_101;
x_49 = x_92;
x_50 = x_93;
x_51 = x_103;
x_52 = x_94;
x_53 = x_110;
x_54 = x_111;
goto block_68;
}
}
}
else
{
uint8_t x_112; 
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_84);
lean_dec_ref(x_3);
x_112 = !lean_is_exclusive(x_98);
if (x_112 == 0)
{
return x_98;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_98, 0);
x_114 = lean_ctor_get(x_98, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_98);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
block_154:
{
lean_object* x_129; 
lean_inc(x_127);
lean_inc_ref(x_126);
lean_inc(x_125);
lean_inc_ref(x_124);
lean_inc_ref(x_118);
x_129 = l_Lean_Meta_getLevel(x_118, x_124, x_125, x_126, x_127, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec_ref(x_129);
lean_inc(x_127);
lean_inc_ref(x_126);
lean_inc(x_125);
lean_inc_ref(x_124);
lean_inc_ref(x_117);
x_132 = l_Lean_Meta_getLevel(x_117, x_124, x_125, x_126, x_127, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec_ref(x_132);
x_135 = lean_ctor_get(x_126, 2);
x_136 = l_Lean_MVarId_rewrite___lam__1___closed__8;
x_137 = lean_box(0);
if (lean_is_scalar(x_88)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_88;
 lean_ctor_set_tag(x_138, 1);
}
lean_ctor_set(x_138, 0, x_133);
lean_ctor_set(x_138, 1, x_137);
if (lean_is_scalar(x_85)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_85;
 lean_ctor_set_tag(x_139, 1);
}
lean_ctor_set(x_139, 0, x_130);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Lean_Expr_const___override(x_136, x_139);
x_141 = l_Lean_mkApp6(x_140, x_118, x_117, x_119, x_123, x_120, x_122);
x_142 = l_Lean_MVarId_rewrite___lam__1___closed__9;
x_143 = l_Lean_Option_get___at___Lean_MVarId_rewrite_spec__12(x_135, x_142);
if (x_143 == 0)
{
uint8_t x_144; 
x_144 = 1;
x_89 = x_127;
x_90 = x_126;
x_91 = x_125;
x_92 = x_124;
x_93 = x_141;
x_94 = x_121;
x_95 = x_134;
x_96 = x_144;
goto block_116;
}
else
{
uint8_t x_145; 
x_145 = 0;
x_89 = x_127;
x_90 = x_126;
x_91 = x_125;
x_92 = x_124;
x_93 = x_141;
x_94 = x_121;
x_95 = x_134;
x_96 = x_145;
goto block_116;
}
}
else
{
uint8_t x_146; 
lean_dec(x_130);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec_ref(x_123);
lean_dec_ref(x_122);
lean_dec_ref(x_121);
lean_dec_ref(x_120);
lean_dec_ref(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_132);
if (x_146 == 0)
{
return x_132;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_132, 0);
x_148 = lean_ctor_get(x_132, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_132);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec_ref(x_123);
lean_dec_ref(x_122);
lean_dec_ref(x_121);
lean_dec_ref(x_120);
lean_dec_ref(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_129);
if (x_150 == 0)
{
return x_129;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_129, 0);
x_152 = lean_ctor_get(x_129, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_129);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
block_207:
{
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec_ref(x_169);
lean_inc(x_159);
lean_inc_ref(x_160);
lean_inc(x_157);
lean_inc_ref(x_158);
lean_inc_ref(x_162);
x_171 = l_Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13___redArg(x_163, x_162, x_167, x_158, x_157, x_160, x_159, x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; uint8_t x_173; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_unbox(x_172);
lean_dec(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec_ref(x_171);
x_175 = l_Lean_MVarId_rewrite___lam__1___closed__11;
lean_inc_ref(x_164);
x_176 = l_Lean_MessageData_ofExpr(x_164);
x_177 = l_Lean_indentD(x_176);
if (lean_is_scalar(x_77)) {
 x_178 = lean_alloc_ctor(7, 2, 0);
} else {
 x_178 = x_77;
 lean_ctor_set_tag(x_178, 7);
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_177);
x_179 = l_Lean_MVarId_rewrite___lam__1___closed__5;
x_180 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = l_Lean_MVarId_rewrite___lam__1___closed__13;
x_182 = l_Lean_indentExpr(x_161);
x_183 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = l_Lean_MVarId_rewrite___lam__1___closed__15;
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
lean_inc_ref(x_156);
x_186 = l_Lean_indentExpr(x_156);
x_187 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_179);
x_189 = l_Lean_MessageData_note(x_188);
x_190 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_190, 0, x_180);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_190);
lean_inc(x_1);
lean_inc(x_2);
x_192 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_191, x_158, x_157, x_160, x_159, x_174);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec_ref(x_192);
x_117 = x_155;
x_118 = x_162;
x_119 = x_156;
x_120 = x_164;
x_121 = x_165;
x_122 = x_166;
x_123 = x_168;
x_124 = x_158;
x_125 = x_157;
x_126 = x_160;
x_127 = x_159;
x_128 = x_193;
goto block_154;
}
else
{
uint8_t x_194; 
lean_dec_ref(x_168);
lean_dec_ref(x_166);
lean_dec_ref(x_165);
lean_dec_ref(x_164);
lean_dec_ref(x_162);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec_ref(x_155);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = !lean_is_exclusive(x_192);
if (x_194 == 0)
{
return x_192;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_192, 0);
x_196 = lean_ctor_get(x_192, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_192);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
lean_object* x_198; 
lean_dec_ref(x_161);
lean_dec(x_77);
x_198 = lean_ctor_get(x_171, 1);
lean_inc(x_198);
lean_dec_ref(x_171);
x_117 = x_155;
x_118 = x_162;
x_119 = x_156;
x_120 = x_164;
x_121 = x_165;
x_122 = x_166;
x_123 = x_168;
x_124 = x_158;
x_125 = x_157;
x_126 = x_160;
x_127 = x_159;
x_128 = x_198;
goto block_154;
}
}
else
{
uint8_t x_199; 
lean_dec_ref(x_168);
lean_dec_ref(x_166);
lean_dec_ref(x_165);
lean_dec_ref(x_164);
lean_dec_ref(x_162);
lean_dec_ref(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec_ref(x_155);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_171);
if (x_199 == 0)
{
return x_171;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_171, 0);
x_201 = lean_ctor_get(x_171, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_171);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
uint8_t x_203; 
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec_ref(x_166);
lean_dec_ref(x_165);
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec_ref(x_162);
lean_dec_ref(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec_ref(x_155);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_203 = !lean_is_exclusive(x_169);
if (x_203 == 0)
{
return x_169;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_169, 0);
x_205 = lean_ctor_get(x_169, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_169);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
block_253:
{
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec_ref(x_217);
x_226 = l_Lean_MVarId_rewrite___lam__1___closed__17;
lean_inc_ref(x_220);
x_227 = l_Lean_MessageData_ofExpr(x_220);
x_228 = l_Lean_indentD(x_227);
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_228);
x_230 = l_Lean_MVarId_rewrite___lam__1___closed__19;
x_231 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
x_232 = l_Lean_Exception_toMessageData(x_214);
x_233 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
x_234 = l_Lean_MVarId_rewrite___lam__1___closed__21;
x_235 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
x_236 = l_Lean_MVarId_rewrite___lam__1___closed__8;
x_237 = l_Lean_MessageData_ofConstName(x_236, x_225);
x_238 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_237);
x_239 = l_Lean_MVarId_rewrite___lam__1___closed__23;
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = l_Lean_MVarId_rewrite___lam__1___closed__26;
x_242 = l_Lean_MessageData_ofConstName(x_241, x_225);
x_243 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lean_MVarId_rewrite___lam__1___closed__28;
x_245 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = l_Lean_MVarId_rewrite___lam__1___closed__30;
x_247 = l_Lean_MessageData_ofConstName(x_246, x_225);
x_248 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_247);
x_249 = l_Lean_MVarId_rewrite___lam__1___closed__32;
x_250 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_251, 0, x_250);
lean_inc(x_1);
lean_inc(x_2);
x_252 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_251, x_211, x_210, x_213, x_212, x_215);
x_155 = x_208;
x_156 = x_209;
x_157 = x_210;
x_158 = x_211;
x_159 = x_212;
x_160 = x_213;
x_161 = x_216;
x_162 = x_218;
x_163 = x_219;
x_164 = x_220;
x_165 = x_221;
x_166 = x_222;
x_167 = x_223;
x_168 = x_224;
x_169 = x_252;
goto block_207;
}
else
{
lean_dec_ref(x_214);
x_155 = x_208;
x_156 = x_209;
x_157 = x_210;
x_158 = x_211;
x_159 = x_212;
x_160 = x_213;
x_161 = x_216;
x_162 = x_218;
x_163 = x_219;
x_164 = x_220;
x_165 = x_221;
x_166 = x_222;
x_167 = x_223;
x_168 = x_224;
x_169 = x_217;
goto block_207;
}
}
block_283:
{
lean_object* x_267; 
lean_inc(x_265);
lean_inc_ref(x_264);
lean_inc(x_263);
lean_inc_ref(x_262);
lean_inc_ref(x_258);
x_267 = lean_infer_type(x_258, x_262, x_263, x_264, x_265, x_266);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; lean_object* x_274; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec_ref(x_267);
lean_inc(x_268);
x_270 = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__0___boxed), 8, 2);
lean_closure_set(x_270, 0, x_254);
lean_closure_set(x_270, 1, x_268);
x_271 = l_Lean_MVarId_rewrite___lam__1___closed__34;
x_272 = 0;
lean_inc_ref(x_255);
x_273 = l_Lean_mkLambda(x_271, x_272, x_255, x_257);
lean_inc(x_265);
lean_inc_ref(x_264);
lean_inc(x_263);
lean_inc_ref(x_262);
lean_inc_ref(x_273);
x_274 = l_Lean_Meta_check(x_273, x_262, x_263, x_264, x_265, x_269);
if (lean_obj_tag(x_274) == 0)
{
x_155 = x_268;
x_156 = x_256;
x_157 = x_263;
x_158 = x_262;
x_159 = x_265;
x_160 = x_264;
x_161 = x_258;
x_162 = x_255;
x_163 = x_271;
x_164 = x_273;
x_165 = x_261;
x_166 = x_259;
x_167 = x_270;
x_168 = x_260;
x_169 = x_274;
goto block_207;
}
else
{
lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
x_277 = l_Lean_Exception_isInterrupt(x_275);
if (x_277 == 0)
{
uint8_t x_278; 
x_278 = l_Lean_Exception_isRuntime(x_275);
x_208 = x_268;
x_209 = x_256;
x_210 = x_263;
x_211 = x_262;
x_212 = x_265;
x_213 = x_264;
x_214 = x_275;
x_215 = x_276;
x_216 = x_258;
x_217 = x_274;
x_218 = x_255;
x_219 = x_271;
x_220 = x_273;
x_221 = x_261;
x_222 = x_259;
x_223 = x_270;
x_224 = x_260;
x_225 = x_278;
goto block_253;
}
else
{
x_208 = x_268;
x_209 = x_256;
x_210 = x_263;
x_211 = x_262;
x_212 = x_265;
x_213 = x_264;
x_214 = x_275;
x_215 = x_276;
x_216 = x_258;
x_217 = x_274;
x_218 = x_255;
x_219 = x_271;
x_220 = x_273;
x_221 = x_261;
x_222 = x_259;
x_223 = x_270;
x_224 = x_260;
x_225 = x_277;
goto block_253;
}
}
}
else
{
uint8_t x_279; 
lean_dec(x_265);
lean_dec_ref(x_264);
lean_dec(x_263);
lean_dec_ref(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec_ref(x_255);
lean_dec_ref(x_254);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_279 = !lean_is_exclusive(x_267);
if (x_279 == 0)
{
return x_267;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_267, 0);
x_281 = lean_ctor_get(x_267, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_267);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
}
block_307:
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_295 = lean_expr_instantiate1(x_284, x_289);
x_296 = l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4___redArg(x_295, x_291, x_294);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec_ref(x_296);
x_299 = l_Lean_Expr_hasBinderNameHint(x_289);
if (x_299 == 0)
{
lean_inc_ref(x_284);
x_254 = x_284;
x_255 = x_285;
x_256 = x_286;
x_257 = x_284;
x_258 = x_287;
x_259 = x_288;
x_260 = x_289;
x_261 = x_297;
x_262 = x_290;
x_263 = x_291;
x_264 = x_292;
x_265 = x_293;
x_266 = x_298;
goto block_283;
}
else
{
lean_object* x_300; 
lean_inc(x_293);
lean_inc_ref(x_292);
x_300 = l_Lean_Expr_resolveBinderNameHint(x_297, x_292, x_293, x_298);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec_ref(x_300);
lean_inc_ref(x_284);
x_254 = x_284;
x_255 = x_285;
x_256 = x_286;
x_257 = x_284;
x_258 = x_287;
x_259 = x_288;
x_260 = x_289;
x_261 = x_301;
x_262 = x_290;
x_263 = x_291;
x_264 = x_292;
x_265 = x_293;
x_266 = x_302;
goto block_283;
}
else
{
uint8_t x_303; 
lean_dec(x_293);
lean_dec_ref(x_292);
lean_dec(x_291);
lean_dec_ref(x_290);
lean_dec_ref(x_289);
lean_dec_ref(x_288);
lean_dec_ref(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec_ref(x_284);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_303 = !lean_is_exclusive(x_300);
if (x_303 == 0)
{
return x_300;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_300, 0);
x_305 = lean_ctor_get(x_300, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_300);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
return x_306;
}
}
}
}
block_538:
{
lean_object* x_318; uint8_t x_319; 
x_318 = l_Lean_Expr_getAppFn(x_311);
x_319 = l_Lean_Expr_isMVar(x_318);
lean_dec_ref(x_318);
if (x_319 == 0)
{
lean_object* x_320; uint8_t x_321; 
lean_dec_ref(x_310);
x_320 = l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4___redArg(x_4, x_314, x_317);
x_321 = !lean_is_exclusive(x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; uint8_t x_324; uint8_t x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_322 = lean_ctor_get(x_320, 0);
x_323 = lean_ctor_get(x_320, 1);
x_324 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_325 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_326 = lean_ctor_get(x_5, 0);
lean_inc(x_326);
lean_dec_ref(x_5);
x_327 = l_Lean_Meta_Context_config(x_313);
x_328 = !lean_is_exclusive(x_327);
if (x_328 == 0)
{
uint8_t x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; uint8_t x_337; uint64_t x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_329 = lean_ctor_get_uint8(x_313, sizeof(void*)*7);
x_330 = lean_ctor_get(x_313, 1);
x_331 = lean_ctor_get(x_313, 2);
x_332 = lean_ctor_get(x_313, 3);
x_333 = lean_ctor_get(x_313, 4);
x_334 = lean_ctor_get(x_313, 5);
x_335 = lean_ctor_get(x_313, 6);
x_336 = lean_ctor_get_uint8(x_313, sizeof(void*)*7 + 1);
x_337 = lean_ctor_get_uint8(x_313, sizeof(void*)*7 + 2);
lean_ctor_set_uint8(x_327, 8, x_325);
lean_ctor_set_uint8(x_327, 9, x_324);
x_338 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_327);
x_339 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_339, 0, x_327);
lean_ctor_set_uint64(x_339, sizeof(void*)*1, x_338);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
lean_inc_ref(x_332);
lean_inc_ref(x_331);
lean_inc(x_330);
x_340 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_330);
lean_ctor_set(x_340, 2, x_331);
lean_ctor_set(x_340, 3, x_332);
lean_ctor_set(x_340, 4, x_333);
lean_ctor_set(x_340, 5, x_334);
lean_ctor_set(x_340, 6, x_335);
lean_ctor_set_uint8(x_340, sizeof(void*)*7, x_329);
lean_ctor_set_uint8(x_340, sizeof(void*)*7 + 1, x_336);
lean_ctor_set_uint8(x_340, sizeof(void*)*7 + 2, x_337);
lean_inc(x_316);
lean_inc_ref(x_315);
lean_inc(x_314);
lean_inc_ref(x_311);
lean_inc(x_322);
x_341 = l_Lean_Meta_kabstract(x_322, x_311, x_326, x_340, x_314, x_315, x_316, x_323);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec_ref(x_341);
x_344 = l_Lean_Expr_hasLooseBVars(x_342);
if (x_344 == 0)
{
lean_object* x_345; 
lean_inc(x_316);
lean_inc_ref(x_315);
lean_inc(x_314);
lean_inc_ref(x_313);
lean_inc_ref(x_311);
lean_inc(x_322);
x_345 = l_Lean_Meta_addPPExplicitToExposeDiff(x_322, x_311, x_313, x_314, x_315, x_316, x_343);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec_ref(x_345);
x_348 = !lean_is_exclusive(x_346);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_349 = lean_ctor_get(x_346, 0);
x_350 = lean_ctor_get(x_346, 1);
x_351 = l_Lean_MVarId_rewrite___lam__1___closed__36;
x_352 = l_Lean_indentExpr(x_350);
lean_ctor_set_tag(x_346, 7);
lean_ctor_set(x_346, 1, x_352);
lean_ctor_set(x_346, 0, x_351);
x_353 = l_Lean_MVarId_rewrite___lam__1___closed__38;
lean_ctor_set_tag(x_320, 7);
lean_ctor_set(x_320, 1, x_353);
lean_ctor_set(x_320, 0, x_346);
x_354 = l_Lean_indentExpr(x_349);
x_355 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_355, 0, x_320);
lean_ctor_set(x_355, 1, x_354);
x_356 = l_Lean_MVarId_rewrite___lam__1___closed__5;
x_357 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
x_358 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_358, 0, x_357);
lean_inc(x_1);
lean_inc(x_2);
x_359 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_358, x_313, x_314, x_315, x_316, x_347);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; 
x_360 = lean_ctor_get(x_359, 1);
lean_inc(x_360);
lean_dec_ref(x_359);
x_284 = x_342;
x_285 = x_308;
x_286 = x_311;
x_287 = x_322;
x_288 = x_309;
x_289 = x_312;
x_290 = x_313;
x_291 = x_314;
x_292 = x_315;
x_293 = x_316;
x_294 = x_360;
goto block_307;
}
else
{
uint8_t x_361; 
lean_dec(x_342);
lean_dec(x_322);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec_ref(x_312);
lean_dec_ref(x_311);
lean_dec_ref(x_309);
lean_dec_ref(x_308);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_361 = !lean_is_exclusive(x_359);
if (x_361 == 0)
{
return x_359;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_359, 0);
x_363 = lean_ctor_get(x_359, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_359);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_365 = lean_ctor_get(x_346, 0);
x_366 = lean_ctor_get(x_346, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_346);
x_367 = l_Lean_MVarId_rewrite___lam__1___closed__36;
x_368 = l_Lean_indentExpr(x_366);
x_369 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
x_370 = l_Lean_MVarId_rewrite___lam__1___closed__38;
lean_ctor_set_tag(x_320, 7);
lean_ctor_set(x_320, 1, x_370);
lean_ctor_set(x_320, 0, x_369);
x_371 = l_Lean_indentExpr(x_365);
x_372 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_372, 0, x_320);
lean_ctor_set(x_372, 1, x_371);
x_373 = l_Lean_MVarId_rewrite___lam__1___closed__5;
x_374 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_374);
lean_inc(x_1);
lean_inc(x_2);
x_376 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_375, x_313, x_314, x_315, x_316, x_347);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; 
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
lean_dec_ref(x_376);
x_284 = x_342;
x_285 = x_308;
x_286 = x_311;
x_287 = x_322;
x_288 = x_309;
x_289 = x_312;
x_290 = x_313;
x_291 = x_314;
x_292 = x_315;
x_293 = x_316;
x_294 = x_377;
goto block_307;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_342);
lean_dec(x_322);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec_ref(x_312);
lean_dec_ref(x_311);
lean_dec_ref(x_309);
lean_dec_ref(x_308);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_378 = lean_ctor_get(x_376, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_376, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_380 = x_376;
} else {
 lean_dec_ref(x_376);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_378);
lean_ctor_set(x_381, 1, x_379);
return x_381;
}
}
}
else
{
uint8_t x_382; 
lean_dec(x_342);
lean_free_object(x_320);
lean_dec(x_322);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec_ref(x_312);
lean_dec_ref(x_311);
lean_dec_ref(x_309);
lean_dec_ref(x_308);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_382 = !lean_is_exclusive(x_345);
if (x_382 == 0)
{
return x_345;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_345, 0);
x_384 = lean_ctor_get(x_345, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_345);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
return x_385;
}
}
}
else
{
lean_free_object(x_320);
x_284 = x_342;
x_285 = x_308;
x_286 = x_311;
x_287 = x_322;
x_288 = x_309;
x_289 = x_312;
x_290 = x_313;
x_291 = x_314;
x_292 = x_315;
x_293 = x_316;
x_294 = x_343;
goto block_307;
}
}
else
{
uint8_t x_386; 
lean_free_object(x_320);
lean_dec(x_322);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec_ref(x_312);
lean_dec_ref(x_311);
lean_dec_ref(x_309);
lean_dec_ref(x_308);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_386 = !lean_is_exclusive(x_341);
if (x_386 == 0)
{
return x_341;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_341, 0);
x_388 = lean_ctor_get(x_341, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_341);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
}
else
{
uint8_t x_390; uint8_t x_391; uint8_t x_392; uint8_t x_393; uint8_t x_394; uint8_t x_395; uint8_t x_396; uint8_t x_397; uint8_t x_398; uint8_t x_399; uint8_t x_400; uint8_t x_401; uint8_t x_402; uint8_t x_403; uint8_t x_404; uint8_t x_405; uint8_t x_406; uint8_t x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; uint8_t x_415; lean_object* x_416; uint64_t x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_390 = lean_ctor_get_uint8(x_327, 0);
x_391 = lean_ctor_get_uint8(x_327, 1);
x_392 = lean_ctor_get_uint8(x_327, 2);
x_393 = lean_ctor_get_uint8(x_327, 3);
x_394 = lean_ctor_get_uint8(x_327, 4);
x_395 = lean_ctor_get_uint8(x_327, 5);
x_396 = lean_ctor_get_uint8(x_327, 6);
x_397 = lean_ctor_get_uint8(x_327, 7);
x_398 = lean_ctor_get_uint8(x_327, 10);
x_399 = lean_ctor_get_uint8(x_327, 11);
x_400 = lean_ctor_get_uint8(x_327, 12);
x_401 = lean_ctor_get_uint8(x_327, 13);
x_402 = lean_ctor_get_uint8(x_327, 14);
x_403 = lean_ctor_get_uint8(x_327, 15);
x_404 = lean_ctor_get_uint8(x_327, 16);
x_405 = lean_ctor_get_uint8(x_327, 17);
x_406 = lean_ctor_get_uint8(x_327, 18);
lean_dec(x_327);
x_407 = lean_ctor_get_uint8(x_313, sizeof(void*)*7);
x_408 = lean_ctor_get(x_313, 1);
x_409 = lean_ctor_get(x_313, 2);
x_410 = lean_ctor_get(x_313, 3);
x_411 = lean_ctor_get(x_313, 4);
x_412 = lean_ctor_get(x_313, 5);
x_413 = lean_ctor_get(x_313, 6);
x_414 = lean_ctor_get_uint8(x_313, sizeof(void*)*7 + 1);
x_415 = lean_ctor_get_uint8(x_313, sizeof(void*)*7 + 2);
x_416 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_416, 0, x_390);
lean_ctor_set_uint8(x_416, 1, x_391);
lean_ctor_set_uint8(x_416, 2, x_392);
lean_ctor_set_uint8(x_416, 3, x_393);
lean_ctor_set_uint8(x_416, 4, x_394);
lean_ctor_set_uint8(x_416, 5, x_395);
lean_ctor_set_uint8(x_416, 6, x_396);
lean_ctor_set_uint8(x_416, 7, x_397);
lean_ctor_set_uint8(x_416, 8, x_325);
lean_ctor_set_uint8(x_416, 9, x_324);
lean_ctor_set_uint8(x_416, 10, x_398);
lean_ctor_set_uint8(x_416, 11, x_399);
lean_ctor_set_uint8(x_416, 12, x_400);
lean_ctor_set_uint8(x_416, 13, x_401);
lean_ctor_set_uint8(x_416, 14, x_402);
lean_ctor_set_uint8(x_416, 15, x_403);
lean_ctor_set_uint8(x_416, 16, x_404);
lean_ctor_set_uint8(x_416, 17, x_405);
lean_ctor_set_uint8(x_416, 18, x_406);
x_417 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_416);
x_418 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set_uint64(x_418, sizeof(void*)*1, x_417);
lean_inc(x_413);
lean_inc(x_412);
lean_inc(x_411);
lean_inc_ref(x_410);
lean_inc_ref(x_409);
lean_inc(x_408);
x_419 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_408);
lean_ctor_set(x_419, 2, x_409);
lean_ctor_set(x_419, 3, x_410);
lean_ctor_set(x_419, 4, x_411);
lean_ctor_set(x_419, 5, x_412);
lean_ctor_set(x_419, 6, x_413);
lean_ctor_set_uint8(x_419, sizeof(void*)*7, x_407);
lean_ctor_set_uint8(x_419, sizeof(void*)*7 + 1, x_414);
lean_ctor_set_uint8(x_419, sizeof(void*)*7 + 2, x_415);
lean_inc(x_316);
lean_inc_ref(x_315);
lean_inc(x_314);
lean_inc_ref(x_311);
lean_inc(x_322);
x_420 = l_Lean_Meta_kabstract(x_322, x_311, x_326, x_419, x_314, x_315, x_316, x_323);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec_ref(x_420);
x_423 = l_Lean_Expr_hasLooseBVars(x_421);
if (x_423 == 0)
{
lean_object* x_424; 
lean_inc(x_316);
lean_inc_ref(x_315);
lean_inc(x_314);
lean_inc_ref(x_313);
lean_inc_ref(x_311);
lean_inc(x_322);
x_424 = l_Lean_Meta_addPPExplicitToExposeDiff(x_322, x_311, x_313, x_314, x_315, x_316, x_422);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec_ref(x_424);
x_427 = lean_ctor_get(x_425, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_425, 1);
lean_inc(x_428);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 x_429 = x_425;
} else {
 lean_dec_ref(x_425);
 x_429 = lean_box(0);
}
x_430 = l_Lean_MVarId_rewrite___lam__1___closed__36;
x_431 = l_Lean_indentExpr(x_428);
if (lean_is_scalar(x_429)) {
 x_432 = lean_alloc_ctor(7, 2, 0);
} else {
 x_432 = x_429;
 lean_ctor_set_tag(x_432, 7);
}
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
x_433 = l_Lean_MVarId_rewrite___lam__1___closed__38;
lean_ctor_set_tag(x_320, 7);
lean_ctor_set(x_320, 1, x_433);
lean_ctor_set(x_320, 0, x_432);
x_434 = l_Lean_indentExpr(x_427);
x_435 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_435, 0, x_320);
lean_ctor_set(x_435, 1, x_434);
x_436 = l_Lean_MVarId_rewrite___lam__1___closed__5;
x_437 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
x_438 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_438, 0, x_437);
lean_inc(x_1);
lean_inc(x_2);
x_439 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_438, x_313, x_314, x_315, x_316, x_426);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; 
x_440 = lean_ctor_get(x_439, 1);
lean_inc(x_440);
lean_dec_ref(x_439);
x_284 = x_421;
x_285 = x_308;
x_286 = x_311;
x_287 = x_322;
x_288 = x_309;
x_289 = x_312;
x_290 = x_313;
x_291 = x_314;
x_292 = x_315;
x_293 = x_316;
x_294 = x_440;
goto block_307;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_421);
lean_dec(x_322);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec_ref(x_312);
lean_dec_ref(x_311);
lean_dec_ref(x_309);
lean_dec_ref(x_308);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_441 = lean_ctor_get(x_439, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_439, 1);
lean_inc(x_442);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_443 = x_439;
} else {
 lean_dec_ref(x_439);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(1, 2, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_441);
lean_ctor_set(x_444, 1, x_442);
return x_444;
}
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_421);
lean_free_object(x_320);
lean_dec(x_322);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec_ref(x_312);
lean_dec_ref(x_311);
lean_dec_ref(x_309);
lean_dec_ref(x_308);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_445 = lean_ctor_get(x_424, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_424, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 x_447 = x_424;
} else {
 lean_dec_ref(x_424);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 2, 0);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_446);
return x_448;
}
}
else
{
lean_free_object(x_320);
x_284 = x_421;
x_285 = x_308;
x_286 = x_311;
x_287 = x_322;
x_288 = x_309;
x_289 = x_312;
x_290 = x_313;
x_291 = x_314;
x_292 = x_315;
x_293 = x_316;
x_294 = x_422;
goto block_307;
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_free_object(x_320);
lean_dec(x_322);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec_ref(x_312);
lean_dec_ref(x_311);
lean_dec_ref(x_309);
lean_dec_ref(x_308);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_449 = lean_ctor_get(x_420, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_420, 1);
lean_inc(x_450);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_451 = x_420;
} else {
 lean_dec_ref(x_420);
 x_451 = lean_box(0);
}
if (lean_is_scalar(x_451)) {
 x_452 = lean_alloc_ctor(1, 2, 0);
} else {
 x_452 = x_451;
}
lean_ctor_set(x_452, 0, x_449);
lean_ctor_set(x_452, 1, x_450);
return x_452;
}
}
}
else
{
lean_object* x_453; lean_object* x_454; uint8_t x_455; uint8_t x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; uint8_t x_460; uint8_t x_461; uint8_t x_462; uint8_t x_463; uint8_t x_464; uint8_t x_465; uint8_t x_466; uint8_t x_467; uint8_t x_468; uint8_t x_469; uint8_t x_470; uint8_t x_471; uint8_t x_472; uint8_t x_473; uint8_t x_474; uint8_t x_475; lean_object* x_476; uint8_t x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; uint8_t x_485; lean_object* x_486; uint64_t x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_453 = lean_ctor_get(x_320, 0);
x_454 = lean_ctor_get(x_320, 1);
lean_inc(x_454);
lean_inc(x_453);
lean_dec(x_320);
x_455 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_456 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_457 = lean_ctor_get(x_5, 0);
lean_inc(x_457);
lean_dec_ref(x_5);
x_458 = l_Lean_Meta_Context_config(x_313);
x_459 = lean_ctor_get_uint8(x_458, 0);
x_460 = lean_ctor_get_uint8(x_458, 1);
x_461 = lean_ctor_get_uint8(x_458, 2);
x_462 = lean_ctor_get_uint8(x_458, 3);
x_463 = lean_ctor_get_uint8(x_458, 4);
x_464 = lean_ctor_get_uint8(x_458, 5);
x_465 = lean_ctor_get_uint8(x_458, 6);
x_466 = lean_ctor_get_uint8(x_458, 7);
x_467 = lean_ctor_get_uint8(x_458, 10);
x_468 = lean_ctor_get_uint8(x_458, 11);
x_469 = lean_ctor_get_uint8(x_458, 12);
x_470 = lean_ctor_get_uint8(x_458, 13);
x_471 = lean_ctor_get_uint8(x_458, 14);
x_472 = lean_ctor_get_uint8(x_458, 15);
x_473 = lean_ctor_get_uint8(x_458, 16);
x_474 = lean_ctor_get_uint8(x_458, 17);
x_475 = lean_ctor_get_uint8(x_458, 18);
if (lean_is_exclusive(x_458)) {
 x_476 = x_458;
} else {
 lean_dec_ref(x_458);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get_uint8(x_313, sizeof(void*)*7);
x_478 = lean_ctor_get(x_313, 1);
x_479 = lean_ctor_get(x_313, 2);
x_480 = lean_ctor_get(x_313, 3);
x_481 = lean_ctor_get(x_313, 4);
x_482 = lean_ctor_get(x_313, 5);
x_483 = lean_ctor_get(x_313, 6);
x_484 = lean_ctor_get_uint8(x_313, sizeof(void*)*7 + 1);
x_485 = lean_ctor_get_uint8(x_313, sizeof(void*)*7 + 2);
if (lean_is_scalar(x_476)) {
 x_486 = lean_alloc_ctor(0, 0, 19);
} else {
 x_486 = x_476;
}
lean_ctor_set_uint8(x_486, 0, x_459);
lean_ctor_set_uint8(x_486, 1, x_460);
lean_ctor_set_uint8(x_486, 2, x_461);
lean_ctor_set_uint8(x_486, 3, x_462);
lean_ctor_set_uint8(x_486, 4, x_463);
lean_ctor_set_uint8(x_486, 5, x_464);
lean_ctor_set_uint8(x_486, 6, x_465);
lean_ctor_set_uint8(x_486, 7, x_466);
lean_ctor_set_uint8(x_486, 8, x_456);
lean_ctor_set_uint8(x_486, 9, x_455);
lean_ctor_set_uint8(x_486, 10, x_467);
lean_ctor_set_uint8(x_486, 11, x_468);
lean_ctor_set_uint8(x_486, 12, x_469);
lean_ctor_set_uint8(x_486, 13, x_470);
lean_ctor_set_uint8(x_486, 14, x_471);
lean_ctor_set_uint8(x_486, 15, x_472);
lean_ctor_set_uint8(x_486, 16, x_473);
lean_ctor_set_uint8(x_486, 17, x_474);
lean_ctor_set_uint8(x_486, 18, x_475);
x_487 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_486);
x_488 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set_uint64(x_488, sizeof(void*)*1, x_487);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
lean_inc_ref(x_480);
lean_inc_ref(x_479);
lean_inc(x_478);
x_489 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_478);
lean_ctor_set(x_489, 2, x_479);
lean_ctor_set(x_489, 3, x_480);
lean_ctor_set(x_489, 4, x_481);
lean_ctor_set(x_489, 5, x_482);
lean_ctor_set(x_489, 6, x_483);
lean_ctor_set_uint8(x_489, sizeof(void*)*7, x_477);
lean_ctor_set_uint8(x_489, sizeof(void*)*7 + 1, x_484);
lean_ctor_set_uint8(x_489, sizeof(void*)*7 + 2, x_485);
lean_inc(x_316);
lean_inc_ref(x_315);
lean_inc(x_314);
lean_inc_ref(x_311);
lean_inc(x_453);
x_490 = l_Lean_Meta_kabstract(x_453, x_311, x_457, x_489, x_314, x_315, x_316, x_454);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; uint8_t x_493; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec_ref(x_490);
x_493 = l_Lean_Expr_hasLooseBVars(x_491);
if (x_493 == 0)
{
lean_object* x_494; 
lean_inc(x_316);
lean_inc_ref(x_315);
lean_inc(x_314);
lean_inc_ref(x_313);
lean_inc_ref(x_311);
lean_inc(x_453);
x_494 = l_Lean_Meta_addPPExplicitToExposeDiff(x_453, x_311, x_313, x_314, x_315, x_316, x_492);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec_ref(x_494);
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_495, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_499 = x_495;
} else {
 lean_dec_ref(x_495);
 x_499 = lean_box(0);
}
x_500 = l_Lean_MVarId_rewrite___lam__1___closed__36;
x_501 = l_Lean_indentExpr(x_498);
if (lean_is_scalar(x_499)) {
 x_502 = lean_alloc_ctor(7, 2, 0);
} else {
 x_502 = x_499;
 lean_ctor_set_tag(x_502, 7);
}
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_501);
x_503 = l_Lean_MVarId_rewrite___lam__1___closed__38;
x_504 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_503);
x_505 = l_Lean_indentExpr(x_497);
x_506 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_505);
x_507 = l_Lean_MVarId_rewrite___lam__1___closed__5;
x_508 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_508, 0, x_506);
lean_ctor_set(x_508, 1, x_507);
x_509 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_509, 0, x_508);
lean_inc(x_1);
lean_inc(x_2);
x_510 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_509, x_313, x_314, x_315, x_316, x_496);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; 
x_511 = lean_ctor_get(x_510, 1);
lean_inc(x_511);
lean_dec_ref(x_510);
x_284 = x_491;
x_285 = x_308;
x_286 = x_311;
x_287 = x_453;
x_288 = x_309;
x_289 = x_312;
x_290 = x_313;
x_291 = x_314;
x_292 = x_315;
x_293 = x_316;
x_294 = x_511;
goto block_307;
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_491);
lean_dec(x_453);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec_ref(x_312);
lean_dec_ref(x_311);
lean_dec_ref(x_309);
lean_dec_ref(x_308);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_512 = lean_ctor_get(x_510, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_510, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_510)) {
 lean_ctor_release(x_510, 0);
 lean_ctor_release(x_510, 1);
 x_514 = x_510;
} else {
 lean_dec_ref(x_510);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(1, 2, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_512);
lean_ctor_set(x_515, 1, x_513);
return x_515;
}
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
lean_dec(x_491);
lean_dec(x_453);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec_ref(x_312);
lean_dec_ref(x_311);
lean_dec_ref(x_309);
lean_dec_ref(x_308);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_516 = lean_ctor_get(x_494, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_494, 1);
lean_inc(x_517);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_518 = x_494;
} else {
 lean_dec_ref(x_494);
 x_518 = lean_box(0);
}
if (lean_is_scalar(x_518)) {
 x_519 = lean_alloc_ctor(1, 2, 0);
} else {
 x_519 = x_518;
}
lean_ctor_set(x_519, 0, x_516);
lean_ctor_set(x_519, 1, x_517);
return x_519;
}
}
else
{
x_284 = x_491;
x_285 = x_308;
x_286 = x_311;
x_287 = x_453;
x_288 = x_309;
x_289 = x_312;
x_290 = x_313;
x_291 = x_314;
x_292 = x_315;
x_293 = x_316;
x_294 = x_492;
goto block_307;
}
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
lean_dec(x_453);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec_ref(x_312);
lean_dec_ref(x_311);
lean_dec_ref(x_309);
lean_dec_ref(x_308);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_520 = lean_ctor_get(x_490, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_490, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 x_522 = x_490;
} else {
 lean_dec_ref(x_490);
 x_522 = lean_box(0);
}
if (lean_is_scalar(x_522)) {
 x_523 = lean_alloc_ctor(1, 2, 0);
} else {
 x_523 = x_522;
}
lean_ctor_set(x_523, 0, x_520);
lean_ctor_set(x_523, 1, x_521);
return x_523;
}
}
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; uint8_t x_534; 
lean_dec_ref(x_312);
lean_dec_ref(x_309);
lean_dec_ref(x_308);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_524 = l_Lean_MVarId_rewrite___lam__1___closed__40;
x_525 = l_Lean_MessageData_ofExpr(x_311);
x_526 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_526, 0, x_524);
lean_ctor_set(x_526, 1, x_525);
x_527 = l_Lean_MVarId_rewrite___lam__1___closed__42;
x_528 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_528, 0, x_526);
lean_ctor_set(x_528, 1, x_527);
x_529 = l_Lean_indentExpr(x_310);
x_530 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_530, 0, x_528);
lean_ctor_set(x_530, 1, x_529);
x_531 = l_Lean_MVarId_rewrite___lam__1___closed__5;
x_532 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_532, 0, x_530);
lean_ctor_set(x_532, 1, x_531);
x_533 = l_Lean_throwError___at___Lean_MVarId_rewrite_spec__5___redArg(x_532, x_313, x_314, x_315, x_316, x_317);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
x_534 = !lean_is_exclusive(x_533);
if (x_534 == 0)
{
return x_533;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_535 = lean_ctor_get(x_533, 0);
x_536 = lean_ctor_get(x_533, 1);
lean_inc(x_536);
lean_inc(x_535);
lean_dec(x_533);
x_537 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_537, 0, x_535);
lean_ctor_set(x_537, 1, x_536);
return x_537;
}
}
}
block_588:
{
lean_object* x_546; 
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
lean_inc_ref(x_540);
x_546 = l_Lean_Meta_matchEq_x3f(x_540, x_541, x_542, x_543, x_544, x_545);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; 
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; lean_object* x_549; 
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec_ref(x_546);
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
lean_inc_ref(x_540);
x_549 = l_Lean_Meta_isProp(x_540, x_541, x_542, x_543, x_544, x_548);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; uint8_t x_551; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
x_551 = lean_unbox(x_550);
lean_dec(x_550);
if (x_551 == 0)
{
lean_object* x_552; lean_object* x_553; 
x_552 = lean_ctor_get(x_549, 1);
lean_inc(x_552);
lean_dec_ref(x_549);
x_553 = l_Lean_MVarId_rewrite___lam__1___closed__43;
x_12 = x_543;
x_13 = x_540;
x_14 = x_552;
x_15 = x_544;
x_16 = x_539;
x_17 = x_542;
x_18 = x_541;
x_19 = x_553;
goto block_34;
}
else
{
lean_object* x_554; lean_object* x_555; 
x_554 = lean_ctor_get(x_549, 1);
lean_inc(x_554);
lean_dec_ref(x_549);
x_555 = l_Lean_MVarId_rewrite___lam__1___closed__44;
x_12 = x_543;
x_13 = x_540;
x_14 = x_554;
x_15 = x_544;
x_16 = x_539;
x_17 = x_542;
x_18 = x_541;
x_19 = x_555;
goto block_34;
}
}
else
{
uint8_t x_556; 
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec_ref(x_540);
lean_dec_ref(x_539);
x_556 = !lean_is_exclusive(x_549);
if (x_556 == 0)
{
return x_549;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_557 = lean_ctor_get(x_549, 0);
x_558 = lean_ctor_get(x_549, 1);
lean_inc(x_558);
lean_inc(x_557);
lean_dec(x_549);
x_559 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_559, 0, x_557);
lean_ctor_set(x_559, 1, x_558);
return x_559;
}
}
}
else
{
lean_object* x_560; lean_object* x_561; 
x_560 = lean_ctor_get(x_547, 0);
lean_inc(x_560);
lean_dec_ref(x_547);
x_561 = lean_ctor_get(x_560, 1);
lean_inc(x_561);
if (x_6 == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_562 = lean_ctor_get(x_546, 1);
lean_inc(x_562);
lean_dec_ref(x_546);
x_563 = lean_ctor_get(x_560, 0);
lean_inc(x_563);
lean_dec(x_560);
x_564 = lean_ctor_get(x_561, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_561, 1);
lean_inc(x_565);
lean_dec(x_561);
x_308 = x_563;
x_309 = x_539;
x_310 = x_540;
x_311 = x_564;
x_312 = x_565;
x_313 = x_541;
x_314 = x_542;
x_315 = x_543;
x_316 = x_544;
x_317 = x_562;
goto block_538;
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
lean_dec_ref(x_540);
x_566 = lean_ctor_get(x_546, 1);
lean_inc(x_566);
lean_dec_ref(x_546);
x_567 = lean_ctor_get(x_560, 0);
lean_inc(x_567);
lean_dec(x_560);
x_568 = lean_ctor_get(x_561, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_561, 1);
lean_inc(x_569);
lean_dec(x_561);
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
x_570 = l_Lean_Meta_mkEqSymm(x_539, x_541, x_542, x_543, x_544, x_566);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
lean_dec_ref(x_570);
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
lean_inc(x_568);
lean_inc(x_569);
x_573 = l_Lean_Meta_mkEq(x_569, x_568, x_541, x_542, x_543, x_544, x_572);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec_ref(x_573);
x_308 = x_567;
x_309 = x_571;
x_310 = x_574;
x_311 = x_569;
x_312 = x_568;
x_313 = x_541;
x_314 = x_542;
x_315 = x_543;
x_316 = x_544;
x_317 = x_575;
goto block_538;
}
else
{
uint8_t x_576; 
lean_dec(x_571);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_567);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_576 = !lean_is_exclusive(x_573);
if (x_576 == 0)
{
return x_573;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_577 = lean_ctor_get(x_573, 0);
x_578 = lean_ctor_get(x_573, 1);
lean_inc(x_578);
lean_inc(x_577);
lean_dec(x_573);
x_579 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_579, 0, x_577);
lean_ctor_set(x_579, 1, x_578);
return x_579;
}
}
}
else
{
uint8_t x_580; 
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_567);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_580 = !lean_is_exclusive(x_570);
if (x_580 == 0)
{
return x_570;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_581 = lean_ctor_get(x_570, 0);
x_582 = lean_ctor_get(x_570, 1);
lean_inc(x_582);
lean_inc(x_581);
lean_dec(x_570);
x_583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_583, 0, x_581);
lean_ctor_set(x_583, 1, x_582);
return x_583;
}
}
}
}
}
else
{
uint8_t x_584; 
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec_ref(x_540);
lean_dec_ref(x_539);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_77);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_584 = !lean_is_exclusive(x_546);
if (x_584 == 0)
{
return x_546;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_546, 0);
x_586 = lean_ctor_get(x_546, 1);
lean_inc(x_586);
lean_inc(x_585);
lean_dec(x_546);
x_587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set(x_587, 1, x_586);
return x_587;
}
}
}
}
else
{
uint8_t x_605; 
lean_dec(x_77);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_605 = !lean_is_exclusive(x_80);
if (x_605 == 0)
{
return x_80;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_606 = lean_ctor_get(x_80, 0);
x_607 = lean_ctor_get(x_80, 1);
lean_inc(x_607);
lean_inc(x_606);
lean_dec(x_80);
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_606);
lean_ctor_set(x_608, 1, x_607);
return x_608;
}
}
}
else
{
uint8_t x_609; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_609 = !lean_is_exclusive(x_71);
if (x_609 == 0)
{
return x_71;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_610 = lean_ctor_get(x_71, 0);
x_611 = lean_ctor_get(x_71, 1);
lean_inc(x_611);
lean_inc(x_610);
lean_dec(x_71);
x_612 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_612, 0, x_610);
lean_ctor_set(x_612, 1, x_611);
return x_612;
}
}
}
else
{
uint8_t x_613; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_613 = !lean_is_exclusive(x_69);
if (x_613 == 0)
{
return x_69;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_ctor_get(x_69, 0);
x_615 = lean_ctor_get(x_69, 1);
lean_inc(x_615);
lean_inc(x_614);
lean_dec(x_69);
x_616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_616, 0, x_614);
lean_ctor_set(x_616, 1, x_615);
return x_616;
}
}
block_34:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = l_Lean_MVarId_rewrite___lam__1___closed__1;
x_21 = lean_unsigned_to_nat(30u);
x_22 = l_Lean_inlineExpr(x_16, x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_MVarId_rewrite___lam__1___closed__3;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_stringToMessageData(x_19);
lean_dec_ref(x_19);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MVarId_rewrite___lam__1___closed__5;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_indentExpr(x_13);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
x_33 = l_Lean_throwError___at___Lean_MVarId_rewrite_spec__5___redArg(x_32, x_18, x_17, x_12, x_15, x_14);
lean_dec(x_15);
lean_dec_ref(x_12);
lean_dec(x_17);
lean_dec_ref(x_18);
return x_33;
}
block_44:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = l_Array_append___redArg(x_37, x_39);
lean_dec_ref(x_39);
x_41 = lean_array_to_list(x_40);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_35);
return x_43;
}
block_68:
{
lean_object* x_55; 
x_55 = l_Lean_Meta_getMVarsNoDelayed(x_3, x_49, x_47, x_46, x_45, x_54);
lean_dec(x_45);
lean_dec_ref(x_46);
lean_dec(x_47);
lean_dec_ref(x_49);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_array_get_size(x_56);
x_59 = lean_mk_empty_array_with_capacity(x_51);
x_60 = lean_nat_dec_lt(x_51, x_58);
if (x_60 == 0)
{
lean_dec(x_58);
lean_dec(x_56);
x_35 = x_57;
x_36 = x_50;
x_37 = x_53;
x_38 = x_52;
x_39 = x_59;
goto block_44;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_58, x_58);
if (x_61 == 0)
{
lean_dec(x_58);
lean_dec(x_56);
x_35 = x_57;
x_36 = x_50;
x_37 = x_53;
x_38 = x_52;
x_39 = x_59;
goto block_44;
}
else
{
size_t x_62; lean_object* x_63; 
x_62 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_63 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__10(x_53, x_56, x_48, x_62, x_59);
lean_dec(x_56);
x_35 = x_57;
x_36 = x_50;
x_37 = x_53;
x_38 = x_52;
x_39 = x_63;
goto block_44;
}
}
}
else
{
uint8_t x_64; 
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_50);
x_64 = !lean_is_exclusive(x_55);
if (x_64 == 0)
{
return x_55;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_55, 0);
x_66 = lean_ctor_get(x_55, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_55);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rewrite", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_MVarId_rewrite___closed__1;
x_12 = lean_box(x_4);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__1___boxed), 11, 6);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_2);
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_12);
x_14 = l_Lean_MVarId_withContext___at___Lean_MVarId_rewrite_spec__15___redArg(x_1, x_13, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_MVarId_rewrite_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_MVarId_rewrite_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_rewrite_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_MVarId_rewrite_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_rewrite_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___Lean_MVarId_rewrite_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_MVarId_rewrite_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_MVarId_rewrite_spec__7(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Array_contains___at___Lean_MVarId_rewrite_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Array_contains___at___Lean_MVarId_rewrite_spec__8_spec__8(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___Lean_MVarId_rewrite_spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___Lean_MVarId_rewrite_spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__10(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__11(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_MVarId_rewrite_spec__12___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___Lean_MVarId_rewrite_spec__12(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13_spec__13___redArg(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13_spec__13(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_rewrite___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
x_13 = l_Lean_MVarId_rewrite___lam__1(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_MVarId_rewrite(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_BinderNameHint(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KAbstract(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_BinderNameHint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__1();
l_Lean_MVarId_rewrite___lam__1___closed__0 = _init_l_Lean_MVarId_rewrite___lam__1___closed__0();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__0);
l_Lean_MVarId_rewrite___lam__1___closed__1 = _init_l_Lean_MVarId_rewrite___lam__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__1);
l_Lean_MVarId_rewrite___lam__1___closed__2 = _init_l_Lean_MVarId_rewrite___lam__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__2);
l_Lean_MVarId_rewrite___lam__1___closed__3 = _init_l_Lean_MVarId_rewrite___lam__1___closed__3();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__3);
l_Lean_MVarId_rewrite___lam__1___closed__4 = _init_l_Lean_MVarId_rewrite___lam__1___closed__4();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__4);
l_Lean_MVarId_rewrite___lam__1___closed__5 = _init_l_Lean_MVarId_rewrite___lam__1___closed__5();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__5);
l_Lean_MVarId_rewrite___lam__1___closed__6 = _init_l_Lean_MVarId_rewrite___lam__1___closed__6();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__6);
l_Lean_MVarId_rewrite___lam__1___closed__7 = _init_l_Lean_MVarId_rewrite___lam__1___closed__7();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__7);
l_Lean_MVarId_rewrite___lam__1___closed__8 = _init_l_Lean_MVarId_rewrite___lam__1___closed__8();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__8);
l_Lean_MVarId_rewrite___lam__1___closed__9 = _init_l_Lean_MVarId_rewrite___lam__1___closed__9();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__9);
l_Lean_MVarId_rewrite___lam__1___closed__10 = _init_l_Lean_MVarId_rewrite___lam__1___closed__10();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__10);
l_Lean_MVarId_rewrite___lam__1___closed__11 = _init_l_Lean_MVarId_rewrite___lam__1___closed__11();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__11);
l_Lean_MVarId_rewrite___lam__1___closed__12 = _init_l_Lean_MVarId_rewrite___lam__1___closed__12();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__12);
l_Lean_MVarId_rewrite___lam__1___closed__13 = _init_l_Lean_MVarId_rewrite___lam__1___closed__13();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__13);
l_Lean_MVarId_rewrite___lam__1___closed__14 = _init_l_Lean_MVarId_rewrite___lam__1___closed__14();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__14);
l_Lean_MVarId_rewrite___lam__1___closed__15 = _init_l_Lean_MVarId_rewrite___lam__1___closed__15();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__15);
l_Lean_MVarId_rewrite___lam__1___closed__16 = _init_l_Lean_MVarId_rewrite___lam__1___closed__16();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__16);
l_Lean_MVarId_rewrite___lam__1___closed__17 = _init_l_Lean_MVarId_rewrite___lam__1___closed__17();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__17);
l_Lean_MVarId_rewrite___lam__1___closed__18 = _init_l_Lean_MVarId_rewrite___lam__1___closed__18();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__18);
l_Lean_MVarId_rewrite___lam__1___closed__19 = _init_l_Lean_MVarId_rewrite___lam__1___closed__19();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__19);
l_Lean_MVarId_rewrite___lam__1___closed__20 = _init_l_Lean_MVarId_rewrite___lam__1___closed__20();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__20);
l_Lean_MVarId_rewrite___lam__1___closed__21 = _init_l_Lean_MVarId_rewrite___lam__1___closed__21();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__21);
l_Lean_MVarId_rewrite___lam__1___closed__22 = _init_l_Lean_MVarId_rewrite___lam__1___closed__22();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__22);
l_Lean_MVarId_rewrite___lam__1___closed__23 = _init_l_Lean_MVarId_rewrite___lam__1___closed__23();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__23);
l_Lean_MVarId_rewrite___lam__1___closed__24 = _init_l_Lean_MVarId_rewrite___lam__1___closed__24();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__24);
l_Lean_MVarId_rewrite___lam__1___closed__25 = _init_l_Lean_MVarId_rewrite___lam__1___closed__25();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__25);
l_Lean_MVarId_rewrite___lam__1___closed__26 = _init_l_Lean_MVarId_rewrite___lam__1___closed__26();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__26);
l_Lean_MVarId_rewrite___lam__1___closed__27 = _init_l_Lean_MVarId_rewrite___lam__1___closed__27();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__27);
l_Lean_MVarId_rewrite___lam__1___closed__28 = _init_l_Lean_MVarId_rewrite___lam__1___closed__28();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__28);
l_Lean_MVarId_rewrite___lam__1___closed__29 = _init_l_Lean_MVarId_rewrite___lam__1___closed__29();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__29);
l_Lean_MVarId_rewrite___lam__1___closed__30 = _init_l_Lean_MVarId_rewrite___lam__1___closed__30();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__30);
l_Lean_MVarId_rewrite___lam__1___closed__31 = _init_l_Lean_MVarId_rewrite___lam__1___closed__31();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__31);
l_Lean_MVarId_rewrite___lam__1___closed__32 = _init_l_Lean_MVarId_rewrite___lam__1___closed__32();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__32);
l_Lean_MVarId_rewrite___lam__1___closed__33 = _init_l_Lean_MVarId_rewrite___lam__1___closed__33();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__33);
l_Lean_MVarId_rewrite___lam__1___closed__34 = _init_l_Lean_MVarId_rewrite___lam__1___closed__34();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__34);
l_Lean_MVarId_rewrite___lam__1___closed__35 = _init_l_Lean_MVarId_rewrite___lam__1___closed__35();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__35);
l_Lean_MVarId_rewrite___lam__1___closed__36 = _init_l_Lean_MVarId_rewrite___lam__1___closed__36();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__36);
l_Lean_MVarId_rewrite___lam__1___closed__37 = _init_l_Lean_MVarId_rewrite___lam__1___closed__37();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__37);
l_Lean_MVarId_rewrite___lam__1___closed__38 = _init_l_Lean_MVarId_rewrite___lam__1___closed__38();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__38);
l_Lean_MVarId_rewrite___lam__1___closed__39 = _init_l_Lean_MVarId_rewrite___lam__1___closed__39();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__39);
l_Lean_MVarId_rewrite___lam__1___closed__40 = _init_l_Lean_MVarId_rewrite___lam__1___closed__40();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__40);
l_Lean_MVarId_rewrite___lam__1___closed__41 = _init_l_Lean_MVarId_rewrite___lam__1___closed__41();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__41);
l_Lean_MVarId_rewrite___lam__1___closed__42 = _init_l_Lean_MVarId_rewrite___lam__1___closed__42();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__42);
l_Lean_MVarId_rewrite___lam__1___closed__43 = _init_l_Lean_MVarId_rewrite___lam__1___closed__43();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__43);
l_Lean_MVarId_rewrite___lam__1___closed__44 = _init_l_Lean_MVarId_rewrite___lam__1___closed__44();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__44);
l_Lean_MVarId_rewrite___lam__1___closed__45 = _init_l_Lean_MVarId_rewrite___lam__1___closed__45();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__45);
l_Lean_MVarId_rewrite___lam__1___closed__46 = _init_l_Lean_MVarId_rewrite___lam__1___closed__46();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__46);
l_Lean_MVarId_rewrite___lam__1___closed__47 = _init_l_Lean_MVarId_rewrite___lam__1___closed__47();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__47);
l_Lean_MVarId_rewrite___lam__1___closed__48 = _init_l_Lean_MVarId_rewrite___lam__1___closed__48();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__48);
l_Lean_MVarId_rewrite___lam__1___closed__49 = _init_l_Lean_MVarId_rewrite___lam__1___closed__49();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__49);
l_Lean_MVarId_rewrite___closed__0 = _init_l_Lean_MVarId_rewrite___closed__0();
lean_mark_persistent(l_Lean_MVarId_rewrite___closed__0);
l_Lean_MVarId_rewrite___closed__1 = _init_l_Lean_MVarId_rewrite___closed__1();
lean_mark_persistent(l_Lean_MVarId_rewrite___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
