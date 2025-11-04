// Lean compiler output
// Module: Lean.Meta.Tactic.Rewrite
// Imports: public import Lean.Meta.AppBuilder public import Lean.Meta.MatchUtil public import Lean.Meta.KAbstract public import Lean.Meta.Tactic.Apply public import Lean.Meta.BinderNameHint
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
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__37;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__39;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__35;
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__31;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__0;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__27;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__12___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__20;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__2;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__42;
lean_object* l_Lean_MessageData_note(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__7;
lean_object* l_Lean_Expr_resolveBinderNameHint(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__32;
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__38;
uint8_t l_Lean_Expr_hasBinderNameHint(lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__43;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__44;
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__21;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__45;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__29;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__40;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__26;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__28;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__46;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tactic_skipAssignedInstances;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__41;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__7___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__12;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__34;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__18;
static lean_object* l_Lean_MVarId_rewrite___closed__0;
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__15;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__23;
LEAN_EXPORT lean_object* l_Lean_Meta_RewriteResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_MVarId_rewrite_spec__8(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__24;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__8_spec__8(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__22;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__13;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__47;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__16;
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__33;
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__25;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_RewriteResult_ctorIdx(lean_object*);
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__30;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__3;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__12(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_MVarId_rewrite_spec__8___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__10;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__19;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RewriteResult_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RewriteResult_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_RewriteResult_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = l_Lean_instBEqMVarId_beq(x_3, x_6);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_5, x_6);
return x_7;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__1;
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
x_12 = l_Lean_instBEqMVarId_beq(x_3, x_11);
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
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableMVarId_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 7);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(x_6, x_1);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__4___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__5___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__7(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__8_spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_instBEqMVarId_beq(x_1, x_6);
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
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_MVarId_rewrite_spec__8(lean_object* x_1, lean_object* x_2) {
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
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__8_spec__8(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = l_Array_contains___at___00Lean_MVarId_rewrite_spec__8(x_1, x_12);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_2, x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_array_uget(x_1, x_2);
x_21 = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(x_17, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
x_18 = lean_box(0);
goto block_20;
}
else
{
lean_dec(x_17);
x_10 = x_4;
x_11 = lean_box(0);
goto block_15;
}
block_20:
{
lean_object* x_19; 
x_19 = lean_array_push(x_4, x_17);
x_10 = x_19;
x_11 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_4);
return x_24;
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__12(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = 0;
x_11 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13___redArg(x_1, x_9, x_2, x_3, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__15___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__15___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_expr_instantiate1(x_1, x_3);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_10 = lean_infer_type(x_9, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_Meta_isExprDefEq(x_11, x_2, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrArg", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_tactic_skipAssignedInstances;
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Motive is dependent:", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The rewrite tactic cannot substitute terms on which the type of the target expression depends. The type of the expression", 121, 121);
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
x_1 = lean_mk_string_unchecked("\ndepends on the value", 21, 21);
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
x_1 = lean_mk_string_unchecked("motive is not type correct:", 27, 27);
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
x_1 = lean_mk_string_unchecked("\nError: ", 8, 8);
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
x_1 = lean_mk_string_unchecked("\n\nExplanation: The rewrite tactic rewrites an expression 'e' using an equality 'a = b' by the following process. First, it looks for all 'a' in 'e'. Second, it tries to abstract these occurrences of 'a' to create a function 'm := fun _a => ...', called the *motive*, with the property that 'm a' is definitionally equal to 'e'. Third, we observe that '", 352, 352);
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
x_1 = lean_mk_string_unchecked("' implies that 'm a = m b', which can be used with lemmas such as '", 67, 67);
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
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mpr", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__23;
x_2 = l_Lean_MVarId_rewrite___lam__1___closed__22;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' to change the goal. However, if 'e' depends on specific properties of 'a', then the motive 'm' might not typecheck.\n\nPossible solutions: use rewrite's 'occs' configuration option to limit which occurrences are rewritten, or use 'simp' or 'conv' mode, which have strategies for certain kinds of dependencies (these tactics can handle proofs and '", 347, 347);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__25;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Decidable", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__27;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' instances whose types depend on the rewritten term, and 'simp' can apply user-defined '@[congr]' theorems as well).", 117, 117);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__29;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_a", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__31;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Did not find an occurrence of the pattern", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__33;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nin the target expression", 25, 25);
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
x_1 = lean_mk_string_unchecked("Invalid rewrite argument: The pattern to be substituted is a metavariable (`", 76, 76);
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
x_1 = lean_mk_string_unchecked("`) in this equality", 19, 19);
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
x_1 = lean_mk_string_unchecked("a value of type", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a proof of", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Iff", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__43;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("propext", 7, 7);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_rewrite___lam__1___closed__46;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_64; 
lean_inc(x_2);
lean_inc(x_1);
x_64 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
lean_dec_ref(x_64);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_3);
x_65 = lean_infer_type(x_3, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__4___redArg(x_66, x_8);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
x_71 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_72 = l_Lean_Meta_forallMetaTelescopeReducing(x_68, x_70, x_71, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_79 = x_74;
} else {
 lean_dec_ref(x_74);
 x_79 = lean_box(0);
}
lean_inc_ref(x_3);
x_513 = l_Lean_mkAppN(x_3, x_75);
x_514 = l_Lean_MVarId_rewrite___lam__1___closed__44;
x_515 = lean_unsigned_to_nat(2u);
x_516 = l_Lean_Expr_isAppOfArity(x_78, x_514, x_515);
if (x_516 == 0)
{
x_474 = x_513;
x_475 = x_78;
x_476 = x_7;
x_477 = x_8;
x_478 = x_9;
x_479 = x_10;
x_480 = lean_box(0);
goto block_512;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_517 = l_Lean_Expr_appFn_x21(x_78);
x_518 = l_Lean_Expr_appArg_x21(x_517);
lean_dec_ref(x_517);
x_519 = l_Lean_Expr_appArg_x21(x_78);
lean_dec(x_78);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_519);
lean_inc_ref(x_518);
x_520 = l_Lean_Meta_mkEq(x_518, x_519, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
lean_dec_ref(x_520);
x_522 = l_Lean_MVarId_rewrite___lam__1___closed__47;
x_523 = l_Lean_mkApp3(x_522, x_518, x_519, x_513);
x_474 = x_523;
x_475 = x_521;
x_476 = x_7;
x_477 = x_8;
x_478 = x_9;
x_479 = x_10;
x_480 = lean_box(0);
goto block_512;
}
else
{
uint8_t x_524; 
lean_dec_ref(x_519);
lean_dec_ref(x_518);
lean_dec_ref(x_513);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_524 = !lean_is_exclusive(x_520);
if (x_524 == 0)
{
return x_520;
}
else
{
lean_object* x_525; lean_object* x_526; 
x_525 = lean_ctor_get(x_520, 0);
lean_inc(x_525);
lean_dec(x_520);
x_526 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_526, 0, x_525);
return x_526;
}
}
}
block_104:
{
uint8_t x_88; lean_object* x_89; 
x_88 = 0;
lean_inc(x_82);
lean_inc_ref(x_86);
lean_inc(x_85);
lean_inc_ref(x_81);
x_89 = l_Lean_Meta_postprocessAppMVars(x_2, x_1, x_75, x_77, x_87, x_88, x_81, x_85, x_86, x_82);
if (lean_obj_tag(x_89) == 0)
{
size_t x_90; size_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_dec_ref(x_89);
x_90 = lean_array_size(x_75);
x_91 = 0;
x_92 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__7(x_90, x_91, x_75);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_array_get_size(x_92);
x_95 = l_Lean_MVarId_rewrite___lam__1___closed__4;
x_96 = lean_nat_dec_lt(x_93, x_94);
if (x_96 == 0)
{
lean_dec(x_94);
lean_dec_ref(x_92);
x_42 = x_80;
x_43 = x_91;
x_44 = x_81;
x_45 = x_82;
x_46 = x_93;
x_47 = x_83;
x_48 = x_85;
x_49 = x_86;
x_50 = x_95;
x_51 = lean_box(0);
goto block_63;
}
else
{
uint8_t x_97; 
x_97 = lean_nat_dec_le(x_94, x_94);
if (x_97 == 0)
{
lean_dec(x_94);
lean_dec_ref(x_92);
x_42 = x_80;
x_43 = x_91;
x_44 = x_81;
x_45 = x_82;
x_46 = x_93;
x_47 = x_83;
x_48 = x_85;
x_49 = x_86;
x_50 = x_95;
x_51 = lean_box(0);
goto block_63;
}
else
{
size_t x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_usize_of_nat(x_94);
lean_dec(x_94);
x_99 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__11(x_92, x_91, x_98, x_95, x_81, x_85, x_86, x_82);
lean_dec_ref(x_92);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_42 = x_80;
x_43 = x_91;
x_44 = x_81;
x_45 = x_82;
x_46 = x_93;
x_47 = x_83;
x_48 = x_85;
x_49 = x_86;
x_50 = x_100;
x_51 = lean_box(0);
goto block_63;
}
}
}
else
{
uint8_t x_101; 
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec_ref(x_80);
lean_dec(x_75);
lean_dec_ref(x_3);
x_101 = !lean_is_exclusive(x_89);
if (x_101 == 0)
{
return x_89;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_89, 0);
lean_inc(x_102);
lean_dec(x_89);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
block_138:
{
lean_object* x_117; 
lean_inc(x_115);
lean_inc_ref(x_114);
lean_inc(x_113);
lean_inc_ref(x_112);
lean_inc_ref(x_109);
x_117 = l_Lean_Meta_getLevel(x_109, x_112, x_113, x_114, x_115);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
lean_inc(x_115);
lean_inc_ref(x_114);
lean_inc(x_113);
lean_inc_ref(x_112);
lean_inc_ref(x_106);
x_119 = l_Lean_Meta_getLevel(x_106, x_112, x_113, x_114, x_115);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = lean_ctor_get(x_114, 2);
x_122 = l_Lean_MVarId_rewrite___lam__1___closed__6;
x_123 = lean_box(0);
if (lean_is_scalar(x_79)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_79;
 lean_ctor_set_tag(x_124, 1);
}
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
if (lean_is_scalar(x_76)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_76;
 lean_ctor_set_tag(x_125, 1);
}
lean_ctor_set(x_125, 0, x_118);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_Expr_const___override(x_122, x_125);
x_127 = l_Lean_mkApp6(x_126, x_109, x_106, x_111, x_110, x_107, x_108);
x_128 = l_Lean_MVarId_rewrite___lam__1___closed__7;
x_129 = l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__12(x_121, x_128);
if (x_129 == 0)
{
uint8_t x_130; 
x_130 = 1;
x_80 = x_105;
x_81 = x_112;
x_82 = x_115;
x_83 = x_127;
x_84 = lean_box(0);
x_85 = x_113;
x_86 = x_114;
x_87 = x_130;
goto block_104;
}
else
{
uint8_t x_131; 
x_131 = 0;
x_80 = x_105;
x_81 = x_112;
x_82 = x_115;
x_83 = x_127;
x_84 = lean_box(0);
x_85 = x_113;
x_86 = x_114;
x_87 = x_131;
goto block_104;
}
}
else
{
uint8_t x_132; 
lean_dec(x_118);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_105);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_119);
if (x_132 == 0)
{
return x_119;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_119, 0);
lean_inc(x_133);
lean_dec(x_119);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_105);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_117);
if (x_135 == 0)
{
return x_117;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_117, 0);
lean_inc(x_136);
lean_dec(x_117);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
}
block_181:
{
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
lean_dec_ref(x_153);
lean_inc(x_147);
lean_inc_ref(x_139);
lean_inc(x_144);
lean_inc_ref(x_141);
lean_inc_ref(x_150);
x_154 = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13___redArg(x_142, x_150, x_151, x_141, x_144, x_139, x_147);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; uint8_t x_156; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec_ref(x_154);
x_156 = lean_unbox(x_155);
lean_dec(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_157 = l_Lean_MVarId_rewrite___lam__1___closed__9;
lean_inc_ref(x_140);
x_158 = l_Lean_MessageData_ofExpr(x_140);
x_159 = l_Lean_indentD(x_158);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_MVarId_rewrite___lam__1___closed__11;
x_162 = l_Lean_indentExpr(x_148);
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_MVarId_rewrite___lam__1___closed__13;
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
lean_inc_ref(x_152);
x_166 = l_Lean_indentExpr(x_152);
x_167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_MessageData_note(x_167);
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_160);
lean_ctor_set(x_169, 1, x_168);
if (lean_is_scalar(x_69)) {
 x_170 = lean_alloc_ctor(1, 1, 0);
} else {
 x_170 = x_69;
 lean_ctor_set_tag(x_170, 1);
}
lean_ctor_set(x_170, 0, x_169);
lean_inc(x_1);
lean_inc(x_2);
x_171 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_170, x_141, x_144, x_139, x_147);
if (lean_obj_tag(x_171) == 0)
{
lean_dec_ref(x_171);
x_105 = x_145;
x_106 = x_146;
x_107 = x_140;
x_108 = x_149;
x_109 = x_150;
x_110 = x_143;
x_111 = x_152;
x_112 = x_141;
x_113 = x_144;
x_114 = x_139;
x_115 = x_147;
x_116 = lean_box(0);
goto block_138;
}
else
{
uint8_t x_172; 
lean_dec_ref(x_152);
lean_dec_ref(x_150);
lean_dec_ref(x_149);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_141);
lean_dec_ref(x_140);
lean_dec_ref(x_139);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
return x_171;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_173);
return x_174;
}
}
}
else
{
lean_dec_ref(x_148);
lean_dec(x_69);
x_105 = x_145;
x_106 = x_146;
x_107 = x_140;
x_108 = x_149;
x_109 = x_150;
x_110 = x_143;
x_111 = x_152;
x_112 = x_141;
x_113 = x_144;
x_114 = x_139;
x_115 = x_147;
x_116 = lean_box(0);
goto block_138;
}
}
else
{
uint8_t x_175; 
lean_dec_ref(x_152);
lean_dec_ref(x_150);
lean_dec_ref(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_141);
lean_dec_ref(x_140);
lean_dec_ref(x_139);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_154);
if (x_175 == 0)
{
return x_154;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_154, 0);
lean_inc(x_176);
lean_dec(x_154);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_176);
return x_177;
}
}
}
else
{
uint8_t x_178; 
lean_dec_ref(x_152);
lean_dec_ref(x_151);
lean_dec_ref(x_150);
lean_dec_ref(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_140);
lean_dec_ref(x_139);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_178 = !lean_is_exclusive(x_153);
if (x_178 == 0)
{
return x_153;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_153, 0);
lean_inc(x_179);
lean_dec(x_153);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_179);
return x_180;
}
}
}
block_227:
{
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec_ref(x_186);
x_200 = l_Lean_MVarId_rewrite___lam__1___closed__15;
lean_inc_ref(x_183);
x_201 = l_Lean_MessageData_ofExpr(x_183);
x_202 = l_Lean_indentD(x_201);
x_203 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_202);
x_204 = l_Lean_MVarId_rewrite___lam__1___closed__17;
x_205 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = l_Lean_Exception_toMessageData(x_187);
x_207 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = l_Lean_MVarId_rewrite___lam__1___closed__19;
x_209 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = l_Lean_MVarId_rewrite___lam__1___closed__6;
x_211 = l_Lean_MessageData_ofConstName(x_210, x_199);
x_212 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_MVarId_rewrite___lam__1___closed__21;
x_214 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_215 = l_Lean_MVarId_rewrite___lam__1___closed__24;
x_216 = l_Lean_MessageData_ofConstName(x_215, x_199);
x_217 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_216);
x_218 = l_Lean_MVarId_rewrite___lam__1___closed__26;
x_219 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Lean_MVarId_rewrite___lam__1___closed__28;
x_221 = l_Lean_MessageData_ofConstName(x_220, x_199);
x_222 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_221);
x_223 = l_Lean_MVarId_rewrite___lam__1___closed__30;
x_224 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_225, 0, x_224);
lean_inc(x_1);
lean_inc(x_2);
x_226 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_225, x_184, x_190, x_182, x_193);
x_139 = x_182;
x_140 = x_183;
x_141 = x_184;
x_142 = x_185;
x_143 = x_188;
x_144 = x_190;
x_145 = x_191;
x_146 = x_192;
x_147 = x_193;
x_148 = x_194;
x_149 = x_195;
x_150 = x_196;
x_151 = x_197;
x_152 = x_198;
x_153 = x_226;
goto block_181;
}
else
{
lean_dec_ref(x_187);
x_139 = x_182;
x_140 = x_183;
x_141 = x_184;
x_142 = x_185;
x_143 = x_188;
x_144 = x_190;
x_145 = x_191;
x_146 = x_192;
x_147 = x_193;
x_148 = x_194;
x_149 = x_195;
x_150 = x_196;
x_151 = x_197;
x_152 = x_198;
x_153 = x_186;
goto block_181;
}
}
block_254:
{
lean_object* x_241; 
lean_inc(x_239);
lean_inc_ref(x_238);
lean_inc(x_237);
lean_inc_ref(x_236);
lean_inc_ref(x_230);
x_241 = lean_infer_type(x_230, x_236, x_237, x_238, x_239);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
lean_dec_ref(x_241);
lean_inc(x_242);
x_243 = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__0___boxed), 8, 2);
lean_closure_set(x_243, 0, x_228);
lean_closure_set(x_243, 1, x_242);
x_244 = l_Lean_MVarId_rewrite___lam__1___closed__32;
x_245 = 0;
lean_inc_ref(x_232);
x_246 = l_Lean_mkLambda(x_244, x_245, x_232, x_229);
lean_inc(x_239);
lean_inc_ref(x_238);
lean_inc(x_237);
lean_inc_ref(x_236);
lean_inc_ref(x_246);
x_247 = l_Lean_Meta_check(x_246, x_236, x_237, x_238, x_239);
if (lean_obj_tag(x_247) == 0)
{
x_139 = x_238;
x_140 = x_246;
x_141 = x_236;
x_142 = x_244;
x_143 = x_233;
x_144 = x_237;
x_145 = x_235;
x_146 = x_242;
x_147 = x_239;
x_148 = x_230;
x_149 = x_231;
x_150 = x_232;
x_151 = x_243;
x_152 = x_234;
x_153 = x_247;
goto block_181;
}
else
{
lean_object* x_248; uint8_t x_249; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = l_Lean_Exception_isInterrupt(x_248);
if (x_249 == 0)
{
uint8_t x_250; 
x_250 = l_Lean_Exception_isRuntime(x_248);
x_182 = x_238;
x_183 = x_246;
x_184 = x_236;
x_185 = x_244;
x_186 = x_247;
x_187 = x_248;
x_188 = x_233;
x_189 = lean_box(0);
x_190 = x_237;
x_191 = x_235;
x_192 = x_242;
x_193 = x_239;
x_194 = x_230;
x_195 = x_231;
x_196 = x_232;
x_197 = x_243;
x_198 = x_234;
x_199 = x_250;
goto block_227;
}
else
{
x_182 = x_238;
x_183 = x_246;
x_184 = x_236;
x_185 = x_244;
x_186 = x_247;
x_187 = x_248;
x_188 = x_233;
x_189 = lean_box(0);
x_190 = x_237;
x_191 = x_235;
x_192 = x_242;
x_193 = x_239;
x_194 = x_230;
x_195 = x_231;
x_196 = x_232;
x_197 = x_243;
x_198 = x_234;
x_199 = x_249;
goto block_227;
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_233);
lean_dec_ref(x_232);
lean_dec_ref(x_231);
lean_dec_ref(x_230);
lean_dec_ref(x_229);
lean_dec_ref(x_228);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_251 = !lean_is_exclusive(x_241);
if (x_251 == 0)
{
return x_241;
}
else
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_241, 0);
lean_inc(x_252);
lean_dec(x_241);
x_253 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_253, 0, x_252);
return x_253;
}
}
}
block_275:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_266 = lean_expr_instantiate1(x_255, x_259);
x_267 = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__4___redArg(x_266, x_262);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
lean_dec_ref(x_267);
x_269 = l_Lean_Expr_hasBinderNameHint(x_259);
if (x_269 == 0)
{
lean_inc_ref(x_255);
x_228 = x_255;
x_229 = x_255;
x_230 = x_256;
x_231 = x_257;
x_232 = x_258;
x_233 = x_259;
x_234 = x_260;
x_235 = x_268;
x_236 = x_261;
x_237 = x_262;
x_238 = x_263;
x_239 = x_264;
x_240 = lean_box(0);
goto block_254;
}
else
{
lean_object* x_270; 
lean_inc(x_264);
lean_inc_ref(x_263);
x_270 = l_Lean_Expr_resolveBinderNameHint(x_268, x_263, x_264);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
lean_dec_ref(x_270);
lean_inc_ref(x_255);
x_228 = x_255;
x_229 = x_255;
x_230 = x_256;
x_231 = x_257;
x_232 = x_258;
x_233 = x_259;
x_234 = x_260;
x_235 = x_271;
x_236 = x_261;
x_237 = x_262;
x_238 = x_263;
x_239 = x_264;
x_240 = lean_box(0);
goto block_254;
}
else
{
uint8_t x_272; 
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec_ref(x_255);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_272 = !lean_is_exclusive(x_270);
if (x_272 == 0)
{
return x_270;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_270, 0);
lean_inc(x_273);
lean_dec(x_270);
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_273);
return x_274;
}
}
}
}
block_473:
{
lean_object* x_286; uint8_t x_287; 
x_286 = l_Lean_Expr_getAppFn(x_279);
x_287 = l_Lean_Expr_isMVar(x_286);
lean_dec_ref(x_286);
if (x_287 == 0)
{
lean_object* x_288; uint8_t x_289; 
lean_dec_ref(x_278);
x_288 = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__4___redArg(x_4, x_282);
x_289 = !lean_is_exclusive(x_288);
if (x_289 == 0)
{
lean_object* x_290; uint8_t x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_290 = lean_ctor_get(x_288, 0);
x_291 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_292 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_293 = lean_ctor_get(x_5, 0);
lean_inc(x_293);
lean_dec_ref(x_5);
x_294 = l_Lean_Meta_Context_config(x_281);
x_295 = !lean_is_exclusive(x_294);
if (x_295 == 0)
{
uint8_t x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; uint8_t x_304; uint64_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_296 = lean_ctor_get_uint8(x_281, sizeof(void*)*7);
x_297 = lean_ctor_get(x_281, 1);
x_298 = lean_ctor_get(x_281, 2);
x_299 = lean_ctor_get(x_281, 3);
x_300 = lean_ctor_get(x_281, 4);
x_301 = lean_ctor_get(x_281, 5);
x_302 = lean_ctor_get(x_281, 6);
x_303 = lean_ctor_get_uint8(x_281, sizeof(void*)*7 + 1);
x_304 = lean_ctor_get_uint8(x_281, sizeof(void*)*7 + 2);
lean_ctor_set_uint8(x_294, 8, x_292);
lean_ctor_set_uint8(x_294, 9, x_291);
x_305 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_294);
x_306 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_306, 0, x_294);
lean_ctor_set_uint64(x_306, sizeof(void*)*1, x_305);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc_ref(x_299);
lean_inc_ref(x_298);
lean_inc(x_297);
x_307 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_297);
lean_ctor_set(x_307, 2, x_298);
lean_ctor_set(x_307, 3, x_299);
lean_ctor_set(x_307, 4, x_300);
lean_ctor_set(x_307, 5, x_301);
lean_ctor_set(x_307, 6, x_302);
lean_ctor_set_uint8(x_307, sizeof(void*)*7, x_296);
lean_ctor_set_uint8(x_307, sizeof(void*)*7 + 1, x_303);
lean_ctor_set_uint8(x_307, sizeof(void*)*7 + 2, x_304);
lean_inc(x_284);
lean_inc_ref(x_283);
lean_inc(x_282);
lean_inc_ref(x_279);
lean_inc(x_290);
x_308 = l_Lean_Meta_kabstract(x_290, x_279, x_293, x_307, x_282, x_283, x_284);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; uint8_t x_310; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
lean_dec_ref(x_308);
x_310 = l_Lean_Expr_hasLooseBVars(x_309);
if (x_310 == 0)
{
lean_object* x_311; 
lean_inc(x_284);
lean_inc_ref(x_283);
lean_inc(x_282);
lean_inc_ref(x_281);
lean_inc_ref(x_279);
lean_inc(x_290);
x_311 = l_Lean_Meta_addPPExplicitToExposeDiff(x_290, x_279, x_281, x_282, x_283, x_284);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; uint8_t x_313; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
lean_dec_ref(x_311);
x_313 = !lean_is_exclusive(x_312);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_314 = lean_ctor_get(x_312, 0);
x_315 = lean_ctor_get(x_312, 1);
x_316 = l_Lean_MVarId_rewrite___lam__1___closed__34;
x_317 = l_Lean_indentExpr(x_315);
lean_ctor_set_tag(x_312, 7);
lean_ctor_set(x_312, 1, x_317);
lean_ctor_set(x_312, 0, x_316);
x_318 = l_Lean_MVarId_rewrite___lam__1___closed__36;
x_319 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_319, 0, x_312);
lean_ctor_set(x_319, 1, x_318);
x_320 = l_Lean_indentExpr(x_314);
x_321 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
lean_ctor_set_tag(x_288, 1);
lean_ctor_set(x_288, 0, x_321);
lean_inc(x_1);
lean_inc(x_2);
x_322 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_288, x_281, x_282, x_283, x_284);
if (lean_obj_tag(x_322) == 0)
{
lean_dec_ref(x_322);
x_255 = x_309;
x_256 = x_290;
x_257 = x_277;
x_258 = x_276;
x_259 = x_280;
x_260 = x_279;
x_261 = x_281;
x_262 = x_282;
x_263 = x_283;
x_264 = x_284;
x_265 = lean_box(0);
goto block_275;
}
else
{
uint8_t x_323; 
lean_dec(x_309);
lean_dec(x_290);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_277);
lean_dec_ref(x_276);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_323 = !lean_is_exclusive(x_322);
if (x_323 == 0)
{
return x_322;
}
else
{
lean_object* x_324; lean_object* x_325; 
x_324 = lean_ctor_get(x_322, 0);
lean_inc(x_324);
lean_dec(x_322);
x_325 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_325, 0, x_324);
return x_325;
}
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_326 = lean_ctor_get(x_312, 0);
x_327 = lean_ctor_get(x_312, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_312);
x_328 = l_Lean_MVarId_rewrite___lam__1___closed__34;
x_329 = l_Lean_indentExpr(x_327);
x_330 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
x_331 = l_Lean_MVarId_rewrite___lam__1___closed__36;
x_332 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
x_333 = l_Lean_indentExpr(x_326);
x_334 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
lean_ctor_set_tag(x_288, 1);
lean_ctor_set(x_288, 0, x_334);
lean_inc(x_1);
lean_inc(x_2);
x_335 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_288, x_281, x_282, x_283, x_284);
if (lean_obj_tag(x_335) == 0)
{
lean_dec_ref(x_335);
x_255 = x_309;
x_256 = x_290;
x_257 = x_277;
x_258 = x_276;
x_259 = x_280;
x_260 = x_279;
x_261 = x_281;
x_262 = x_282;
x_263 = x_283;
x_264 = x_284;
x_265 = lean_box(0);
goto block_275;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_309);
lean_dec(x_290);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_277);
lean_dec_ref(x_276);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 x_337 = x_335;
} else {
 lean_dec_ref(x_335);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 1, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_336);
return x_338;
}
}
}
else
{
uint8_t x_339; 
lean_dec(x_309);
lean_free_object(x_288);
lean_dec(x_290);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_277);
lean_dec_ref(x_276);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_339 = !lean_is_exclusive(x_311);
if (x_339 == 0)
{
return x_311;
}
else
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_ctor_get(x_311, 0);
lean_inc(x_340);
lean_dec(x_311);
x_341 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_341, 0, x_340);
return x_341;
}
}
}
else
{
lean_free_object(x_288);
x_255 = x_309;
x_256 = x_290;
x_257 = x_277;
x_258 = x_276;
x_259 = x_280;
x_260 = x_279;
x_261 = x_281;
x_262 = x_282;
x_263 = x_283;
x_264 = x_284;
x_265 = lean_box(0);
goto block_275;
}
}
else
{
uint8_t x_342; 
lean_free_object(x_288);
lean_dec(x_290);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_277);
lean_dec_ref(x_276);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_342 = !lean_is_exclusive(x_308);
if (x_342 == 0)
{
return x_308;
}
else
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_308, 0);
lean_inc(x_343);
lean_dec(x_308);
x_344 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_344, 0, x_343);
return x_344;
}
}
}
else
{
uint8_t x_345; uint8_t x_346; uint8_t x_347; uint8_t x_348; uint8_t x_349; uint8_t x_350; uint8_t x_351; uint8_t x_352; uint8_t x_353; uint8_t x_354; uint8_t x_355; uint8_t x_356; uint8_t x_357; uint8_t x_358; uint8_t x_359; uint8_t x_360; uint8_t x_361; uint8_t x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; uint8_t x_370; lean_object* x_371; uint64_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_345 = lean_ctor_get_uint8(x_294, 0);
x_346 = lean_ctor_get_uint8(x_294, 1);
x_347 = lean_ctor_get_uint8(x_294, 2);
x_348 = lean_ctor_get_uint8(x_294, 3);
x_349 = lean_ctor_get_uint8(x_294, 4);
x_350 = lean_ctor_get_uint8(x_294, 5);
x_351 = lean_ctor_get_uint8(x_294, 6);
x_352 = lean_ctor_get_uint8(x_294, 7);
x_353 = lean_ctor_get_uint8(x_294, 10);
x_354 = lean_ctor_get_uint8(x_294, 11);
x_355 = lean_ctor_get_uint8(x_294, 12);
x_356 = lean_ctor_get_uint8(x_294, 13);
x_357 = lean_ctor_get_uint8(x_294, 14);
x_358 = lean_ctor_get_uint8(x_294, 15);
x_359 = lean_ctor_get_uint8(x_294, 16);
x_360 = lean_ctor_get_uint8(x_294, 17);
x_361 = lean_ctor_get_uint8(x_294, 18);
lean_dec(x_294);
x_362 = lean_ctor_get_uint8(x_281, sizeof(void*)*7);
x_363 = lean_ctor_get(x_281, 1);
x_364 = lean_ctor_get(x_281, 2);
x_365 = lean_ctor_get(x_281, 3);
x_366 = lean_ctor_get(x_281, 4);
x_367 = lean_ctor_get(x_281, 5);
x_368 = lean_ctor_get(x_281, 6);
x_369 = lean_ctor_get_uint8(x_281, sizeof(void*)*7 + 1);
x_370 = lean_ctor_get_uint8(x_281, sizeof(void*)*7 + 2);
x_371 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_371, 0, x_345);
lean_ctor_set_uint8(x_371, 1, x_346);
lean_ctor_set_uint8(x_371, 2, x_347);
lean_ctor_set_uint8(x_371, 3, x_348);
lean_ctor_set_uint8(x_371, 4, x_349);
lean_ctor_set_uint8(x_371, 5, x_350);
lean_ctor_set_uint8(x_371, 6, x_351);
lean_ctor_set_uint8(x_371, 7, x_352);
lean_ctor_set_uint8(x_371, 8, x_292);
lean_ctor_set_uint8(x_371, 9, x_291);
lean_ctor_set_uint8(x_371, 10, x_353);
lean_ctor_set_uint8(x_371, 11, x_354);
lean_ctor_set_uint8(x_371, 12, x_355);
lean_ctor_set_uint8(x_371, 13, x_356);
lean_ctor_set_uint8(x_371, 14, x_357);
lean_ctor_set_uint8(x_371, 15, x_358);
lean_ctor_set_uint8(x_371, 16, x_359);
lean_ctor_set_uint8(x_371, 17, x_360);
lean_ctor_set_uint8(x_371, 18, x_361);
x_372 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_371);
x_373 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set_uint64(x_373, sizeof(void*)*1, x_372);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc_ref(x_365);
lean_inc_ref(x_364);
lean_inc(x_363);
x_374 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_363);
lean_ctor_set(x_374, 2, x_364);
lean_ctor_set(x_374, 3, x_365);
lean_ctor_set(x_374, 4, x_366);
lean_ctor_set(x_374, 5, x_367);
lean_ctor_set(x_374, 6, x_368);
lean_ctor_set_uint8(x_374, sizeof(void*)*7, x_362);
lean_ctor_set_uint8(x_374, sizeof(void*)*7 + 1, x_369);
lean_ctor_set_uint8(x_374, sizeof(void*)*7 + 2, x_370);
lean_inc(x_284);
lean_inc_ref(x_283);
lean_inc(x_282);
lean_inc_ref(x_279);
lean_inc(x_290);
x_375 = l_Lean_Meta_kabstract(x_290, x_279, x_293, x_374, x_282, x_283, x_284);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; uint8_t x_377; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
lean_dec_ref(x_375);
x_377 = l_Lean_Expr_hasLooseBVars(x_376);
if (x_377 == 0)
{
lean_object* x_378; 
lean_inc(x_284);
lean_inc_ref(x_283);
lean_inc(x_282);
lean_inc_ref(x_281);
lean_inc_ref(x_279);
lean_inc(x_290);
x_378 = l_Lean_Meta_addPPExplicitToExposeDiff(x_290, x_279, x_281, x_282, x_283, x_284);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
lean_dec_ref(x_378);
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 x_382 = x_379;
} else {
 lean_dec_ref(x_379);
 x_382 = lean_box(0);
}
x_383 = l_Lean_MVarId_rewrite___lam__1___closed__34;
x_384 = l_Lean_indentExpr(x_381);
if (lean_is_scalar(x_382)) {
 x_385 = lean_alloc_ctor(7, 2, 0);
} else {
 x_385 = x_382;
 lean_ctor_set_tag(x_385, 7);
}
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
x_386 = l_Lean_MVarId_rewrite___lam__1___closed__36;
x_387 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
x_388 = l_Lean_indentExpr(x_380);
x_389 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
lean_ctor_set_tag(x_288, 1);
lean_ctor_set(x_288, 0, x_389);
lean_inc(x_1);
lean_inc(x_2);
x_390 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_288, x_281, x_282, x_283, x_284);
if (lean_obj_tag(x_390) == 0)
{
lean_dec_ref(x_390);
x_255 = x_376;
x_256 = x_290;
x_257 = x_277;
x_258 = x_276;
x_259 = x_280;
x_260 = x_279;
x_261 = x_281;
x_262 = x_282;
x_263 = x_283;
x_264 = x_284;
x_265 = lean_box(0);
goto block_275;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_376);
lean_dec(x_290);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_277);
lean_dec_ref(x_276);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 x_392 = x_390;
} else {
 lean_dec_ref(x_390);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 1, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_391);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_376);
lean_free_object(x_288);
lean_dec(x_290);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_277);
lean_dec_ref(x_276);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_394 = lean_ctor_get(x_378, 0);
lean_inc(x_394);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 x_395 = x_378;
} else {
 lean_dec_ref(x_378);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 1, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_394);
return x_396;
}
}
else
{
lean_free_object(x_288);
x_255 = x_376;
x_256 = x_290;
x_257 = x_277;
x_258 = x_276;
x_259 = x_280;
x_260 = x_279;
x_261 = x_281;
x_262 = x_282;
x_263 = x_283;
x_264 = x_284;
x_265 = lean_box(0);
goto block_275;
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_free_object(x_288);
lean_dec(x_290);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_277);
lean_dec_ref(x_276);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_397 = lean_ctor_get(x_375, 0);
lean_inc(x_397);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 x_398 = x_375;
} else {
 lean_dec_ref(x_375);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 1, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_397);
return x_399;
}
}
}
else
{
lean_object* x_400; uint8_t x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; uint8_t x_406; uint8_t x_407; uint8_t x_408; uint8_t x_409; uint8_t x_410; uint8_t x_411; uint8_t x_412; uint8_t x_413; uint8_t x_414; uint8_t x_415; uint8_t x_416; uint8_t x_417; uint8_t x_418; uint8_t x_419; uint8_t x_420; uint8_t x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; uint8_t x_430; uint8_t x_431; lean_object* x_432; uint64_t x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_400 = lean_ctor_get(x_288, 0);
lean_inc(x_400);
lean_dec(x_288);
x_401 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_402 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_403 = lean_ctor_get(x_5, 0);
lean_inc(x_403);
lean_dec_ref(x_5);
x_404 = l_Lean_Meta_Context_config(x_281);
x_405 = lean_ctor_get_uint8(x_404, 0);
x_406 = lean_ctor_get_uint8(x_404, 1);
x_407 = lean_ctor_get_uint8(x_404, 2);
x_408 = lean_ctor_get_uint8(x_404, 3);
x_409 = lean_ctor_get_uint8(x_404, 4);
x_410 = lean_ctor_get_uint8(x_404, 5);
x_411 = lean_ctor_get_uint8(x_404, 6);
x_412 = lean_ctor_get_uint8(x_404, 7);
x_413 = lean_ctor_get_uint8(x_404, 10);
x_414 = lean_ctor_get_uint8(x_404, 11);
x_415 = lean_ctor_get_uint8(x_404, 12);
x_416 = lean_ctor_get_uint8(x_404, 13);
x_417 = lean_ctor_get_uint8(x_404, 14);
x_418 = lean_ctor_get_uint8(x_404, 15);
x_419 = lean_ctor_get_uint8(x_404, 16);
x_420 = lean_ctor_get_uint8(x_404, 17);
x_421 = lean_ctor_get_uint8(x_404, 18);
if (lean_is_exclusive(x_404)) {
 x_422 = x_404;
} else {
 lean_dec_ref(x_404);
 x_422 = lean_box(0);
}
x_423 = lean_ctor_get_uint8(x_281, sizeof(void*)*7);
x_424 = lean_ctor_get(x_281, 1);
x_425 = lean_ctor_get(x_281, 2);
x_426 = lean_ctor_get(x_281, 3);
x_427 = lean_ctor_get(x_281, 4);
x_428 = lean_ctor_get(x_281, 5);
x_429 = lean_ctor_get(x_281, 6);
x_430 = lean_ctor_get_uint8(x_281, sizeof(void*)*7 + 1);
x_431 = lean_ctor_get_uint8(x_281, sizeof(void*)*7 + 2);
if (lean_is_scalar(x_422)) {
 x_432 = lean_alloc_ctor(0, 0, 19);
} else {
 x_432 = x_422;
}
lean_ctor_set_uint8(x_432, 0, x_405);
lean_ctor_set_uint8(x_432, 1, x_406);
lean_ctor_set_uint8(x_432, 2, x_407);
lean_ctor_set_uint8(x_432, 3, x_408);
lean_ctor_set_uint8(x_432, 4, x_409);
lean_ctor_set_uint8(x_432, 5, x_410);
lean_ctor_set_uint8(x_432, 6, x_411);
lean_ctor_set_uint8(x_432, 7, x_412);
lean_ctor_set_uint8(x_432, 8, x_402);
lean_ctor_set_uint8(x_432, 9, x_401);
lean_ctor_set_uint8(x_432, 10, x_413);
lean_ctor_set_uint8(x_432, 11, x_414);
lean_ctor_set_uint8(x_432, 12, x_415);
lean_ctor_set_uint8(x_432, 13, x_416);
lean_ctor_set_uint8(x_432, 14, x_417);
lean_ctor_set_uint8(x_432, 15, x_418);
lean_ctor_set_uint8(x_432, 16, x_419);
lean_ctor_set_uint8(x_432, 17, x_420);
lean_ctor_set_uint8(x_432, 18, x_421);
x_433 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_432);
x_434 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set_uint64(x_434, sizeof(void*)*1, x_433);
lean_inc(x_429);
lean_inc(x_428);
lean_inc(x_427);
lean_inc_ref(x_426);
lean_inc_ref(x_425);
lean_inc(x_424);
x_435 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_424);
lean_ctor_set(x_435, 2, x_425);
lean_ctor_set(x_435, 3, x_426);
lean_ctor_set(x_435, 4, x_427);
lean_ctor_set(x_435, 5, x_428);
lean_ctor_set(x_435, 6, x_429);
lean_ctor_set_uint8(x_435, sizeof(void*)*7, x_423);
lean_ctor_set_uint8(x_435, sizeof(void*)*7 + 1, x_430);
lean_ctor_set_uint8(x_435, sizeof(void*)*7 + 2, x_431);
lean_inc(x_284);
lean_inc_ref(x_283);
lean_inc(x_282);
lean_inc_ref(x_279);
lean_inc(x_400);
x_436 = l_Lean_Meta_kabstract(x_400, x_279, x_403, x_435, x_282, x_283, x_284);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; uint8_t x_438; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
lean_dec_ref(x_436);
x_438 = l_Lean_Expr_hasLooseBVars(x_437);
if (x_438 == 0)
{
lean_object* x_439; 
lean_inc(x_284);
lean_inc_ref(x_283);
lean_inc(x_282);
lean_inc_ref(x_281);
lean_inc_ref(x_279);
lean_inc(x_400);
x_439 = l_Lean_Meta_addPPExplicitToExposeDiff(x_400, x_279, x_281, x_282, x_283, x_284);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
lean_dec_ref(x_439);
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_443 = x_440;
} else {
 lean_dec_ref(x_440);
 x_443 = lean_box(0);
}
x_444 = l_Lean_MVarId_rewrite___lam__1___closed__34;
x_445 = l_Lean_indentExpr(x_442);
if (lean_is_scalar(x_443)) {
 x_446 = lean_alloc_ctor(7, 2, 0);
} else {
 x_446 = x_443;
 lean_ctor_set_tag(x_446, 7);
}
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
x_447 = l_Lean_MVarId_rewrite___lam__1___closed__36;
x_448 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_448, 0, x_446);
lean_ctor_set(x_448, 1, x_447);
x_449 = l_Lean_indentExpr(x_441);
x_450 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
x_451 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_451, 0, x_450);
lean_inc(x_1);
lean_inc(x_2);
x_452 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_451, x_281, x_282, x_283, x_284);
if (lean_obj_tag(x_452) == 0)
{
lean_dec_ref(x_452);
x_255 = x_437;
x_256 = x_400;
x_257 = x_277;
x_258 = x_276;
x_259 = x_280;
x_260 = x_279;
x_261 = x_281;
x_262 = x_282;
x_263 = x_283;
x_264 = x_284;
x_265 = lean_box(0);
goto block_275;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_dec(x_437);
lean_dec(x_400);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_277);
lean_dec_ref(x_276);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 x_454 = x_452;
} else {
 lean_dec_ref(x_452);
 x_454 = lean_box(0);
}
if (lean_is_scalar(x_454)) {
 x_455 = lean_alloc_ctor(1, 1, 0);
} else {
 x_455 = x_454;
}
lean_ctor_set(x_455, 0, x_453);
return x_455;
}
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_437);
lean_dec(x_400);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_277);
lean_dec_ref(x_276);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_456 = lean_ctor_get(x_439, 0);
lean_inc(x_456);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 x_457 = x_439;
} else {
 lean_dec_ref(x_439);
 x_457 = lean_box(0);
}
if (lean_is_scalar(x_457)) {
 x_458 = lean_alloc_ctor(1, 1, 0);
} else {
 x_458 = x_457;
}
lean_ctor_set(x_458, 0, x_456);
return x_458;
}
}
else
{
x_255 = x_437;
x_256 = x_400;
x_257 = x_277;
x_258 = x_276;
x_259 = x_280;
x_260 = x_279;
x_261 = x_281;
x_262 = x_282;
x_263 = x_283;
x_264 = x_284;
x_265 = lean_box(0);
goto block_275;
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_400);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_277);
lean_dec_ref(x_276);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_459 = lean_ctor_get(x_436, 0);
lean_inc(x_459);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 x_460 = x_436;
} else {
 lean_dec_ref(x_436);
 x_460 = lean_box(0);
}
if (lean_is_scalar(x_460)) {
 x_461 = lean_alloc_ctor(1, 1, 0);
} else {
 x_461 = x_460;
}
lean_ctor_set(x_461, 0, x_459);
return x_461;
}
}
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; 
lean_dec_ref(x_280);
lean_dec_ref(x_277);
lean_dec_ref(x_276);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_462 = l_Lean_MVarId_rewrite___lam__1___closed__38;
x_463 = l_Lean_MessageData_ofExpr(x_279);
x_464 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_464, 0, x_462);
lean_ctor_set(x_464, 1, x_463);
x_465 = l_Lean_MVarId_rewrite___lam__1___closed__40;
x_466 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
x_467 = l_Lean_indentExpr(x_278);
x_468 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set(x_468, 1, x_467);
x_469 = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__5___redArg(x_468, x_281, x_282, x_283, x_284);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec_ref(x_281);
x_470 = !lean_is_exclusive(x_469);
if (x_470 == 0)
{
return x_469;
}
else
{
lean_object* x_471; lean_object* x_472; 
x_471 = lean_ctor_get(x_469, 0);
lean_inc(x_471);
lean_dec(x_469);
x_472 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_472, 0, x_471);
return x_472;
}
}
}
block_512:
{
lean_object* x_481; 
lean_inc(x_479);
lean_inc_ref(x_478);
lean_inc(x_477);
lean_inc_ref(x_476);
lean_inc_ref(x_475);
x_481 = l_Lean_Meta_matchEq_x3f(x_475, x_476, x_477, x_478, x_479);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; 
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
lean_dec_ref(x_481);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; 
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_479);
lean_inc_ref(x_478);
lean_inc(x_477);
lean_inc_ref(x_476);
lean_inc_ref(x_475);
x_483 = l_Lean_Meta_isProp(x_475, x_476, x_477, x_478, x_479);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; uint8_t x_485; 
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
lean_dec_ref(x_483);
x_485 = lean_unbox(x_484);
lean_dec(x_484);
if (x_485 == 0)
{
lean_object* x_486; 
x_486 = l_Lean_MVarId_rewrite___lam__1___closed__41;
x_12 = x_475;
x_13 = x_477;
x_14 = x_479;
x_15 = x_478;
x_16 = lean_box(0);
x_17 = x_474;
x_18 = x_476;
x_19 = x_486;
goto block_31;
}
else
{
lean_object* x_487; 
x_487 = l_Lean_MVarId_rewrite___lam__1___closed__42;
x_12 = x_475;
x_13 = x_477;
x_14 = x_479;
x_15 = x_478;
x_16 = lean_box(0);
x_17 = x_474;
x_18 = x_476;
x_19 = x_487;
goto block_31;
}
}
else
{
uint8_t x_488; 
lean_dec(x_479);
lean_dec_ref(x_478);
lean_dec(x_477);
lean_dec_ref(x_476);
lean_dec_ref(x_475);
lean_dec_ref(x_474);
x_488 = !lean_is_exclusive(x_483);
if (x_488 == 0)
{
return x_483;
}
else
{
lean_object* x_489; lean_object* x_490; 
x_489 = lean_ctor_get(x_483, 0);
lean_inc(x_489);
lean_dec(x_483);
x_490 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_490, 0, x_489);
return x_490;
}
}
}
else
{
lean_object* x_491; lean_object* x_492; 
x_491 = lean_ctor_get(x_482, 0);
lean_inc(x_491);
lean_dec_ref(x_482);
x_492 = lean_ctor_get(x_491, 1);
lean_inc(x_492);
if (x_6 == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_493 = lean_ctor_get(x_491, 0);
lean_inc(x_493);
lean_dec(x_491);
x_494 = lean_ctor_get(x_492, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_492, 1);
lean_inc(x_495);
lean_dec(x_492);
x_276 = x_493;
x_277 = x_474;
x_278 = x_475;
x_279 = x_494;
x_280 = x_495;
x_281 = x_476;
x_282 = x_477;
x_283 = x_478;
x_284 = x_479;
x_285 = lean_box(0);
goto block_473;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
lean_dec_ref(x_475);
x_496 = lean_ctor_get(x_491, 0);
lean_inc(x_496);
lean_dec(x_491);
x_497 = lean_ctor_get(x_492, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_492, 1);
lean_inc(x_498);
lean_dec(x_492);
lean_inc(x_479);
lean_inc_ref(x_478);
lean_inc(x_477);
lean_inc_ref(x_476);
x_499 = l_Lean_Meta_mkEqSymm(x_474, x_476, x_477, x_478, x_479);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; 
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
lean_dec_ref(x_499);
lean_inc(x_479);
lean_inc_ref(x_478);
lean_inc(x_477);
lean_inc_ref(x_476);
lean_inc(x_497);
lean_inc(x_498);
x_501 = l_Lean_Meta_mkEq(x_498, x_497, x_476, x_477, x_478, x_479);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
lean_dec_ref(x_501);
x_276 = x_496;
x_277 = x_500;
x_278 = x_502;
x_279 = x_498;
x_280 = x_497;
x_281 = x_476;
x_282 = x_477;
x_283 = x_478;
x_284 = x_479;
x_285 = lean_box(0);
goto block_473;
}
else
{
uint8_t x_503; 
lean_dec(x_500);
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_479);
lean_dec_ref(x_478);
lean_dec(x_477);
lean_dec_ref(x_476);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_503 = !lean_is_exclusive(x_501);
if (x_503 == 0)
{
return x_501;
}
else
{
lean_object* x_504; lean_object* x_505; 
x_504 = lean_ctor_get(x_501, 0);
lean_inc(x_504);
lean_dec(x_501);
x_505 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_505, 0, x_504);
return x_505;
}
}
}
else
{
uint8_t x_506; 
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_479);
lean_dec_ref(x_478);
lean_dec(x_477);
lean_dec_ref(x_476);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_506 = !lean_is_exclusive(x_499);
if (x_506 == 0)
{
return x_499;
}
else
{
lean_object* x_507; lean_object* x_508; 
x_507 = lean_ctor_get(x_499, 0);
lean_inc(x_507);
lean_dec(x_499);
x_508 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_508, 0, x_507);
return x_508;
}
}
}
}
}
else
{
uint8_t x_509; 
lean_dec(x_479);
lean_dec_ref(x_478);
lean_dec(x_477);
lean_dec_ref(x_476);
lean_dec_ref(x_475);
lean_dec_ref(x_474);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_509 = !lean_is_exclusive(x_481);
if (x_509 == 0)
{
return x_481;
}
else
{
lean_object* x_510; lean_object* x_511; 
x_510 = lean_ctor_get(x_481, 0);
lean_inc(x_510);
lean_dec(x_481);
x_511 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_511, 0, x_510);
return x_511;
}
}
}
}
else
{
uint8_t x_527; 
lean_dec(x_69);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_527 = !lean_is_exclusive(x_72);
if (x_527 == 0)
{
return x_72;
}
else
{
lean_object* x_528; lean_object* x_529; 
x_528 = lean_ctor_get(x_72, 0);
lean_inc(x_528);
lean_dec(x_72);
x_529 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_529, 0, x_528);
return x_529;
}
}
}
else
{
uint8_t x_530; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_530 = !lean_is_exclusive(x_65);
if (x_530 == 0)
{
return x_65;
}
else
{
lean_object* x_531; lean_object* x_532; 
x_531 = lean_ctor_get(x_65, 0);
lean_inc(x_531);
lean_dec(x_65);
x_532 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_532, 0, x_531);
return x_532;
}
}
}
else
{
uint8_t x_533; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_533 = !lean_is_exclusive(x_64);
if (x_533 == 0)
{
return x_64;
}
else
{
lean_object* x_534; lean_object* x_535; 
x_534 = lean_ctor_get(x_64, 0);
lean_inc(x_534);
lean_dec(x_64);
x_535 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_535, 0, x_534);
return x_535;
}
}
block_31:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = l_Lean_MVarId_rewrite___lam__1___closed__1;
x_21 = lean_unsigned_to_nat(30u);
x_22 = l_Lean_inlineExpr(x_17, x_21);
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
x_28 = l_Lean_indentExpr(x_12);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__5___redArg(x_29, x_18, x_13, x_15, x_14);
lean_dec(x_14);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec_ref(x_18);
return x_30;
}
block_41:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = l_Array_append___redArg(x_35, x_36);
lean_dec_ref(x_36);
x_38 = lean_array_to_list(x_37);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
block_63:
{
lean_object* x_52; 
x_52 = l_Lean_Meta_getMVarsNoDelayed(x_3, x_44, x_48, x_49, x_45);
lean_dec(x_45);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec_ref(x_44);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_array_get_size(x_53);
x_55 = lean_mk_empty_array_with_capacity(x_46);
x_56 = lean_nat_dec_lt(x_46, x_54);
if (x_56 == 0)
{
lean_dec(x_54);
lean_dec(x_53);
x_32 = x_42;
x_33 = x_47;
x_34 = lean_box(0);
x_35 = x_50;
x_36 = x_55;
goto block_41;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_54, x_54);
if (x_57 == 0)
{
lean_dec(x_54);
lean_dec(x_53);
x_32 = x_42;
x_33 = x_47;
x_34 = lean_box(0);
x_35 = x_50;
x_36 = x_55;
goto block_41;
}
else
{
size_t x_58; lean_object* x_59; 
x_58 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_59 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__10(x_50, x_53, x_43, x_58, x_55);
lean_dec(x_53);
x_32 = x_42;
x_33 = x_47;
x_34 = lean_box(0);
x_35 = x_50;
x_36 = x_59;
goto block_41;
}
}
}
else
{
uint8_t x_60; 
lean_dec_ref(x_50);
lean_dec_ref(x_47);
lean_dec_ref(x_42);
x_60 = !lean_is_exclusive(x_52);
if (x_60 == 0)
{
return x_52;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_52, 0);
lean_inc(x_61);
lean_dec(x_52);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
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
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_14 = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__15___redArg(x_1, x_13, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__4___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__5___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__7(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__8_spec__8(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_MVarId_rewrite_spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___00Lean_MVarId_rewrite_spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__10(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__11(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__12___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__12(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13___redArg(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13_spec__13(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__15___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__15___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_rewrite___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_13 = l_Lean_MVarId_rewrite___lam__1(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_MVarId_rewrite(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_BinderNameHint(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KAbstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__1();
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
l_Lean_MVarId_rewrite___closed__0 = _init_l_Lean_MVarId_rewrite___closed__0();
lean_mark_persistent(l_Lean_MVarId_rewrite___closed__0);
l_Lean_MVarId_rewrite___closed__1 = _init_l_Lean_MVarId_rewrite___closed__1();
lean_mark_persistent(l_Lean_MVarId_rewrite___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
