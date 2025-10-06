// Lean compiler output
// Module: Lean.Meta.Tactic.Rewrite
// Imports: public import Lean.Meta.AppBuilder public import Lean.Meta.MatchUtil public import Lean.Meta.KAbstract public import Lean.Meta.Check public import Lean.Meta.Tactic.Util public import Lean.Meta.Tactic.Apply public import Lean.Meta.BinderNameHint
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
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_RewriteResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___Lean_MVarId_rewrite_spec__8(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__24;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_rewrite_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__25;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_RewriteResult_ctorIdx(lean_object*);
static size_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_MVarId_rewrite_spec__0_spec__0_spec__0___redArg___closed__1;
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
x_3 = l_Lean_instHashableMVarId_hash(x_2);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_ctor_get(x_4, 2);
lean_inc(x_18);
lean_inc_ref(x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set_tag(x_12, 3);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 0, x_19);
lean_ctor_set(x_7, 1, x_15);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_4, 2);
lean_inc(x_24);
lean_inc_ref(x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_24);
x_26 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_1);
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_26);
return x_7;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_3, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_2, 2);
x_36 = lean_ctor_get(x_4, 2);
lean_inc(x_36);
lean_inc_ref(x_35);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_36);
if (lean_is_scalar(x_33)) {
 x_38 = lean_alloc_ctor(3, 2, 0);
} else {
 x_38 = x_33;
 lean_ctor_set_tag(x_38, 3);
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
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
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_66; 
lean_inc(x_2);
lean_inc(x_1);
x_66 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec_ref(x_66);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_3);
x_68 = lean_infer_type(x_3, x_7, x_8, x_9, x_10, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4___redArg(x_69, x_8, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_box(0);
x_76 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_77 = l_Lean_Meta_forallMetaTelescopeReducing(x_72, x_75, x_76, x_7, x_8, x_9, x_10, x_73);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec_ref(x_77);
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_82 = x_78;
} else {
 lean_dec_ref(x_78);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_79, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_79, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_85 = x_79;
} else {
 lean_dec_ref(x_79);
 x_85 = lean_box(0);
}
lean_inc_ref(x_3);
x_573 = l_Lean_mkAppN(x_3, x_81);
x_574 = l_Lean_MVarId_rewrite___lam__1___closed__44;
x_575 = lean_unsigned_to_nat(2u);
x_576 = l_Lean_Expr_isAppOfArity(x_84, x_574, x_575);
if (x_576 == 0)
{
x_523 = x_573;
x_524 = x_84;
x_525 = x_7;
x_526 = x_8;
x_527 = x_9;
x_528 = x_10;
x_529 = x_80;
goto block_572;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_577 = l_Lean_Expr_appFn_x21(x_84);
x_578 = l_Lean_Expr_appArg_x21(x_577);
lean_dec_ref(x_577);
x_579 = l_Lean_Expr_appArg_x21(x_84);
lean_dec(x_84);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_579);
lean_inc_ref(x_578);
x_580 = l_Lean_Meta_mkEq(x_578, x_579, x_7, x_8, x_9, x_10, x_80);
if (lean_obj_tag(x_580) == 0)
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
lean_dec_ref(x_580);
x_583 = l_Lean_MVarId_rewrite___lam__1___closed__47;
x_584 = l_Lean_mkApp3(x_583, x_578, x_579, x_573);
x_523 = x_584;
x_524 = x_581;
x_525 = x_7;
x_526 = x_8;
x_527 = x_9;
x_528 = x_10;
x_529 = x_582;
goto block_572;
}
else
{
uint8_t x_585; 
lean_dec_ref(x_579);
lean_dec_ref(x_578);
lean_dec_ref(x_573);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_585 = !lean_is_exclusive(x_580);
if (x_585 == 0)
{
return x_580;
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_586 = lean_ctor_get(x_580, 0);
x_587 = lean_ctor_get(x_580, 1);
lean_inc(x_587);
lean_inc(x_586);
lean_dec(x_580);
x_588 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_588, 0, x_586);
lean_ctor_set(x_588, 1, x_587);
return x_588;
}
}
}
block_113:
{
uint8_t x_94; lean_object* x_95; 
x_94 = 0;
lean_inc(x_91);
lean_inc_ref(x_92);
lean_inc(x_90);
lean_inc_ref(x_86);
x_95 = l_Lean_Meta_postprocessAppMVars(x_2, x_1, x_81, x_83, x_93, x_94, x_86, x_90, x_92, x_91, x_87);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; size_t x_97; size_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = lean_array_size(x_81);
x_98 = 0;
x_99 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_MVarId_rewrite_spec__7(x_97, x_98, x_81);
x_100 = lean_unsigned_to_nat(0u);
x_101 = lean_array_get_size(x_99);
x_102 = l_Lean_MVarId_rewrite___lam__1___closed__4;
x_103 = lean_nat_dec_lt(x_100, x_101);
if (x_103 == 0)
{
lean_dec(x_101);
lean_dec_ref(x_99);
x_42 = x_86;
x_43 = x_88;
x_44 = x_89;
x_45 = x_90;
x_46 = x_100;
x_47 = x_91;
x_48 = x_98;
x_49 = x_92;
x_50 = x_102;
x_51 = x_96;
goto block_65;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_101, x_101);
if (x_104 == 0)
{
lean_dec(x_101);
lean_dec_ref(x_99);
x_42 = x_86;
x_43 = x_88;
x_44 = x_89;
x_45 = x_90;
x_46 = x_100;
x_47 = x_91;
x_48 = x_98;
x_49 = x_92;
x_50 = x_102;
x_51 = x_96;
goto block_65;
}
else
{
size_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_usize_of_nat(x_101);
lean_dec(x_101);
x_106 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__11(x_99, x_98, x_105, x_102, x_86, x_90, x_92, x_91, x_96);
lean_dec_ref(x_99);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec_ref(x_106);
x_42 = x_86;
x_43 = x_88;
x_44 = x_89;
x_45 = x_90;
x_46 = x_100;
x_47 = x_91;
x_48 = x_98;
x_49 = x_92;
x_50 = x_107;
x_51 = x_108;
goto block_65;
}
}
}
else
{
uint8_t x_109; 
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec_ref(x_88);
lean_dec_ref(x_86);
lean_dec(x_81);
lean_dec_ref(x_3);
x_109 = !lean_is_exclusive(x_95);
if (x_109 == 0)
{
return x_95;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_95, 0);
x_111 = lean_ctor_get(x_95, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_95);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
block_151:
{
lean_object* x_126; 
lean_inc(x_124);
lean_inc_ref(x_123);
lean_inc(x_122);
lean_inc_ref(x_121);
lean_inc_ref(x_114);
x_126 = l_Lean_Meta_getLevel(x_114, x_121, x_122, x_123, x_124, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec_ref(x_126);
lean_inc(x_124);
lean_inc_ref(x_123);
lean_inc(x_122);
lean_inc_ref(x_121);
lean_inc_ref(x_118);
x_129 = l_Lean_Meta_getLevel(x_118, x_121, x_122, x_123, x_124, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec_ref(x_129);
x_132 = lean_ctor_get(x_123, 2);
x_133 = l_Lean_MVarId_rewrite___lam__1___closed__6;
x_134 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_85;
 lean_ctor_set_tag(x_135, 1);
}
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_134);
if (lean_is_scalar(x_82)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_82;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_Expr_const___override(x_133, x_136);
x_138 = l_Lean_mkApp6(x_137, x_114, x_118, x_120, x_117, x_115, x_119);
x_139 = l_Lean_MVarId_rewrite___lam__1___closed__7;
x_140 = l_Lean_Option_get___at___Lean_MVarId_rewrite_spec__12(x_132, x_139);
if (x_140 == 0)
{
uint8_t x_141; 
x_141 = 1;
x_86 = x_121;
x_87 = x_131;
x_88 = x_116;
x_89 = x_138;
x_90 = x_122;
x_91 = x_124;
x_92 = x_123;
x_93 = x_141;
goto block_113;
}
else
{
uint8_t x_142; 
x_142 = 0;
x_86 = x_121;
x_87 = x_131;
x_88 = x_116;
x_89 = x_138;
x_90 = x_122;
x_91 = x_124;
x_92 = x_123;
x_93 = x_142;
goto block_113;
}
}
else
{
uint8_t x_143; 
lean_dec(x_127);
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec_ref(x_120);
lean_dec_ref(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec_ref(x_114);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_129);
if (x_143 == 0)
{
return x_129;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_129, 0);
x_145 = lean_ctor_get(x_129, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_129);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec_ref(x_120);
lean_dec_ref(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec_ref(x_114);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_126);
if (x_147 == 0)
{
return x_126;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_126, 0);
x_149 = lean_ctor_get(x_126, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_126);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
block_201:
{
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec_ref(x_166);
lean_inc(x_153);
lean_inc_ref(x_161);
lean_inc(x_156);
lean_inc_ref(x_164);
lean_inc_ref(x_152);
x_168 = l_Lean_Meta_withLocalDeclD___at___Lean_MVarId_rewrite_spec__13___redArg(x_163, x_152, x_157, x_164, x_156, x_161, x_153, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; uint8_t x_170; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_unbox(x_169);
lean_dec(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec_ref(x_168);
x_172 = l_Lean_MVarId_rewrite___lam__1___closed__9;
lean_inc_ref(x_159);
x_173 = l_Lean_MessageData_ofExpr(x_159);
x_174 = l_Lean_indentD(x_173);
if (lean_is_scalar(x_74)) {
 x_175 = lean_alloc_ctor(7, 2, 0);
} else {
 x_175 = x_74;
 lean_ctor_set_tag(x_175, 7);
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_Lean_MVarId_rewrite___lam__1___closed__11;
x_177 = l_Lean_indentExpr(x_160);
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = l_Lean_MVarId_rewrite___lam__1___closed__13;
x_180 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
lean_inc_ref(x_158);
x_181 = l_Lean_indentExpr(x_158);
x_182 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = l_Lean_MessageData_note(x_182);
x_184 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_184, 0, x_175);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
lean_inc(x_1);
lean_inc(x_2);
x_186 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_185, x_164, x_156, x_161, x_153, x_171);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec_ref(x_186);
x_114 = x_152;
x_115 = x_159;
x_116 = x_154;
x_117 = x_155;
x_118 = x_162;
x_119 = x_165;
x_120 = x_158;
x_121 = x_164;
x_122 = x_156;
x_123 = x_161;
x_124 = x_153;
x_125 = x_187;
goto block_151;
}
else
{
uint8_t x_188; 
lean_dec_ref(x_165);
lean_dec_ref(x_164);
lean_dec_ref(x_162);
lean_dec_ref(x_161);
lean_dec_ref(x_159);
lean_dec_ref(x_158);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_186);
if (x_188 == 0)
{
return x_186;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_186, 0);
x_190 = lean_ctor_get(x_186, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_186);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
lean_object* x_192; 
lean_dec_ref(x_160);
lean_dec(x_74);
x_192 = lean_ctor_get(x_168, 1);
lean_inc(x_192);
lean_dec_ref(x_168);
x_114 = x_152;
x_115 = x_159;
x_116 = x_154;
x_117 = x_155;
x_118 = x_162;
x_119 = x_165;
x_120 = x_158;
x_121 = x_164;
x_122 = x_156;
x_123 = x_161;
x_124 = x_153;
x_125 = x_192;
goto block_151;
}
}
else
{
uint8_t x_193; 
lean_dec_ref(x_165);
lean_dec_ref(x_164);
lean_dec_ref(x_162);
lean_dec_ref(x_161);
lean_dec_ref(x_160);
lean_dec_ref(x_159);
lean_dec_ref(x_158);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_193 = !lean_is_exclusive(x_168);
if (x_193 == 0)
{
return x_168;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_168, 0);
x_195 = lean_ctor_get(x_168, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_168);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
else
{
uint8_t x_197; 
lean_dec_ref(x_165);
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec_ref(x_162);
lean_dec_ref(x_161);
lean_dec_ref(x_160);
lean_dec_ref(x_159);
lean_dec_ref(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_197 = !lean_is_exclusive(x_166);
if (x_197 == 0)
{
return x_166;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_166, 0);
x_199 = lean_ctor_get(x_166, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_166);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
block_247:
{
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec_ref(x_212);
x_220 = l_Lean_MVarId_rewrite___lam__1___closed__15;
lean_inc_ref(x_210);
x_221 = l_Lean_MessageData_ofExpr(x_210);
x_222 = l_Lean_indentD(x_221);
x_223 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_222);
x_224 = l_Lean_MVarId_rewrite___lam__1___closed__17;
x_225 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
x_226 = l_Lean_Exception_toMessageData(x_215);
x_227 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
x_228 = l_Lean_MVarId_rewrite___lam__1___closed__19;
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = l_Lean_MVarId_rewrite___lam__1___closed__6;
x_231 = l_Lean_MessageData_ofConstName(x_230, x_219);
x_232 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lean_MVarId_rewrite___lam__1___closed__21;
x_234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = l_Lean_MVarId_rewrite___lam__1___closed__24;
x_236 = l_Lean_MessageData_ofConstName(x_235, x_219);
x_237 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_236);
x_238 = l_Lean_MVarId_rewrite___lam__1___closed__26;
x_239 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_240 = l_Lean_MVarId_rewrite___lam__1___closed__28;
x_241 = l_Lean_MessageData_ofConstName(x_240, x_219);
x_242 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_241);
x_243 = l_Lean_MVarId_rewrite___lam__1___closed__30;
x_244 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_244);
lean_inc(x_1);
lean_inc(x_2);
x_246 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_245, x_217, x_206, x_214, x_203, x_207);
x_152 = x_202;
x_153 = x_203;
x_154 = x_204;
x_155 = x_205;
x_156 = x_206;
x_157 = x_208;
x_158 = x_209;
x_159 = x_210;
x_160 = x_211;
x_161 = x_214;
x_162 = x_213;
x_163 = x_216;
x_164 = x_217;
x_165 = x_218;
x_166 = x_246;
goto block_201;
}
else
{
lean_dec_ref(x_215);
lean_dec(x_207);
x_152 = x_202;
x_153 = x_203;
x_154 = x_204;
x_155 = x_205;
x_156 = x_206;
x_157 = x_208;
x_158 = x_209;
x_159 = x_210;
x_160 = x_211;
x_161 = x_214;
x_162 = x_213;
x_163 = x_216;
x_164 = x_217;
x_165 = x_218;
x_166 = x_212;
goto block_201;
}
}
block_277:
{
lean_object* x_261; 
lean_inc(x_259);
lean_inc_ref(x_258);
lean_inc(x_257);
lean_inc_ref(x_256);
lean_inc_ref(x_251);
x_261 = lean_infer_type(x_251, x_256, x_257, x_258, x_259, x_260);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; lean_object* x_268; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec_ref(x_261);
lean_inc(x_262);
x_264 = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__0___boxed), 8, 2);
lean_closure_set(x_264, 0, x_248);
lean_closure_set(x_264, 1, x_262);
x_265 = l_Lean_MVarId_rewrite___lam__1___closed__32;
x_266 = 0;
lean_inc_ref(x_249);
x_267 = l_Lean_mkLambda(x_265, x_266, x_249, x_250);
lean_inc(x_259);
lean_inc_ref(x_258);
lean_inc(x_257);
lean_inc_ref(x_256);
lean_inc_ref(x_267);
x_268 = l_Lean_Meta_check(x_267, x_256, x_257, x_258, x_259, x_263);
if (lean_obj_tag(x_268) == 0)
{
x_152 = x_249;
x_153 = x_259;
x_154 = x_255;
x_155 = x_252;
x_156 = x_257;
x_157 = x_264;
x_158 = x_254;
x_159 = x_267;
x_160 = x_251;
x_161 = x_258;
x_162 = x_262;
x_163 = x_265;
x_164 = x_256;
x_165 = x_253;
x_166 = x_268;
goto block_201;
}
else
{
lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
x_271 = l_Lean_Exception_isInterrupt(x_269);
if (x_271 == 0)
{
uint8_t x_272; 
x_272 = l_Lean_Exception_isRuntime(x_269);
x_202 = x_249;
x_203 = x_259;
x_204 = x_255;
x_205 = x_252;
x_206 = x_257;
x_207 = x_270;
x_208 = x_264;
x_209 = x_254;
x_210 = x_267;
x_211 = x_251;
x_212 = x_268;
x_213 = x_262;
x_214 = x_258;
x_215 = x_269;
x_216 = x_265;
x_217 = x_256;
x_218 = x_253;
x_219 = x_272;
goto block_247;
}
else
{
x_202 = x_249;
x_203 = x_259;
x_204 = x_255;
x_205 = x_252;
x_206 = x_257;
x_207 = x_270;
x_208 = x_264;
x_209 = x_254;
x_210 = x_267;
x_211 = x_251;
x_212 = x_268;
x_213 = x_262;
x_214 = x_258;
x_215 = x_269;
x_216 = x_265;
x_217 = x_256;
x_218 = x_253;
x_219 = x_271;
goto block_247;
}
}
}
else
{
uint8_t x_273; 
lean_dec(x_259);
lean_dec_ref(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec_ref(x_255);
lean_dec_ref(x_254);
lean_dec_ref(x_253);
lean_dec_ref(x_252);
lean_dec_ref(x_251);
lean_dec_ref(x_250);
lean_dec_ref(x_249);
lean_dec_ref(x_248);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_273 = !lean_is_exclusive(x_261);
if (x_273 == 0)
{
return x_261;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_261, 0);
x_275 = lean_ctor_get(x_261, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_261);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
block_301:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_289 = lean_expr_instantiate1(x_278, x_281);
x_290 = l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4___redArg(x_289, x_285, x_288);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec_ref(x_290);
x_293 = l_Lean_Expr_hasBinderNameHint(x_281);
if (x_293 == 0)
{
lean_inc_ref(x_278);
x_248 = x_278;
x_249 = x_279;
x_250 = x_278;
x_251 = x_280;
x_252 = x_281;
x_253 = x_282;
x_254 = x_283;
x_255 = x_291;
x_256 = x_284;
x_257 = x_285;
x_258 = x_286;
x_259 = x_287;
x_260 = x_292;
goto block_277;
}
else
{
lean_object* x_294; 
lean_inc(x_287);
lean_inc_ref(x_286);
x_294 = l_Lean_Expr_resolveBinderNameHint(x_291, x_286, x_287, x_292);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec_ref(x_294);
lean_inc_ref(x_278);
x_248 = x_278;
x_249 = x_279;
x_250 = x_278;
x_251 = x_280;
x_252 = x_281;
x_253 = x_282;
x_254 = x_283;
x_255 = x_295;
x_256 = x_284;
x_257 = x_285;
x_258 = x_286;
x_259 = x_287;
x_260 = x_296;
goto block_277;
}
else
{
uint8_t x_297; 
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec_ref(x_283);
lean_dec_ref(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_278);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_297 = !lean_is_exclusive(x_294);
if (x_297 == 0)
{
return x_294;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_294, 0);
x_299 = lean_ctor_get(x_294, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_294);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
}
}
block_522:
{
lean_object* x_312; uint8_t x_313; 
x_312 = l_Lean_Expr_getAppFn(x_305);
x_313 = l_Lean_Expr_isMVar(x_312);
lean_dec_ref(x_312);
if (x_313 == 0)
{
lean_object* x_314; uint8_t x_315; 
lean_dec_ref(x_304);
x_314 = l_Lean_instantiateMVars___at___Lean_MVarId_rewrite_spec__4___redArg(x_4, x_308, x_311);
x_315 = !lean_is_exclusive(x_314);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; uint8_t x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_316 = lean_ctor_get(x_314, 0);
x_317 = lean_ctor_get(x_314, 1);
x_318 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_319 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_320 = lean_ctor_get(x_5, 0);
lean_inc(x_320);
lean_dec_ref(x_5);
x_321 = l_Lean_Meta_Context_config(x_307);
x_322 = !lean_is_exclusive(x_321);
if (x_322 == 0)
{
uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; uint8_t x_331; uint64_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_323 = lean_ctor_get_uint8(x_307, sizeof(void*)*7);
x_324 = lean_ctor_get(x_307, 1);
x_325 = lean_ctor_get(x_307, 2);
x_326 = lean_ctor_get(x_307, 3);
x_327 = lean_ctor_get(x_307, 4);
x_328 = lean_ctor_get(x_307, 5);
x_329 = lean_ctor_get(x_307, 6);
x_330 = lean_ctor_get_uint8(x_307, sizeof(void*)*7 + 1);
x_331 = lean_ctor_get_uint8(x_307, sizeof(void*)*7 + 2);
lean_ctor_set_uint8(x_321, 8, x_319);
lean_ctor_set_uint8(x_321, 9, x_318);
x_332 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_321);
x_333 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_333, 0, x_321);
lean_ctor_set_uint64(x_333, sizeof(void*)*1, x_332);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc_ref(x_326);
lean_inc_ref(x_325);
lean_inc(x_324);
x_334 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_324);
lean_ctor_set(x_334, 2, x_325);
lean_ctor_set(x_334, 3, x_326);
lean_ctor_set(x_334, 4, x_327);
lean_ctor_set(x_334, 5, x_328);
lean_ctor_set(x_334, 6, x_329);
lean_ctor_set_uint8(x_334, sizeof(void*)*7, x_323);
lean_ctor_set_uint8(x_334, sizeof(void*)*7 + 1, x_330);
lean_ctor_set_uint8(x_334, sizeof(void*)*7 + 2, x_331);
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_308);
lean_inc_ref(x_305);
lean_inc(x_316);
x_335 = l_Lean_Meta_kabstract(x_316, x_305, x_320, x_334, x_308, x_309, x_310, x_317);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; uint8_t x_338; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec_ref(x_335);
x_338 = l_Lean_Expr_hasLooseBVars(x_336);
if (x_338 == 0)
{
lean_object* x_339; 
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_308);
lean_inc_ref(x_307);
lean_inc_ref(x_305);
lean_inc(x_316);
x_339 = l_Lean_Meta_addPPExplicitToExposeDiff(x_316, x_305, x_307, x_308, x_309, x_310, x_337);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; uint8_t x_342; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec_ref(x_339);
x_342 = !lean_is_exclusive(x_340);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_343 = lean_ctor_get(x_340, 0);
x_344 = lean_ctor_get(x_340, 1);
x_345 = l_Lean_MVarId_rewrite___lam__1___closed__34;
x_346 = l_Lean_indentExpr(x_344);
lean_ctor_set_tag(x_340, 7);
lean_ctor_set(x_340, 1, x_346);
lean_ctor_set(x_340, 0, x_345);
x_347 = l_Lean_MVarId_rewrite___lam__1___closed__36;
lean_ctor_set_tag(x_314, 7);
lean_ctor_set(x_314, 1, x_347);
lean_ctor_set(x_314, 0, x_340);
x_348 = l_Lean_indentExpr(x_343);
x_349 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_349, 0, x_314);
lean_ctor_set(x_349, 1, x_348);
x_350 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_350, 0, x_349);
lean_inc(x_1);
lean_inc(x_2);
x_351 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_350, x_307, x_308, x_309, x_310, x_341);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; 
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
lean_dec_ref(x_351);
x_278 = x_336;
x_279 = x_302;
x_280 = x_316;
x_281 = x_306;
x_282 = x_303;
x_283 = x_305;
x_284 = x_307;
x_285 = x_308;
x_286 = x_309;
x_287 = x_310;
x_288 = x_352;
goto block_301;
}
else
{
uint8_t x_353; 
lean_dec(x_336);
lean_dec(x_316);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec_ref(x_306);
lean_dec_ref(x_305);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_353 = !lean_is_exclusive(x_351);
if (x_353 == 0)
{
return x_351;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_351, 0);
x_355 = lean_ctor_get(x_351, 1);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_351);
x_356 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
return x_356;
}
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_357 = lean_ctor_get(x_340, 0);
x_358 = lean_ctor_get(x_340, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_340);
x_359 = l_Lean_MVarId_rewrite___lam__1___closed__34;
x_360 = l_Lean_indentExpr(x_358);
x_361 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
x_362 = l_Lean_MVarId_rewrite___lam__1___closed__36;
lean_ctor_set_tag(x_314, 7);
lean_ctor_set(x_314, 1, x_362);
lean_ctor_set(x_314, 0, x_361);
x_363 = l_Lean_indentExpr(x_357);
x_364 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_364, 0, x_314);
lean_ctor_set(x_364, 1, x_363);
x_365 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_365, 0, x_364);
lean_inc(x_1);
lean_inc(x_2);
x_366 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_365, x_307, x_308, x_309, x_310, x_341);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; 
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
lean_dec_ref(x_366);
x_278 = x_336;
x_279 = x_302;
x_280 = x_316;
x_281 = x_306;
x_282 = x_303;
x_283 = x_305;
x_284 = x_307;
x_285 = x_308;
x_286 = x_309;
x_287 = x_310;
x_288 = x_367;
goto block_301;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_336);
lean_dec(x_316);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec_ref(x_306);
lean_dec_ref(x_305);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_368 = lean_ctor_get(x_366, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_366, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_370 = x_366;
} else {
 lean_dec_ref(x_366);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(1, 2, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_369);
return x_371;
}
}
}
else
{
uint8_t x_372; 
lean_dec(x_336);
lean_free_object(x_314);
lean_dec(x_316);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec_ref(x_306);
lean_dec_ref(x_305);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_372 = !lean_is_exclusive(x_339);
if (x_372 == 0)
{
return x_339;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_339, 0);
x_374 = lean_ctor_get(x_339, 1);
lean_inc(x_374);
lean_inc(x_373);
lean_dec(x_339);
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
return x_375;
}
}
}
else
{
lean_free_object(x_314);
x_278 = x_336;
x_279 = x_302;
x_280 = x_316;
x_281 = x_306;
x_282 = x_303;
x_283 = x_305;
x_284 = x_307;
x_285 = x_308;
x_286 = x_309;
x_287 = x_310;
x_288 = x_337;
goto block_301;
}
}
else
{
uint8_t x_376; 
lean_free_object(x_314);
lean_dec(x_316);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec_ref(x_306);
lean_dec_ref(x_305);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_376 = !lean_is_exclusive(x_335);
if (x_376 == 0)
{
return x_335;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_335, 0);
x_378 = lean_ctor_get(x_335, 1);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_335);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
return x_379;
}
}
}
else
{
uint8_t x_380; uint8_t x_381; uint8_t x_382; uint8_t x_383; uint8_t x_384; uint8_t x_385; uint8_t x_386; uint8_t x_387; uint8_t x_388; uint8_t x_389; uint8_t x_390; uint8_t x_391; uint8_t x_392; uint8_t x_393; uint8_t x_394; uint8_t x_395; uint8_t x_396; uint8_t x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; uint8_t x_405; lean_object* x_406; uint64_t x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_380 = lean_ctor_get_uint8(x_321, 0);
x_381 = lean_ctor_get_uint8(x_321, 1);
x_382 = lean_ctor_get_uint8(x_321, 2);
x_383 = lean_ctor_get_uint8(x_321, 3);
x_384 = lean_ctor_get_uint8(x_321, 4);
x_385 = lean_ctor_get_uint8(x_321, 5);
x_386 = lean_ctor_get_uint8(x_321, 6);
x_387 = lean_ctor_get_uint8(x_321, 7);
x_388 = lean_ctor_get_uint8(x_321, 10);
x_389 = lean_ctor_get_uint8(x_321, 11);
x_390 = lean_ctor_get_uint8(x_321, 12);
x_391 = lean_ctor_get_uint8(x_321, 13);
x_392 = lean_ctor_get_uint8(x_321, 14);
x_393 = lean_ctor_get_uint8(x_321, 15);
x_394 = lean_ctor_get_uint8(x_321, 16);
x_395 = lean_ctor_get_uint8(x_321, 17);
x_396 = lean_ctor_get_uint8(x_321, 18);
lean_dec(x_321);
x_397 = lean_ctor_get_uint8(x_307, sizeof(void*)*7);
x_398 = lean_ctor_get(x_307, 1);
x_399 = lean_ctor_get(x_307, 2);
x_400 = lean_ctor_get(x_307, 3);
x_401 = lean_ctor_get(x_307, 4);
x_402 = lean_ctor_get(x_307, 5);
x_403 = lean_ctor_get(x_307, 6);
x_404 = lean_ctor_get_uint8(x_307, sizeof(void*)*7 + 1);
x_405 = lean_ctor_get_uint8(x_307, sizeof(void*)*7 + 2);
x_406 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_406, 0, x_380);
lean_ctor_set_uint8(x_406, 1, x_381);
lean_ctor_set_uint8(x_406, 2, x_382);
lean_ctor_set_uint8(x_406, 3, x_383);
lean_ctor_set_uint8(x_406, 4, x_384);
lean_ctor_set_uint8(x_406, 5, x_385);
lean_ctor_set_uint8(x_406, 6, x_386);
lean_ctor_set_uint8(x_406, 7, x_387);
lean_ctor_set_uint8(x_406, 8, x_319);
lean_ctor_set_uint8(x_406, 9, x_318);
lean_ctor_set_uint8(x_406, 10, x_388);
lean_ctor_set_uint8(x_406, 11, x_389);
lean_ctor_set_uint8(x_406, 12, x_390);
lean_ctor_set_uint8(x_406, 13, x_391);
lean_ctor_set_uint8(x_406, 14, x_392);
lean_ctor_set_uint8(x_406, 15, x_393);
lean_ctor_set_uint8(x_406, 16, x_394);
lean_ctor_set_uint8(x_406, 17, x_395);
lean_ctor_set_uint8(x_406, 18, x_396);
x_407 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_406);
x_408 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set_uint64(x_408, sizeof(void*)*1, x_407);
lean_inc(x_403);
lean_inc(x_402);
lean_inc(x_401);
lean_inc_ref(x_400);
lean_inc_ref(x_399);
lean_inc(x_398);
x_409 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_398);
lean_ctor_set(x_409, 2, x_399);
lean_ctor_set(x_409, 3, x_400);
lean_ctor_set(x_409, 4, x_401);
lean_ctor_set(x_409, 5, x_402);
lean_ctor_set(x_409, 6, x_403);
lean_ctor_set_uint8(x_409, sizeof(void*)*7, x_397);
lean_ctor_set_uint8(x_409, sizeof(void*)*7 + 1, x_404);
lean_ctor_set_uint8(x_409, sizeof(void*)*7 + 2, x_405);
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_308);
lean_inc_ref(x_305);
lean_inc(x_316);
x_410 = l_Lean_Meta_kabstract(x_316, x_305, x_320, x_409, x_308, x_309, x_310, x_317);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec_ref(x_410);
x_413 = l_Lean_Expr_hasLooseBVars(x_411);
if (x_413 == 0)
{
lean_object* x_414; 
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_308);
lean_inc_ref(x_307);
lean_inc_ref(x_305);
lean_inc(x_316);
x_414 = l_Lean_Meta_addPPExplicitToExposeDiff(x_316, x_305, x_307, x_308, x_309, x_310, x_412);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec_ref(x_414);
x_417 = lean_ctor_get(x_415, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_415, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_419 = x_415;
} else {
 lean_dec_ref(x_415);
 x_419 = lean_box(0);
}
x_420 = l_Lean_MVarId_rewrite___lam__1___closed__34;
x_421 = l_Lean_indentExpr(x_418);
if (lean_is_scalar(x_419)) {
 x_422 = lean_alloc_ctor(7, 2, 0);
} else {
 x_422 = x_419;
 lean_ctor_set_tag(x_422, 7);
}
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_421);
x_423 = l_Lean_MVarId_rewrite___lam__1___closed__36;
lean_ctor_set_tag(x_314, 7);
lean_ctor_set(x_314, 1, x_423);
lean_ctor_set(x_314, 0, x_422);
x_424 = l_Lean_indentExpr(x_417);
x_425 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_425, 0, x_314);
lean_ctor_set(x_425, 1, x_424);
x_426 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_426, 0, x_425);
lean_inc(x_1);
lean_inc(x_2);
x_427 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_426, x_307, x_308, x_309, x_310, x_416);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; 
x_428 = lean_ctor_get(x_427, 1);
lean_inc(x_428);
lean_dec_ref(x_427);
x_278 = x_411;
x_279 = x_302;
x_280 = x_316;
x_281 = x_306;
x_282 = x_303;
x_283 = x_305;
x_284 = x_307;
x_285 = x_308;
x_286 = x_309;
x_287 = x_310;
x_288 = x_428;
goto block_301;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_411);
lean_dec(x_316);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec_ref(x_306);
lean_dec_ref(x_305);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_429 = lean_ctor_get(x_427, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_427, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 x_431 = x_427;
} else {
 lean_dec_ref(x_427);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 2, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_429);
lean_ctor_set(x_432, 1, x_430);
return x_432;
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_411);
lean_free_object(x_314);
lean_dec(x_316);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec_ref(x_306);
lean_dec_ref(x_305);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_433 = lean_ctor_get(x_414, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_414, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_435 = x_414;
} else {
 lean_dec_ref(x_414);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(1, 2, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_433);
lean_ctor_set(x_436, 1, x_434);
return x_436;
}
}
else
{
lean_free_object(x_314);
x_278 = x_411;
x_279 = x_302;
x_280 = x_316;
x_281 = x_306;
x_282 = x_303;
x_283 = x_305;
x_284 = x_307;
x_285 = x_308;
x_286 = x_309;
x_287 = x_310;
x_288 = x_412;
goto block_301;
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_free_object(x_314);
lean_dec(x_316);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec_ref(x_306);
lean_dec_ref(x_305);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_437 = lean_ctor_get(x_410, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_410, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_439 = x_410;
} else {
 lean_dec_ref(x_410);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_440 = lean_alloc_ctor(1, 2, 0);
} else {
 x_440 = x_439;
}
lean_ctor_set(x_440, 0, x_437);
lean_ctor_set(x_440, 1, x_438);
return x_440;
}
}
}
else
{
lean_object* x_441; lean_object* x_442; uint8_t x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; uint8_t x_448; uint8_t x_449; uint8_t x_450; uint8_t x_451; uint8_t x_452; uint8_t x_453; uint8_t x_454; uint8_t x_455; uint8_t x_456; uint8_t x_457; uint8_t x_458; uint8_t x_459; uint8_t x_460; uint8_t x_461; uint8_t x_462; uint8_t x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; uint8_t x_473; lean_object* x_474; uint64_t x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_441 = lean_ctor_get(x_314, 0);
x_442 = lean_ctor_get(x_314, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_314);
x_443 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_444 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_445 = lean_ctor_get(x_5, 0);
lean_inc(x_445);
lean_dec_ref(x_5);
x_446 = l_Lean_Meta_Context_config(x_307);
x_447 = lean_ctor_get_uint8(x_446, 0);
x_448 = lean_ctor_get_uint8(x_446, 1);
x_449 = lean_ctor_get_uint8(x_446, 2);
x_450 = lean_ctor_get_uint8(x_446, 3);
x_451 = lean_ctor_get_uint8(x_446, 4);
x_452 = lean_ctor_get_uint8(x_446, 5);
x_453 = lean_ctor_get_uint8(x_446, 6);
x_454 = lean_ctor_get_uint8(x_446, 7);
x_455 = lean_ctor_get_uint8(x_446, 10);
x_456 = lean_ctor_get_uint8(x_446, 11);
x_457 = lean_ctor_get_uint8(x_446, 12);
x_458 = lean_ctor_get_uint8(x_446, 13);
x_459 = lean_ctor_get_uint8(x_446, 14);
x_460 = lean_ctor_get_uint8(x_446, 15);
x_461 = lean_ctor_get_uint8(x_446, 16);
x_462 = lean_ctor_get_uint8(x_446, 17);
x_463 = lean_ctor_get_uint8(x_446, 18);
if (lean_is_exclusive(x_446)) {
 x_464 = x_446;
} else {
 lean_dec_ref(x_446);
 x_464 = lean_box(0);
}
x_465 = lean_ctor_get_uint8(x_307, sizeof(void*)*7);
x_466 = lean_ctor_get(x_307, 1);
x_467 = lean_ctor_get(x_307, 2);
x_468 = lean_ctor_get(x_307, 3);
x_469 = lean_ctor_get(x_307, 4);
x_470 = lean_ctor_get(x_307, 5);
x_471 = lean_ctor_get(x_307, 6);
x_472 = lean_ctor_get_uint8(x_307, sizeof(void*)*7 + 1);
x_473 = lean_ctor_get_uint8(x_307, sizeof(void*)*7 + 2);
if (lean_is_scalar(x_464)) {
 x_474 = lean_alloc_ctor(0, 0, 19);
} else {
 x_474 = x_464;
}
lean_ctor_set_uint8(x_474, 0, x_447);
lean_ctor_set_uint8(x_474, 1, x_448);
lean_ctor_set_uint8(x_474, 2, x_449);
lean_ctor_set_uint8(x_474, 3, x_450);
lean_ctor_set_uint8(x_474, 4, x_451);
lean_ctor_set_uint8(x_474, 5, x_452);
lean_ctor_set_uint8(x_474, 6, x_453);
lean_ctor_set_uint8(x_474, 7, x_454);
lean_ctor_set_uint8(x_474, 8, x_444);
lean_ctor_set_uint8(x_474, 9, x_443);
lean_ctor_set_uint8(x_474, 10, x_455);
lean_ctor_set_uint8(x_474, 11, x_456);
lean_ctor_set_uint8(x_474, 12, x_457);
lean_ctor_set_uint8(x_474, 13, x_458);
lean_ctor_set_uint8(x_474, 14, x_459);
lean_ctor_set_uint8(x_474, 15, x_460);
lean_ctor_set_uint8(x_474, 16, x_461);
lean_ctor_set_uint8(x_474, 17, x_462);
lean_ctor_set_uint8(x_474, 18, x_463);
x_475 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_474);
x_476 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set_uint64(x_476, sizeof(void*)*1, x_475);
lean_inc(x_471);
lean_inc(x_470);
lean_inc(x_469);
lean_inc_ref(x_468);
lean_inc_ref(x_467);
lean_inc(x_466);
x_477 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_466);
lean_ctor_set(x_477, 2, x_467);
lean_ctor_set(x_477, 3, x_468);
lean_ctor_set(x_477, 4, x_469);
lean_ctor_set(x_477, 5, x_470);
lean_ctor_set(x_477, 6, x_471);
lean_ctor_set_uint8(x_477, sizeof(void*)*7, x_465);
lean_ctor_set_uint8(x_477, sizeof(void*)*7 + 1, x_472);
lean_ctor_set_uint8(x_477, sizeof(void*)*7 + 2, x_473);
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_308);
lean_inc_ref(x_305);
lean_inc(x_441);
x_478 = l_Lean_Meta_kabstract(x_441, x_305, x_445, x_477, x_308, x_309, x_310, x_442);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; uint8_t x_481; 
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
lean_dec_ref(x_478);
x_481 = l_Lean_Expr_hasLooseBVars(x_479);
if (x_481 == 0)
{
lean_object* x_482; 
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_308);
lean_inc_ref(x_307);
lean_inc_ref(x_305);
lean_inc(x_441);
x_482 = l_Lean_Meta_addPPExplicitToExposeDiff(x_441, x_305, x_307, x_308, x_309, x_310, x_480);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_482, 1);
lean_inc(x_484);
lean_dec_ref(x_482);
x_485 = lean_ctor_get(x_483, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_483, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_487 = x_483;
} else {
 lean_dec_ref(x_483);
 x_487 = lean_box(0);
}
x_488 = l_Lean_MVarId_rewrite___lam__1___closed__34;
x_489 = l_Lean_indentExpr(x_486);
if (lean_is_scalar(x_487)) {
 x_490 = lean_alloc_ctor(7, 2, 0);
} else {
 x_490 = x_487;
 lean_ctor_set_tag(x_490, 7);
}
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
x_491 = l_Lean_MVarId_rewrite___lam__1___closed__36;
x_492 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_491);
x_493 = l_Lean_indentExpr(x_485);
x_494 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
x_495 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_495, 0, x_494);
lean_inc(x_1);
lean_inc(x_2);
x_496 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_495, x_307, x_308, x_309, x_310, x_484);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; 
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
lean_dec_ref(x_496);
x_278 = x_479;
x_279 = x_302;
x_280 = x_441;
x_281 = x_306;
x_282 = x_303;
x_283 = x_305;
x_284 = x_307;
x_285 = x_308;
x_286 = x_309;
x_287 = x_310;
x_288 = x_497;
goto block_301;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
lean_dec(x_479);
lean_dec(x_441);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec_ref(x_306);
lean_dec_ref(x_305);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_498 = lean_ctor_get(x_496, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_496, 1);
lean_inc(x_499);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_500 = x_496;
} else {
 lean_dec_ref(x_496);
 x_500 = lean_box(0);
}
if (lean_is_scalar(x_500)) {
 x_501 = lean_alloc_ctor(1, 2, 0);
} else {
 x_501 = x_500;
}
lean_ctor_set(x_501, 0, x_498);
lean_ctor_set(x_501, 1, x_499);
return x_501;
}
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
lean_dec(x_479);
lean_dec(x_441);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec_ref(x_306);
lean_dec_ref(x_305);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_502 = lean_ctor_get(x_482, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_482, 1);
lean_inc(x_503);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_504 = x_482;
} else {
 lean_dec_ref(x_482);
 x_504 = lean_box(0);
}
if (lean_is_scalar(x_504)) {
 x_505 = lean_alloc_ctor(1, 2, 0);
} else {
 x_505 = x_504;
}
lean_ctor_set(x_505, 0, x_502);
lean_ctor_set(x_505, 1, x_503);
return x_505;
}
}
else
{
x_278 = x_479;
x_279 = x_302;
x_280 = x_441;
x_281 = x_306;
x_282 = x_303;
x_283 = x_305;
x_284 = x_307;
x_285 = x_308;
x_286 = x_309;
x_287 = x_310;
x_288 = x_480;
goto block_301;
}
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_441);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec_ref(x_306);
lean_dec_ref(x_305);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_506 = lean_ctor_get(x_478, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_478, 1);
lean_inc(x_507);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_508 = x_478;
} else {
 lean_dec_ref(x_478);
 x_508 = lean_box(0);
}
if (lean_is_scalar(x_508)) {
 x_509 = lean_alloc_ctor(1, 2, 0);
} else {
 x_509 = x_508;
}
lean_ctor_set(x_509, 0, x_506);
lean_ctor_set(x_509, 1, x_507);
return x_509;
}
}
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_518; 
lean_dec_ref(x_306);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_510 = l_Lean_MVarId_rewrite___lam__1___closed__38;
x_511 = l_Lean_MessageData_ofExpr(x_305);
x_512 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_512, 0, x_510);
lean_ctor_set(x_512, 1, x_511);
x_513 = l_Lean_MVarId_rewrite___lam__1___closed__40;
x_514 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_514, 0, x_512);
lean_ctor_set(x_514, 1, x_513);
x_515 = l_Lean_indentExpr(x_304);
x_516 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
x_517 = l_Lean_throwError___at___Lean_MVarId_rewrite_spec__5___redArg(x_516, x_307, x_308, x_309, x_310, x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
x_518 = !lean_is_exclusive(x_517);
if (x_518 == 0)
{
return x_517;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_519 = lean_ctor_get(x_517, 0);
x_520 = lean_ctor_get(x_517, 1);
lean_inc(x_520);
lean_inc(x_519);
lean_dec(x_517);
x_521 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_521, 0, x_519);
lean_ctor_set(x_521, 1, x_520);
return x_521;
}
}
}
block_572:
{
lean_object* x_530; 
lean_inc(x_528);
lean_inc_ref(x_527);
lean_inc(x_526);
lean_inc_ref(x_525);
lean_inc_ref(x_524);
x_530 = l_Lean_Meta_matchEq_x3f(x_524, x_525, x_526, x_527, x_528, x_529);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; 
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; 
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_532 = lean_ctor_get(x_530, 1);
lean_inc(x_532);
lean_dec_ref(x_530);
lean_inc(x_528);
lean_inc_ref(x_527);
lean_inc(x_526);
lean_inc_ref(x_525);
lean_inc_ref(x_524);
x_533 = l_Lean_Meta_isProp(x_524, x_525, x_526, x_527, x_528, x_532);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; uint8_t x_535; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_unbox(x_534);
lean_dec(x_534);
if (x_535 == 0)
{
lean_object* x_536; lean_object* x_537; 
x_536 = lean_ctor_get(x_533, 1);
lean_inc(x_536);
lean_dec_ref(x_533);
x_537 = l_Lean_MVarId_rewrite___lam__1___closed__41;
x_12 = x_536;
x_13 = x_528;
x_14 = x_525;
x_15 = x_524;
x_16 = x_526;
x_17 = x_523;
x_18 = x_527;
x_19 = x_537;
goto block_31;
}
else
{
lean_object* x_538; lean_object* x_539; 
x_538 = lean_ctor_get(x_533, 1);
lean_inc(x_538);
lean_dec_ref(x_533);
x_539 = l_Lean_MVarId_rewrite___lam__1___closed__42;
x_12 = x_538;
x_13 = x_528;
x_14 = x_525;
x_15 = x_524;
x_16 = x_526;
x_17 = x_523;
x_18 = x_527;
x_19 = x_539;
goto block_31;
}
}
else
{
uint8_t x_540; 
lean_dec(x_528);
lean_dec_ref(x_527);
lean_dec(x_526);
lean_dec_ref(x_525);
lean_dec_ref(x_524);
lean_dec_ref(x_523);
x_540 = !lean_is_exclusive(x_533);
if (x_540 == 0)
{
return x_533;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_541 = lean_ctor_get(x_533, 0);
x_542 = lean_ctor_get(x_533, 1);
lean_inc(x_542);
lean_inc(x_541);
lean_dec(x_533);
x_543 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_543, 0, x_541);
lean_ctor_set(x_543, 1, x_542);
return x_543;
}
}
}
else
{
lean_object* x_544; lean_object* x_545; 
x_544 = lean_ctor_get(x_531, 0);
lean_inc(x_544);
lean_dec_ref(x_531);
x_545 = lean_ctor_get(x_544, 1);
lean_inc(x_545);
if (x_6 == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_546 = lean_ctor_get(x_530, 1);
lean_inc(x_546);
lean_dec_ref(x_530);
x_547 = lean_ctor_get(x_544, 0);
lean_inc(x_547);
lean_dec(x_544);
x_548 = lean_ctor_get(x_545, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_545, 1);
lean_inc(x_549);
lean_dec(x_545);
x_302 = x_547;
x_303 = x_523;
x_304 = x_524;
x_305 = x_548;
x_306 = x_549;
x_307 = x_525;
x_308 = x_526;
x_309 = x_527;
x_310 = x_528;
x_311 = x_546;
goto block_522;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_dec_ref(x_524);
x_550 = lean_ctor_get(x_530, 1);
lean_inc(x_550);
lean_dec_ref(x_530);
x_551 = lean_ctor_get(x_544, 0);
lean_inc(x_551);
lean_dec(x_544);
x_552 = lean_ctor_get(x_545, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_545, 1);
lean_inc(x_553);
lean_dec(x_545);
lean_inc(x_528);
lean_inc_ref(x_527);
lean_inc(x_526);
lean_inc_ref(x_525);
x_554 = l_Lean_Meta_mkEqSymm(x_523, x_525, x_526, x_527, x_528, x_550);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec_ref(x_554);
lean_inc(x_528);
lean_inc_ref(x_527);
lean_inc(x_526);
lean_inc_ref(x_525);
lean_inc(x_552);
lean_inc(x_553);
x_557 = l_Lean_Meta_mkEq(x_553, x_552, x_525, x_526, x_527, x_528, x_556);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; lean_object* x_559; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
lean_dec_ref(x_557);
x_302 = x_551;
x_303 = x_555;
x_304 = x_558;
x_305 = x_553;
x_306 = x_552;
x_307 = x_525;
x_308 = x_526;
x_309 = x_527;
x_310 = x_528;
x_311 = x_559;
goto block_522;
}
else
{
uint8_t x_560; 
lean_dec(x_555);
lean_dec(x_553);
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_528);
lean_dec_ref(x_527);
lean_dec(x_526);
lean_dec_ref(x_525);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_560 = !lean_is_exclusive(x_557);
if (x_560 == 0)
{
return x_557;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_561 = lean_ctor_get(x_557, 0);
x_562 = lean_ctor_get(x_557, 1);
lean_inc(x_562);
lean_inc(x_561);
lean_dec(x_557);
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_561);
lean_ctor_set(x_563, 1, x_562);
return x_563;
}
}
}
else
{
uint8_t x_564; 
lean_dec(x_553);
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_528);
lean_dec_ref(x_527);
lean_dec(x_526);
lean_dec_ref(x_525);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_564 = !lean_is_exclusive(x_554);
if (x_564 == 0)
{
return x_554;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_565 = lean_ctor_get(x_554, 0);
x_566 = lean_ctor_get(x_554, 1);
lean_inc(x_566);
lean_inc(x_565);
lean_dec(x_554);
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_566);
return x_567;
}
}
}
}
}
else
{
uint8_t x_568; 
lean_dec(x_528);
lean_dec_ref(x_527);
lean_dec(x_526);
lean_dec_ref(x_525);
lean_dec_ref(x_524);
lean_dec_ref(x_523);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_568 = !lean_is_exclusive(x_530);
if (x_568 == 0)
{
return x_530;
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_569 = lean_ctor_get(x_530, 0);
x_570 = lean_ctor_get(x_530, 1);
lean_inc(x_570);
lean_inc(x_569);
lean_dec(x_530);
x_571 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_571, 0, x_569);
lean_ctor_set(x_571, 1, x_570);
return x_571;
}
}
}
}
else
{
uint8_t x_589; 
lean_dec(x_74);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_589 = !lean_is_exclusive(x_77);
if (x_589 == 0)
{
return x_77;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_77, 0);
x_591 = lean_ctor_get(x_77, 1);
lean_inc(x_591);
lean_inc(x_590);
lean_dec(x_77);
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
return x_592;
}
}
}
else
{
uint8_t x_593; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_593 = !lean_is_exclusive(x_68);
if (x_593 == 0)
{
return x_68;
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_594 = lean_ctor_get(x_68, 0);
x_595 = lean_ctor_get(x_68, 1);
lean_inc(x_595);
lean_inc(x_594);
lean_dec(x_68);
x_596 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_596, 0, x_594);
lean_ctor_set(x_596, 1, x_595);
return x_596;
}
}
}
else
{
uint8_t x_597; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_597 = !lean_is_exclusive(x_66);
if (x_597 == 0)
{
return x_66;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_598 = lean_ctor_get(x_66, 0);
x_599 = lean_ctor_get(x_66, 1);
lean_inc(x_599);
lean_inc(x_598);
lean_dec(x_66);
x_600 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_600, 0, x_598);
lean_ctor_set(x_600, 1, x_599);
return x_600;
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
x_28 = l_Lean_indentExpr(x_15);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at___Lean_MVarId_rewrite_spec__5___redArg(x_29, x_14, x_16, x_18, x_13, x_12);
lean_dec(x_13);
lean_dec_ref(x_18);
lean_dec(x_16);
lean_dec_ref(x_14);
return x_30;
}
block_41:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = l_Array_append___redArg(x_32, x_36);
lean_dec_ref(x_36);
x_38 = lean_array_to_list(x_37);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
block_65:
{
lean_object* x_52; 
x_52 = l_Lean_Meta_getMVarsNoDelayed(x_3, x_42, x_45, x_49, x_47, x_51);
lean_dec(x_47);
lean_dec_ref(x_49);
lean_dec(x_45);
lean_dec_ref(x_42);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_array_get_size(x_53);
x_56 = lean_mk_empty_array_with_capacity(x_46);
x_57 = lean_nat_dec_lt(x_46, x_55);
if (x_57 == 0)
{
lean_dec(x_55);
lean_dec(x_53);
x_32 = x_50;
x_33 = x_43;
x_34 = x_44;
x_35 = x_54;
x_36 = x_56;
goto block_41;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_55, x_55);
if (x_58 == 0)
{
lean_dec(x_55);
lean_dec(x_53);
x_32 = x_50;
x_33 = x_43;
x_34 = x_44;
x_35 = x_54;
x_36 = x_56;
goto block_41;
}
else
{
size_t x_59; lean_object* x_60; 
x_59 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_60 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__10(x_50, x_53, x_48, x_59, x_56);
lean_dec(x_53);
x_32 = x_50;
x_33 = x_43;
x_34 = x_44;
x_35 = x_54;
x_36 = x_60;
goto block_41;
}
}
}
else
{
uint8_t x_61; 
lean_dec_ref(x_50);
lean_dec_ref(x_44);
lean_dec_ref(x_43);
x_61 = !lean_is_exclusive(x_52);
if (x_61 == 0)
{
return x_52;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_52, 0);
x_63 = lean_ctor_get(x_52, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_52);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
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
l_Lean_MVarId_rewrite___closed__0 = _init_l_Lean_MVarId_rewrite___closed__0();
lean_mark_persistent(l_Lean_MVarId_rewrite___closed__0);
l_Lean_MVarId_rewrite___closed__1 = _init_l_Lean_MVarId_rewrite___closed__1();
lean_mark_persistent(l_Lean_MVarId_rewrite___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
