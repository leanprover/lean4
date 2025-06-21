// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Util
// Imports: Init.Grind.Ring.Basic Lean.Meta.SynthInstance Lean.Meta.Basic Std.Internal.Rat
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
static lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__3;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstAddNat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__10;
lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__12;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isNatType___closed__1;
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isSupportedType(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__4;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isRelevantPred(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__17;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__9;
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__9;
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__7;
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__6;
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__15;
static lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isSupportedType___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20;
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__11;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatType(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstLENat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__12;
static lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__0;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__8;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__18;
static lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__0;
lean_object* l_Lean_aquote(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__0;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__13;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__5;
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8;
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_isIntType___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__6;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__15;
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isInstLENat___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatType___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize_go___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_gcdExt___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize_go(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__11;
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_shrink(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntType___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__1;
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__16;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstLENat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isArithTerm(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0;
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__13;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__7;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0(lean_object*, uint64_t, lean_object*);
lean_object* l_Lean_LOption_toOption___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isIntType___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__4;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__4;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(uint64_t, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__9;
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__0;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7;
static lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__0;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__7;
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__19;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__3;
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_Arith_isNatType___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_resize_go___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_shrink___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatAdd(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9;
static lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__13;
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isInstLENat___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__16;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__10;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__14;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_pop___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__14;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__12;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__8;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__1;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__2;
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg___boxed(lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_isNatType___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatType(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isNatType___closed__1;
x_3 = l_Lean_Expr_isConstOf(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isNatType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isIntType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isIntType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_isIntType___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntType(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isIntType___closed__1;
x_3 = l_Lean_Expr_isConstOf(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isIntType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isInstAddNat___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instHAdd", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_isInstAddNat___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instAddNat", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstAddNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_9 = l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1;
x_10 = l_Lean_Expr_isConstOf(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l_Lean_Meta_Grind_Arith_isNatType(x_7);
lean_dec(x_7);
if (x_11 == 0)
{
lean_dec(x_4);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3;
x_13 = l_Lean_Expr_isConstOf(x_4, x_12);
lean_dec(x_4);
return x_13;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isInstAddNat(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isInstLENat___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instLENat", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isInstLENat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_isInstLENat___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstLENat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isInstLENat___closed__1;
x_3 = l_Lean_Expr_isConstOf(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstLENat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isInstLENat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_11 = l_Lean_Expr_isApp(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_10);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_5);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_5);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_5);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2;
x_25 = l_Lean_Expr_isConstOf(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_5);
x_26 = lean_box(0);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = l_Lean_Meta_Grind_Arith_isInstAddNat(x_13);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_5);
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_29, 1, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
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
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatAdd(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_5 = l_Lean_Expr_isApp(x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_4);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_10 = l_Lean_Expr_isApp(x_9);
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Expr_appFnCleanup___redArg(x_9);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_14 = l_Lean_Expr_isApp(x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Lean_Expr_appFnCleanup___redArg(x_13);
x_16 = l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2;
x_17 = l_Lean_Expr_isConstOf(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_dec(x_8);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = l_Lean_Meta_Grind_Arith_isInstAddNat(x_8);
return x_18;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isNatAdd(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instOfNatNat", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_10 = l_Lean_Expr_isApp(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_5);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Expr_appFnCleanup___redArg(x_9);
x_13 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__2;
x_14 = l_Lean_Expr_isConstOf(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_cleanupAnnotations(x_5);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_21 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__4;
x_22 = l_Lean_Expr_isConstOf(x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
x_23 = lean_box(0);
return x_23;
}
else
{
if (lean_obj_tag(x_19) == 9)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_ctor_set_tag(x_24, 1);
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_24);
x_28 = lean_box(0);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_19);
x_29 = lean_box(0);
return x_29;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isSupportedType(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Meta_Grind_Arith_isNatType(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Meta_Grind_Arith_isIntType(x_1);
return x_3;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isSupportedType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isSupportedType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5;
x_2 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8;
x_2 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isRelevantPred(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1;
x_7 = l_Lean_Expr_isConstOf(x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = l_Lean_Expr_isApp(x_5);
if (x_8 == 0)
{
lean_dec(x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_10 = l_Lean_Expr_isApp(x_9);
if (x_10 == 0)
{
lean_dec(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = l_Lean_Expr_appFnCleanup___redArg(x_9);
x_13 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3;
x_14 = l_Lean_Expr_isConstOf(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
x_15 = l_Lean_Expr_isApp(x_12);
if (x_15 == 0)
{
lean_dec(x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_12);
x_18 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6;
x_19 = l_Lean_Expr_isConstOf(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9;
x_21 = l_Lean_Expr_isConstOf(x_17, x_20);
lean_dec(x_17);
if (x_21 == 0)
{
lean_dec(x_16);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = l_Lean_Meta_Grind_Arith_isSupportedType(x_16);
lean_dec(x_16);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_17);
x_23 = l_Lean_Meta_Grind_Arith_isSupportedType(x_16);
lean_dec(x_16);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_12);
x_24 = l_Lean_Meta_Grind_Arith_isSupportedType(x_11);
lean_dec(x_11);
return x_24;
}
}
}
}
else
{
lean_dec(x_5);
x_1 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isRelevantPred(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HPow", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hPow", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__3;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__7;
x_2 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__6;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__10;
x_2 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__9;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__13;
x_2 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__12;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__16;
x_2 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__15;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isArithTerm(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_5 = l_Lean_Expr_isApp(x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_4);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_9 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__2;
x_10 = l_Lean_Expr_isConstOf(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__2;
x_12 = l_Lean_Expr_isConstOf(x_8, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isApp(x_8);
if (x_13 == 0)
{
lean_dec(x_8);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_8);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec(x_14);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_19 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__5;
x_20 = l_Lean_Expr_isConstOf(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__8;
x_22 = l_Lean_Expr_isConstOf(x_18, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__11;
x_24 = l_Lean_Expr_isConstOf(x_18, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__14;
x_26 = l_Lean_Expr_isConstOf(x_18, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__17;
x_28 = l_Lean_Expr_isConstOf(x_18, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2;
x_30 = l_Lean_Expr_isConstOf(x_18, x_29);
lean_dec(x_18);
return x_30;
}
else
{
lean_dec(x_18);
return x_28;
}
}
else
{
lean_dec(x_18);
return x_26;
}
}
else
{
lean_dec(x_18);
return x_24;
}
}
else
{
lean_dec(x_18);
return x_22;
}
}
else
{
lean_dec(x_18);
return x_20;
}
}
}
}
}
else
{
lean_dec(x_8);
return x_12;
}
}
else
{
lean_dec(x_8);
return x_10;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isArithTerm(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc(x_1);
x_2 = l_Lean_Meta_Grind_Arith_isArithTerm(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_ofExpr(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_MessageData_ofExpr(x_1);
x_5 = l_Lean_aquote(x_4);
return x_5;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_gcdExt___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Meta_Grind_Arith_gcdExt___closed__0;
x_4 = lean_int_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_int_emod(x_1, x_2);
x_6 = l_Lean_Meta_Grind_Arith_gcdExt(x_2, x_5);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_int_ediv(x_1, x_2);
x_13 = lean_int_mul(x_12, x_11);
lean_dec(x_12);
x_14 = lean_int_sub(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_11);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_int_ediv(x_1, x_2);
x_18 = lean_int_mul(x_17, x_16);
lean_dec(x_17);
x_19 = lean_int_sub(x_15, x_18);
lean_dec(x_18);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_6, 1, x_20);
return x_6;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
x_26 = lean_int_ediv(x_1, x_2);
x_27 = lean_int_mul(x_26, x_24);
lean_dec(x_26);
x_28 = lean_int_sub(x_23, x_27);
lean_dec(x_27);
lean_dec(x_23);
if (lean_is_scalar(x_25)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_25;
}
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_37; 
x_31 = lean_nat_abs(x_1);
x_32 = lean_nat_to_int(x_31);
x_37 = lean_int_dec_eq(x_1, x_3);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_int_ediv(x_1, x_32);
x_33 = x_38;
goto block_36;
}
else
{
x_33 = x_3;
goto block_36;
}
block_36:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_gcdExt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_shrink(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
return x_1;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_pop___redArg(x_1);
x_1 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_shrink___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_shrink(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_resize_go___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Meta_Grind_Arith_gcdExt___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = lean_nat_dec_lt(x_3, x_1);
lean_dec(x_3);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_Grind_Arith_resize_go___closed__0;
x_6 = l_Lean_PersistentArray_push___redArg(x_2, x_5);
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_resize_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_resize_go(x_2, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Arith_shrink(x_1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_resize(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(lean_object* x_1) {
_start:
{
size_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ptr_addr(x_1);
x_3 = lean_usize_to_uint64(x_2);
x_4 = 2;
x_5 = lean_uint64_shift_right(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; 
x_3 = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_8 = lean_uint64_dec_eq(x_7, x_1);
if (x_8 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_6);
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = 32;
x_8 = lean_unbox_uint64(x_4);
x_9 = lean_uint64_shift_right(x_8, x_7);
x_10 = lean_unbox_uint64(x_4);
x_11 = lean_uint64_xor(x_10, x_9);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_1, x_19);
lean_ctor_set(x_2, 2, x_20);
x_21 = lean_array_uset(x_1, x_19, x_2);
x_1 = x_21;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_26 = lean_array_get_size(x_1);
x_27 = 32;
x_28 = lean_unbox_uint64(x_23);
x_29 = lean_uint64_shift_right(x_28, x_27);
x_30 = lean_unbox_uint64(x_23);
x_31 = lean_uint64_xor(x_30, x_29);
x_32 = 16;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_37 = 1;
x_38 = lean_usize_sub(x_36, x_37);
x_39 = lean_usize_land(x_35, x_38);
x_40 = lean_array_uget(x_1, x_39);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_24);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_array_uset(x_1, x_39, x_41);
x_1 = x_42;
x_2 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__1_spec__1___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(x_1);
x_8 = lean_array_get_size(x_6);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_7, x_9);
x_11 = lean_uint64_xor(x_7, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
lean_inc(x_20);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(x_7, x_20);
if (x_21 == 0)
{
lean_dec(x_2);
if (x_21 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_3);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_28 = lean_ctor_get(x_3, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_3, 0);
lean_dec(x_29);
x_30 = lean_box(0);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_5, x_31);
lean_dec(x_5);
x_33 = lean_box_uint64(x_7);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_20);
x_35 = lean_array_uset(x_6, x_19, x_34);
x_36 = lean_unsigned_to_nat(4u);
x_37 = lean_nat_mul(x_32, x_36);
x_38 = lean_unsigned_to_nat(3u);
x_39 = lean_nat_div(x_37, x_38);
lean_dec(x_37);
x_40 = lean_array_get_size(x_35);
x_41 = lean_nat_dec_le(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(x_35);
lean_ctor_set(x_3, 1, x_42);
lean_ctor_set(x_3, 0, x_32);
x_22 = x_3;
goto block_26;
}
else
{
lean_ctor_set(x_3, 1, x_35);
lean_ctor_set(x_3, 0, x_32);
x_22 = x_3;
goto block_26;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_3);
x_43 = lean_box(0);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_5, x_44);
lean_dec(x_5);
x_46 = lean_box_uint64(x_7);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_20);
x_48 = lean_array_uset(x_6, x_19, x_47);
x_49 = lean_unsigned_to_nat(4u);
x_50 = lean_nat_mul(x_45, x_49);
x_51 = lean_unsigned_to_nat(3u);
x_52 = lean_nat_div(x_50, x_51);
lean_dec(x_50);
x_53 = lean_array_get_size(x_48);
x_54 = lean_nat_dec_le(x_52, x_53);
lean_dec(x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(x_48);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_55);
x_22 = x_56;
goto block_26;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_48);
x_22 = x_57;
goto block_26;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
x_22 = x_3;
goto block_26;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = lean_box(x_21);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_2);
return x_59;
}
block_26:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
x_24 = lean_box(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(x_3, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0(x_1, x_4, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_box(0);
x_6 = l_Lean_FVarIdSet_insert(x_4, x_1);
lean_ctor_set(x_2, 1, x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = l_Lean_FVarIdSet_insert(x_9, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__5;
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(1);
x_2 = lean_unbox(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__0;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__1;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__3;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__6;
x_2 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__5;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8;
x_2 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__7;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Arith", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10;
x_2 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__9;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Util", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__12;
x_2 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__11;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__13;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__14;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__15;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8;
x_2 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__16;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10;
x_2 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__17;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("____intModuleMarker____", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__19;
x_2 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__18;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
x_6 = lean_expr_eqv(x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IsCharP", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0;
x_2 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8;
x_3 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_8);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1, x_2, x_3, x_8, x_9, x_10, x_11, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1;
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 0, x_4);
x_18 = l_Lean_Expr_const___override(x_17, x_13);
lean_inc(x_15);
x_19 = l_Lean_mkApp3(x_18, x_6, x_7, x_15);
x_20 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_21 = l_Lean_Meta_trySynthInstance(x_19, x_20, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_15, x_9, x_23);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = l_Lean_Meta_evalNat(x_27, x_8, x_9, x_10, x_11, x_28);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_free_object(x_25);
lean_dec(x_24);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_29, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_30, 0);
lean_ctor_set(x_25, 1, x_40);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_30, 0, x_25);
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
lean_dec(x_30);
lean_ctor_set(x_25, 1, x_41);
lean_ctor_set(x_25, 0, x_24);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_25);
lean_ctor_set(x_29, 0, x_42);
return x_29;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_dec(x_29);
x_44 = lean_ctor_get(x_30, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_45 = x_30;
} else {
 lean_dec_ref(x_30);
 x_45 = lean_box(0);
}
lean_ctor_set(x_25, 1, x_44);
lean_ctor_set(x_25, 0, x_24);
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_25);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_25, 0);
x_49 = lean_ctor_get(x_25, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_25);
x_50 = l_Lean_Meta_evalNat(x_48, x_8, x_9, x_10, x_11, x_49);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_24);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_59 = x_51;
} else {
 lean_dec_ref(x_51);
 x_59 = lean_box(0);
}
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_24);
lean_ctor_set(x_60, 1, x_58);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
if (lean_is_scalar(x_57)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_57;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_63 = !lean_is_exclusive(x_21);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_21, 0);
lean_dec(x_64);
x_65 = lean_box(0);
lean_ctor_set(x_21, 0, x_65);
return x_21;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_21, 1);
lean_inc(x_66);
lean_dec(x_21);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_69 = !lean_is_exclusive(x_21);
if (x_69 == 0)
{
return x_21;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_21, 0);
x_71 = lean_ctor_get(x_21, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_21);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_73 = lean_ctor_get(x_13, 0);
x_74 = lean_ctor_get(x_13, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_13);
x_75 = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1;
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_4);
lean_ctor_set(x_76, 1, x_5);
x_77 = l_Lean_Expr_const___override(x_75, x_76);
lean_inc(x_73);
x_78 = l_Lean_mkApp3(x_77, x_6, x_7, x_73);
x_79 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_80 = l_Lean_Meta_trySynthInstance(x_78, x_79, x_8, x_9, x_10, x_11, x_74);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 1)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_73, x_9, x_82);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
x_88 = l_Lean_Meta_evalNat(x_85, x_8, x_9, x_10, x_11, x_86);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_87);
lean_dec(x_83);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = lean_box(0);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_95 = x_88;
} else {
 lean_dec_ref(x_88);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_89, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_97 = x_89;
} else {
 lean_dec_ref(x_89);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_87;
}
lean_ctor_set(x_98, 0, x_83);
lean_ctor_set(x_98, 1, x_96);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
if (lean_is_scalar(x_95)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_95;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_94);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_81);
lean_dec(x_73);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_101 = lean_ctor_get(x_80, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_102 = x_80;
} else {
 lean_dec_ref(x_80);
 x_102 = lean_box(0);
}
x_103 = lean_box(0);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_73);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_105 = lean_ctor_get(x_80, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_80, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_107 = x_80;
} else {
 lean_dec_ref(x_80);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_isNatType___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_9 = lean_box(0);
x_10 = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1;
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___boxed), 12, 7);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_1);
lean_closure_set(x_13, 4, x_9);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_3);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_13, x_15, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Zero", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_isArithTerm___closed__12;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("NoNatZeroDivisors", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8;
x_3 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__1;
x_9 = lean_box(0);
lean_inc(x_1);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
lean_inc(x_10);
x_11 = l_Lean_Expr_const___override(x_8, x_10);
lean_inc(x_2);
x_12 = l_Lean_Expr_app___override(x_11, x_2);
x_13 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Meta_trySynthInstance(x_12, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__2;
x_19 = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__3;
lean_inc(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Expr_const___override(x_18, x_21);
x_23 = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0;
lean_inc_n(x_2, 2);
x_24 = l_Lean_mkApp3(x_22, x_23, x_2, x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l_Lean_Meta_trySynthInstance(x_24, x_13, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__5;
x_30 = l_Lean_Expr_const___override(x_29, x_10);
x_31 = l_Lean_mkApp3(x_30, x_2, x_17, x_28);
x_32 = l_Lean_Meta_trySynthInstance(x_31, x_13, x_3, x_4, x_5, x_6, x_27);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = l_Lean_LOption_toOption___redArg(x_34);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = l_Lean_LOption_toOption___redArg(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_25);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_25, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_25, 0, x_46);
return x_25;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
lean_dec(x_25);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_25);
if (x_50 == 0)
{
return x_25;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_25, 0);
x_52 = lean_ctor_get(x_25, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_25);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_14);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_14, 0);
lean_dec(x_55);
x_56 = lean_box(0);
lean_ctor_set(x_14, 0, x_56);
return x_14;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_14, 1);
lean_inc(x_57);
lean_dec(x_14);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_14);
if (x_60 == 0)
{
return x_14;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_14, 0);
x_62 = lean_ctor_get(x_14, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_14);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_3);
x_8 = lean_apply_1(x_1, x_3);
x_9 = lean_nat_to_int(x_2);
x_10 = lean_int_dec_eq(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_3);
x_12 = lean_array_push(x_7, x_11);
lean_ctor_set(x_4, 1, x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
x_14 = l_Lean_PersistentArray_push___redArg(x_6, x_3);
lean_ctor_set(x_4, 0, x_14);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
lean_inc(x_3);
x_18 = lean_apply_1(x_1, x_3);
x_19 = lean_nat_to_int(x_2);
x_20 = lean_int_dec_eq(x_18, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_3);
x_22 = lean_array_push(x_17, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_18);
x_25 = l_Lean_PersistentArray_push___redArg(x_16, x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_split___redArg___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_split___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Arith_split___redArg___closed__5;
x_2 = l_Lean_Meta_Grind_Arith_split___redArg___closed__4;
x_3 = l_Lean_Meta_Grind_Arith_split___redArg___closed__3;
x_4 = l_Lean_Meta_Grind_Arith_split___redArg___closed__2;
x_5 = l_Lean_Meta_Grind_Arith_split___redArg___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_split___redArg___closed__6;
x_2 = l_Lean_Meta_Grind_Arith_split___redArg___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_split___redArg___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__12() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_Arith_split___redArg___closed__10;
x_4 = l_Lean_Meta_Grind_Arith_split___redArg___closed__11;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_split___redArg___closed__13;
x_2 = l_Lean_Meta_Grind_Arith_split___redArg___closed__12;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = l_Lean_Meta_Grind_Arith_split___redArg___closed__9;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_split___redArg___lam__0), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_4);
x_6 = l_Lean_Meta_Grind_Arith_split___redArg___closed__14;
x_7 = l_Lean_PersistentArray_forIn___redArg(x_3, x_1, x_6, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_split___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Internal_Rat(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Rat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_isNatType___closed__0 = _init_l_Lean_Meta_Grind_Arith_isNatType___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatType___closed__0);
l_Lean_Meta_Grind_Arith_isNatType___closed__1 = _init_l_Lean_Meta_Grind_Arith_isNatType___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatType___closed__1);
l_Lean_Meta_Grind_Arith_isIntType___closed__0 = _init_l_Lean_Meta_Grind_Arith_isIntType___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isIntType___closed__0);
l_Lean_Meta_Grind_Arith_isIntType___closed__1 = _init_l_Lean_Meta_Grind_Arith_isIntType___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isIntType___closed__1);
l_Lean_Meta_Grind_Arith_isInstAddNat___closed__0 = _init_l_Lean_Meta_Grind_Arith_isInstAddNat___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__0);
l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1 = _init_l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1);
l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2 = _init_l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2);
l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3 = _init_l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3);
l_Lean_Meta_Grind_Arith_isInstLENat___closed__0 = _init_l_Lean_Meta_Grind_Arith_isInstLENat___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isInstLENat___closed__0);
l_Lean_Meta_Grind_Arith_isInstLENat___closed__1 = _init_l_Lean_Meta_Grind_Arith_isInstLENat___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isInstLENat___closed__1);
l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__0 = _init_l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__0);
l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1 = _init_l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1);
l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2 = _init_l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2);
l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__0 = _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__0);
l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__1 = _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__1);
l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__2 = _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__2);
l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__3 = _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__3);
l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__4 = _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__4);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__0 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__0);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__1 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__1);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__2 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__2);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__3 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__3);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__4 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__4);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__5 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__5);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__6 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__6);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__7 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__7);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__8 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__8);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__9 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__9);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__10 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__10);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__11 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__11);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__12 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__12);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__13 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__13);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__14 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__14);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__15 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__15();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__15);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__16 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__16();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__16);
l_Lean_Meta_Grind_Arith_isArithTerm___closed__17 = _init_l_Lean_Meta_Grind_Arith_isArithTerm___closed__17();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isArithTerm___closed__17);
l_Lean_Meta_Grind_Arith_gcdExt___closed__0 = _init_l_Lean_Meta_Grind_Arith_gcdExt___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_gcdExt___closed__0);
l_Lean_Meta_Grind_Arith_resize_go___closed__0 = _init_l_Lean_Meta_Grind_Arith_resize_go___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_resize_go___closed__0);
l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0 = _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0);
l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1 = _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1);
l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2 = _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2);
l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__3 = _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__3);
l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__4 = _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__4);
l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__5 = _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__5);
l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________ = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________();
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__0 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__0);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__1 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__1);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__3 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__3);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__5 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__5);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__6 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__6);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__7 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__7);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__9 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__9);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__11 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__11);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__12 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__12);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__13 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__13);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__14 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__14);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__15 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__15();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__15);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__16 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__16();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__16);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__17 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__17();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__17);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__18 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__18();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__18);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__19 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__19();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__19);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21 = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21);
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent);
l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0 = _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0);
l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1 = _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1);
l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0 = _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0);
l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1 = _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1);
l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__0 = _init_l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__0);
l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__1 = _init_l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__1);
l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__2 = _init_l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__2);
l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__3 = _init_l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__3);
l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__4 = _init_l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__4);
l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__5 = _init_l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___closed__5);
l_Lean_Meta_Grind_Arith_split___redArg___closed__0 = _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___redArg___closed__0);
l_Lean_Meta_Grind_Arith_split___redArg___closed__1 = _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___redArg___closed__1);
l_Lean_Meta_Grind_Arith_split___redArg___closed__2 = _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___redArg___closed__2);
l_Lean_Meta_Grind_Arith_split___redArg___closed__3 = _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___redArg___closed__3);
l_Lean_Meta_Grind_Arith_split___redArg___closed__4 = _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___redArg___closed__4);
l_Lean_Meta_Grind_Arith_split___redArg___closed__5 = _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___redArg___closed__5);
l_Lean_Meta_Grind_Arith_split___redArg___closed__6 = _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___redArg___closed__6);
l_Lean_Meta_Grind_Arith_split___redArg___closed__7 = _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___redArg___closed__7);
l_Lean_Meta_Grind_Arith_split___redArg___closed__8 = _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___redArg___closed__8);
l_Lean_Meta_Grind_Arith_split___redArg___closed__9 = _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___redArg___closed__9);
l_Lean_Meta_Grind_Arith_split___redArg___closed__10 = _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___redArg___closed__10);
l_Lean_Meta_Grind_Arith_split___redArg___closed__11 = _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___redArg___closed__11);
l_Lean_Meta_Grind_Arith_split___redArg___closed__12 = _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___redArg___closed__12);
l_Lean_Meta_Grind_Arith_split___redArg___closed__13 = _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___redArg___closed__13);
l_Lean_Meta_Grind_Arith_split___redArg___closed__14 = _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___redArg___closed__14);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
