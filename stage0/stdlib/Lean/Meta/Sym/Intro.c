// Lean compiler output
// Module: Lean.Meta.Sym.Intro
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.Tactic.Intro import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.IsClass import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InstantiateMVarsS
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Sym_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t l_Lean_LocalDeclKind_ofBinderName(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateAssignedMVarHeadS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setType___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkAppBVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__10___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1_value;
static const lean_array_object l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__10(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(lean_object* v_max_1_, lean_object* v_i_2_, lean_object* v_type_3_, lean_object* v_body_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_nat_dec_le(v_max_1_, v_i_2_);
if (v___x_5_ == 0)
{
switch(lean_obj_tag(v_type_3_))
{
case 10:
{
lean_object* v_expr_6_; 
v_expr_6_ = lean_ctor_get(v_type_3_, 1);
lean_inc_ref(v_expr_6_);
lean_dec_ref_known(v_type_3_, 2);
v_type_3_ = v_expr_6_;
goto _start;
}
case 7:
{
lean_object* v_binderName_8_; lean_object* v_binderType_9_; lean_object* v_body_10_; uint8_t v_binderInfo_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_binderName_8_ = lean_ctor_get(v_type_3_, 0);
lean_inc(v_binderName_8_);
v_binderType_9_ = lean_ctor_get(v_type_3_, 1);
lean_inc_ref(v_binderType_9_);
v_body_10_ = lean_ctor_get(v_type_3_, 2);
lean_inc_ref(v_body_10_);
v_binderInfo_11_ = lean_ctor_get_uint8(v_type_3_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_3_, 3);
v___x_12_ = lean_unsigned_to_nat(1u);
v___x_13_ = lean_nat_add(v_i_2_, v___x_12_);
v___x_14_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(v_max_1_, v___x_13_, v_body_10_, v_body_4_);
lean_dec(v___x_13_);
v___x_15_ = l_Lean_mkLambda(v_binderName_8_, v_binderInfo_11_, v_binderType_9_, v___x_14_);
return v___x_15_;
}
case 8:
{
lean_object* v_declName_16_; lean_object* v_type_17_; lean_object* v_value_18_; lean_object* v_body_19_; uint8_t v_nondep_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_declName_16_ = lean_ctor_get(v_type_3_, 0);
lean_inc(v_declName_16_);
v_type_17_ = lean_ctor_get(v_type_3_, 1);
lean_inc_ref(v_type_17_);
v_value_18_ = lean_ctor_get(v_type_3_, 2);
lean_inc_ref(v_value_18_);
v_body_19_ = lean_ctor_get(v_type_3_, 3);
lean_inc_ref(v_body_19_);
v_nondep_20_ = lean_ctor_get_uint8(v_type_3_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_type_3_, 4);
v___x_21_ = lean_unsigned_to_nat(1u);
v___x_22_ = lean_nat_add(v_i_2_, v___x_21_);
v___x_23_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(v_max_1_, v___x_22_, v_body_19_, v_body_4_);
lean_dec(v___x_22_);
v___x_24_ = l_Lean_Expr_letE___override(v_declName_16_, v_type_17_, v_value_18_, v___x_23_, v_nondep_20_);
return v___x_24_;
}
default: 
{
lean_dec_ref(v_type_3_);
lean_inc_ref(v_body_4_);
return v_body_4_;
}
}
}
else
{
lean_dec_ref(v_type_3_);
lean_inc_ref(v_body_4_);
return v_body_4_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop___boxed(lean_object* v_max_25_, lean_object* v_i_26_, lean_object* v_type_27_, lean_object* v_body_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(v_max_25_, v_i_26_, v_type_27_, v_body_28_);
lean_dec_ref(v_body_28_);
lean_dec(v_i_26_);
lean_dec(v_max_25_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkAppBVars(lean_object* v_e_30_, lean_object* v_n_31_){
_start:
{
lean_object* v_zero_32_; uint8_t v_isZero_33_; 
v_zero_32_ = lean_unsigned_to_nat(0u);
v_isZero_33_ = lean_nat_dec_eq(v_n_31_, v_zero_32_);
if (v_isZero_33_ == 1)
{
lean_dec(v_n_31_);
return v_e_30_;
}
else
{
lean_object* v_one_34_; lean_object* v_n_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_one_34_ = lean_unsigned_to_nat(1u);
v_n_35_ = lean_nat_sub(v_n_31_, v_one_34_);
lean_dec(v_n_31_);
lean_inc(v_n_35_);
v___x_36_ = l_Lean_mkBVar(v_n_35_);
v___x_37_ = l_Lean_Expr_app___override(v_e_30_, v___x_36_);
v_e_30_ = v___x_37_;
v_n_31_ = v_n_35_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__2___redArg(lean_object* v_fvarId_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = l_Lean_Expr_fvar___override(v_fvarId_39_);
v___x_43_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_42_, v___y_40_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__2___redArg___boxed(lean_object* v_fvarId_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__2___redArg(v_fvarId_44_, v___y_45_);
lean_dec(v___y_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__2(lean_object* v_fvarId_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__2___redArg(v_fvarId_48_, v___y_50_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__2___boxed(lean_object* v_fvarId_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__2(v_fvarId_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__6(size_t v_sz_66_, size_t v_i_67_, lean_object* v_bs_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = lean_usize_dec_lt(v_i_67_, v_sz_66_);
if (v___x_69_ == 0)
{
return v_bs_68_;
}
else
{
lean_object* v_v_70_; lean_object* v___x_71_; lean_object* v_bs_x27_72_; lean_object* v___x_73_; size_t v___x_74_; size_t v___x_75_; lean_object* v___x_76_; 
v_v_70_ = lean_array_uget(v_bs_68_, v_i_67_);
v___x_71_ = lean_unsigned_to_nat(0u);
v_bs_x27_72_ = lean_array_uset(v_bs_68_, v_i_67_, v___x_71_);
v___x_73_ = l_Lean_Expr_fvarId_x21(v_v_70_);
lean_dec(v_v_70_);
v___x_74_ = ((size_t)1ULL);
v___x_75_ = lean_usize_add(v_i_67_, v___x_74_);
v___x_76_ = lean_array_uset(v_bs_x27_72_, v_i_67_, v___x_73_);
v_i_67_ = v___x_75_;
v_bs_68_ = v___x_76_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__6___boxed(lean_object* v_sz_78_, lean_object* v_i_79_, lean_object* v_bs_80_){
_start:
{
size_t v_sz_boxed_81_; size_t v_i_boxed_82_; lean_object* v_res_83_; 
v_sz_boxed_81_ = lean_unbox_usize(v_sz_78_);
lean_dec(v_sz_78_);
v_i_boxed_82_ = lean_unbox_usize(v_i_79_);
lean_dec(v_i_79_);
v_res_83_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__6(v_sz_boxed_81_, v_i_boxed_82_, v_bs_80_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__9_spec__10___redArg(lean_object* v_x_84_, lean_object* v_x_85_, lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
lean_object* v_ks_88_; lean_object* v_vs_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_113_; 
v_ks_88_ = lean_ctor_get(v_x_84_, 0);
v_vs_89_ = lean_ctor_get(v_x_84_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_x_84_);
if (v_isSharedCheck_113_ == 0)
{
v___x_91_ = v_x_84_;
v_isShared_92_ = v_isSharedCheck_113_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_vs_89_);
lean_inc(v_ks_88_);
lean_dec(v_x_84_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_113_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = lean_array_get_size(v_ks_88_);
v___x_94_ = lean_nat_dec_lt(v_x_85_, v___x_93_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
lean_dec(v_x_85_);
v___x_95_ = lean_array_push(v_ks_88_, v_x_86_);
v___x_96_ = lean_array_push(v_vs_89_, v_x_87_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v___x_96_);
lean_ctor_set(v___x_91_, 0, v___x_95_);
v___x_98_ = v___x_91_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_95_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
else
{
lean_object* v_k_x27_100_; uint8_t v___x_101_; 
v_k_x27_100_ = lean_array_fget_borrowed(v_ks_88_, v_x_85_);
v___x_101_ = l_Lean_instBEqMVarId_beq(v_x_86_, v_k_x27_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_103_; 
if (v_isShared_92_ == 0)
{
v___x_103_ = v___x_91_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_ks_88_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_vs_89_);
v___x_103_ = v_reuseFailAlloc_107_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(1u);
v___x_105_ = lean_nat_add(v_x_85_, v___x_104_);
lean_dec(v_x_85_);
v_x_84_ = v___x_103_;
v_x_85_ = v___x_105_;
goto _start;
}
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_108_ = lean_array_fset(v_ks_88_, v_x_85_, v_x_86_);
v___x_109_ = lean_array_fset(v_vs_89_, v_x_85_, v_x_87_);
lean_dec(v_x_85_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v___x_109_);
lean_ctor_set(v___x_91_, 0, v___x_108_);
v___x_111_ = v___x_91_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__9___redArg(lean_object* v_n_114_, lean_object* v_k_115_, lean_object* v_v_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__9_spec__10___redArg(v_n_114_, v___x_117_, v_k_115_, v_v_116_);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg(lean_object* v_x_120_, size_t v_x_121_, size_t v_x_122_, lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
if (lean_obj_tag(v_x_120_) == 0)
{
lean_object* v_es_125_; size_t v___x_126_; size_t v___x_127_; lean_object* v_j_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v_es_125_ = lean_ctor_get(v_x_120_, 0);
v___x_126_ = ((size_t)31ULL);
v___x_127_ = lean_usize_land(v_x_121_, v___x_126_);
v_j_128_ = lean_usize_to_nat(v___x_127_);
v___x_129_ = lean_array_get_size(v_es_125_);
v___x_130_ = lean_nat_dec_lt(v_j_128_, v___x_129_);
if (v___x_130_ == 0)
{
lean_dec(v_j_128_);
lean_dec(v_x_124_);
lean_dec(v_x_123_);
return v_x_120_;
}
else
{
lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_169_; 
lean_inc_ref(v_es_125_);
v_isSharedCheck_169_ = !lean_is_exclusive(v_x_120_);
if (v_isSharedCheck_169_ == 0)
{
lean_object* v_unused_170_; 
v_unused_170_ = lean_ctor_get(v_x_120_, 0);
lean_dec(v_unused_170_);
v___x_132_ = v_x_120_;
v_isShared_133_ = v_isSharedCheck_169_;
goto v_resetjp_131_;
}
else
{
lean_dec(v_x_120_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_169_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v_v_134_; lean_object* v___x_135_; lean_object* v_xs_x27_136_; lean_object* v___y_138_; 
v_v_134_ = lean_array_fget(v_es_125_, v_j_128_);
v___x_135_ = lean_box(0);
v_xs_x27_136_ = lean_array_fset(v_es_125_, v_j_128_, v___x_135_);
switch(lean_obj_tag(v_v_134_))
{
case 0:
{
lean_object* v_key_143_; lean_object* v_val_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_154_; 
v_key_143_ = lean_ctor_get(v_v_134_, 0);
v_val_144_ = lean_ctor_get(v_v_134_, 1);
v_isSharedCheck_154_ = !lean_is_exclusive(v_v_134_);
if (v_isSharedCheck_154_ == 0)
{
v___x_146_ = v_v_134_;
v_isShared_147_ = v_isSharedCheck_154_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_val_144_);
lean_inc(v_key_143_);
lean_dec(v_v_134_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_154_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
uint8_t v___x_148_; 
v___x_148_ = l_Lean_instBEqMVarId_beq(v_x_123_, v_key_143_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_del_object(v___x_146_);
v___x_149_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_143_, v_val_144_, v_x_123_, v_x_124_);
v___x_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
v___y_138_ = v___x_150_;
goto v___jp_137_;
}
else
{
lean_object* v___x_152_; 
lean_dec(v_val_144_);
lean_dec(v_key_143_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v_x_124_);
lean_ctor_set(v___x_146_, 0, v_x_123_);
v___x_152_ = v___x_146_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_x_123_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_x_124_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
v___y_138_ = v___x_152_;
goto v___jp_137_;
}
}
}
}
case 1:
{
lean_object* v_node_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_167_; 
v_node_155_ = lean_ctor_get(v_v_134_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v_v_134_);
if (v_isSharedCheck_167_ == 0)
{
v___x_157_ = v_v_134_;
v_isShared_158_ = v_isSharedCheck_167_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_node_155_);
lean_dec(v_v_134_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_167_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
size_t v___x_159_; size_t v___x_160_; size_t v___x_161_; size_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_159_ = ((size_t)5ULL);
v___x_160_ = lean_usize_shift_right(v_x_121_, v___x_159_);
v___x_161_ = ((size_t)1ULL);
v___x_162_ = lean_usize_add(v_x_122_, v___x_161_);
v___x_163_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg(v_node_155_, v___x_160_, v___x_162_, v_x_123_, v_x_124_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_163_);
v___x_165_ = v___x_157_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
v___y_138_ = v___x_165_;
goto v___jp_137_;
}
}
}
default: 
{
lean_object* v___x_168_; 
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v_x_123_);
lean_ctor_set(v___x_168_, 1, v_x_124_);
v___y_138_ = v___x_168_;
goto v___jp_137_;
}
}
v___jp_137_:
{
lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_139_ = lean_array_fset(v_xs_x27_136_, v_j_128_, v___y_138_);
lean_dec(v_j_128_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_139_);
v___x_141_ = v___x_132_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
else
{
lean_object* v_ks_171_; lean_object* v_vs_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_190_; 
v_ks_171_ = lean_ctor_get(v_x_120_, 0);
v_vs_172_ = lean_ctor_get(v_x_120_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v_x_120_);
if (v_isSharedCheck_190_ == 0)
{
v___x_174_ = v_x_120_;
v_isShared_175_ = v_isSharedCheck_190_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_vs_172_);
lean_inc(v_ks_171_);
lean_dec(v_x_120_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_190_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_ks_171_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_vs_172_);
v___x_177_ = v_reuseFailAlloc_189_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v_newNode_178_; size_t v___x_179_; uint8_t v___x_180_; 
v_newNode_178_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__9___redArg(v___x_177_, v_x_123_, v_x_124_);
v___x_179_ = ((size_t)7ULL);
v___x_180_ = lean_usize_dec_le(v___x_179_, v_x_122_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_181_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_178_);
v___x_182_ = lean_unsigned_to_nat(4u);
v___x_183_ = lean_nat_dec_lt(v___x_181_, v___x_182_);
lean_dec(v___x_181_);
if (v___x_183_ == 0)
{
lean_object* v_ks_184_; lean_object* v_vs_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_ks_184_ = lean_ctor_get(v_newNode_178_, 0);
lean_inc_ref(v_ks_184_);
v_vs_185_ = lean_ctor_get(v_newNode_178_, 1);
lean_inc_ref(v_vs_185_);
lean_dec_ref(v_newNode_178_);
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_188_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__10___redArg(v_x_122_, v_ks_184_, v_vs_185_, v___x_186_, v___x_187_);
lean_dec_ref(v_vs_185_);
lean_dec_ref(v_ks_184_);
return v___x_188_;
}
else
{
return v_newNode_178_;
}
}
else
{
return v_newNode_178_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__10___redArg(size_t v_depth_191_, lean_object* v_keys_192_, lean_object* v_vals_193_, lean_object* v_i_194_, lean_object* v_entries_195_){
_start:
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_array_get_size(v_keys_192_);
v___x_197_ = lean_nat_dec_lt(v_i_194_, v___x_196_);
if (v___x_197_ == 0)
{
lean_dec(v_i_194_);
return v_entries_195_;
}
else
{
lean_object* v_k_198_; lean_object* v_v_199_; uint64_t v___x_200_; size_t v_h_201_; size_t v___x_202_; lean_object* v___x_203_; size_t v___x_204_; size_t v___x_205_; size_t v___x_206_; size_t v_h_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_k_198_ = lean_array_fget_borrowed(v_keys_192_, v_i_194_);
v_v_199_ = lean_array_fget_borrowed(v_vals_193_, v_i_194_);
v___x_200_ = l_Lean_instHashableMVarId_hash(v_k_198_);
v_h_201_ = lean_uint64_to_usize(v___x_200_);
v___x_202_ = ((size_t)5ULL);
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = ((size_t)1ULL);
v___x_205_ = lean_usize_sub(v_depth_191_, v___x_204_);
v___x_206_ = lean_usize_mul(v___x_202_, v___x_205_);
v_h_207_ = lean_usize_shift_right(v_h_201_, v___x_206_);
v___x_208_ = lean_nat_add(v_i_194_, v___x_203_);
lean_dec(v_i_194_);
lean_inc(v_v_199_);
lean_inc(v_k_198_);
v___x_209_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg(v_entries_195_, v_h_207_, v_depth_191_, v_k_198_, v_v_199_);
v_i_194_ = v___x_208_;
v_entries_195_ = v___x_209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__10___redArg___boxed(lean_object* v_depth_211_, lean_object* v_keys_212_, lean_object* v_vals_213_, lean_object* v_i_214_, lean_object* v_entries_215_){
_start:
{
size_t v_depth_boxed_216_; lean_object* v_res_217_; 
v_depth_boxed_216_ = lean_unbox_usize(v_depth_211_);
lean_dec(v_depth_211_);
v_res_217_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__10___redArg(v_depth_boxed_216_, v_keys_212_, v_vals_213_, v_i_214_, v_entries_215_);
lean_dec_ref(v_vals_213_);
lean_dec_ref(v_keys_212_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_x_218_, lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v_x_221_, lean_object* v_x_222_){
_start:
{
size_t v_x_13129__boxed_223_; size_t v_x_13130__boxed_224_; lean_object* v_res_225_; 
v_x_13129__boxed_223_ = lean_unbox_usize(v_x_219_);
lean_dec(v_x_219_);
v_x_13130__boxed_224_ = lean_unbox_usize(v_x_220_);
lean_dec(v_x_220_);
v_res_225_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg(v_x_218_, v_x_13129__boxed_223_, v_x_13130__boxed_224_, v_x_221_, v_x_222_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5___redArg(lean_object* v_x_226_, lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
uint64_t v___x_229_; size_t v___x_230_; size_t v___x_231_; lean_object* v___x_232_; 
v___x_229_ = l_Lean_instHashableMVarId_hash(v_x_227_);
v___x_230_ = lean_uint64_to_usize(v___x_229_);
v___x_231_ = ((size_t)1ULL);
v___x_232_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg(v_x_226_, v___x_230_, v___x_231_, v_x_227_, v_x_228_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4___redArg(lean_object* v_mvarId_233_, lean_object* v_fvars_234_, lean_object* v_mvarIdPending_235_, lean_object* v___y_236_){
_start:
{
lean_object* v___x_238_; lean_object* v_mctx_239_; lean_object* v_cache_240_; lean_object* v_zetaDeltaFVarIds_241_; lean_object* v_postponed_242_; lean_object* v_diag_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_273_; 
v___x_238_ = lean_st_ref_take(v___y_236_);
v_mctx_239_ = lean_ctor_get(v___x_238_, 0);
v_cache_240_ = lean_ctor_get(v___x_238_, 1);
v_zetaDeltaFVarIds_241_ = lean_ctor_get(v___x_238_, 2);
v_postponed_242_ = lean_ctor_get(v___x_238_, 3);
v_diag_243_ = lean_ctor_get(v___x_238_, 4);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_273_ == 0)
{
v___x_245_ = v___x_238_;
v_isShared_246_ = v_isSharedCheck_273_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_diag_243_);
lean_inc(v_postponed_242_);
lean_inc(v_zetaDeltaFVarIds_241_);
lean_inc(v_cache_240_);
lean_inc(v_mctx_239_);
lean_dec(v___x_238_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_273_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_depth_247_; lean_object* v_levelAssignDepth_248_; lean_object* v_lmvarCounter_249_; lean_object* v_mvarCounter_250_; lean_object* v_lDecls_251_; lean_object* v_decls_252_; lean_object* v_userNames_253_; lean_object* v_lAssignment_254_; lean_object* v_eAssignment_255_; lean_object* v_dAssignment_256_; lean_object* v_instanceTypedMVars_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_272_; 
v_depth_247_ = lean_ctor_get(v_mctx_239_, 0);
v_levelAssignDepth_248_ = lean_ctor_get(v_mctx_239_, 1);
v_lmvarCounter_249_ = lean_ctor_get(v_mctx_239_, 2);
v_mvarCounter_250_ = lean_ctor_get(v_mctx_239_, 3);
v_lDecls_251_ = lean_ctor_get(v_mctx_239_, 4);
v_decls_252_ = lean_ctor_get(v_mctx_239_, 5);
v_userNames_253_ = lean_ctor_get(v_mctx_239_, 6);
v_lAssignment_254_ = lean_ctor_get(v_mctx_239_, 7);
v_eAssignment_255_ = lean_ctor_get(v_mctx_239_, 8);
v_dAssignment_256_ = lean_ctor_get(v_mctx_239_, 9);
v_instanceTypedMVars_257_ = lean_ctor_get(v_mctx_239_, 10);
v_isSharedCheck_272_ = !lean_is_exclusive(v_mctx_239_);
if (v_isSharedCheck_272_ == 0)
{
v___x_259_ = v_mctx_239_;
v_isShared_260_ = v_isSharedCheck_272_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_instanceTypedMVars_257_);
lean_inc(v_dAssignment_256_);
lean_inc(v_eAssignment_255_);
lean_inc(v_lAssignment_254_);
lean_inc(v_userNames_253_);
lean_inc(v_decls_252_);
lean_inc(v_lDecls_251_);
lean_inc(v_mvarCounter_250_);
lean_inc(v_lmvarCounter_249_);
lean_inc(v_levelAssignDepth_248_);
lean_inc(v_depth_247_);
lean_dec(v_mctx_239_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_272_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v_fvars_234_);
lean_ctor_set(v___x_262_, 1, v_mvarIdPending_235_);
v___x_263_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5___redArg(v_dAssignment_256_, v_mvarId_233_, v___x_262_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 9, v___x_263_);
v___x_265_ = v___x_259_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_depth_247_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_levelAssignDepth_248_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_lmvarCounter_249_);
lean_ctor_set(v_reuseFailAlloc_271_, 3, v_mvarCounter_250_);
lean_ctor_set(v_reuseFailAlloc_271_, 4, v_lDecls_251_);
lean_ctor_set(v_reuseFailAlloc_271_, 5, v_decls_252_);
lean_ctor_set(v_reuseFailAlloc_271_, 6, v_userNames_253_);
lean_ctor_set(v_reuseFailAlloc_271_, 7, v_lAssignment_254_);
lean_ctor_set(v_reuseFailAlloc_271_, 8, v_eAssignment_255_);
lean_ctor_set(v_reuseFailAlloc_271_, 9, v___x_263_);
lean_ctor_set(v_reuseFailAlloc_271_, 10, v_instanceTypedMVars_257_);
v___x_265_ = v_reuseFailAlloc_271_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_267_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_265_);
v___x_267_ = v___x_245_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_cache_240_);
lean_ctor_set(v_reuseFailAlloc_270_, 2, v_zetaDeltaFVarIds_241_);
lean_ctor_set(v_reuseFailAlloc_270_, 3, v_postponed_242_);
lean_ctor_set(v_reuseFailAlloc_270_, 4, v_diag_243_);
v___x_267_ = v_reuseFailAlloc_270_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_st_ref_put(v___y_236_, v___x_267_);
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_261_);
return v___x_269_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4___redArg___boxed(lean_object* v_mvarId_274_, lean_object* v_fvars_275_, lean_object* v_mvarIdPending_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4___redArg(v_mvarId_274_, v_fvars_275_, v_mvarIdPending_276_, v___y_277_);
lean_dec(v___y_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5___redArg(lean_object* v_mvarId_280_, lean_object* v_val_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; lean_object* v_mctx_285_; lean_object* v_cache_286_; lean_object* v_zetaDeltaFVarIds_287_; lean_object* v_postponed_288_; lean_object* v_diag_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_318_; 
v___x_284_ = lean_st_ref_take(v___y_282_);
v_mctx_285_ = lean_ctor_get(v___x_284_, 0);
v_cache_286_ = lean_ctor_get(v___x_284_, 1);
v_zetaDeltaFVarIds_287_ = lean_ctor_get(v___x_284_, 2);
v_postponed_288_ = lean_ctor_get(v___x_284_, 3);
v_diag_289_ = lean_ctor_get(v___x_284_, 4);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_318_ == 0)
{
v___x_291_ = v___x_284_;
v_isShared_292_ = v_isSharedCheck_318_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_diag_289_);
lean_inc(v_postponed_288_);
lean_inc(v_zetaDeltaFVarIds_287_);
lean_inc(v_cache_286_);
lean_inc(v_mctx_285_);
lean_dec(v___x_284_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_318_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v_depth_293_; lean_object* v_levelAssignDepth_294_; lean_object* v_lmvarCounter_295_; lean_object* v_mvarCounter_296_; lean_object* v_lDecls_297_; lean_object* v_decls_298_; lean_object* v_userNames_299_; lean_object* v_lAssignment_300_; lean_object* v_eAssignment_301_; lean_object* v_dAssignment_302_; lean_object* v_instanceTypedMVars_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_317_; 
v_depth_293_ = lean_ctor_get(v_mctx_285_, 0);
v_levelAssignDepth_294_ = lean_ctor_get(v_mctx_285_, 1);
v_lmvarCounter_295_ = lean_ctor_get(v_mctx_285_, 2);
v_mvarCounter_296_ = lean_ctor_get(v_mctx_285_, 3);
v_lDecls_297_ = lean_ctor_get(v_mctx_285_, 4);
v_decls_298_ = lean_ctor_get(v_mctx_285_, 5);
v_userNames_299_ = lean_ctor_get(v_mctx_285_, 6);
v_lAssignment_300_ = lean_ctor_get(v_mctx_285_, 7);
v_eAssignment_301_ = lean_ctor_get(v_mctx_285_, 8);
v_dAssignment_302_ = lean_ctor_get(v_mctx_285_, 9);
v_instanceTypedMVars_303_ = lean_ctor_get(v_mctx_285_, 10);
v_isSharedCheck_317_ = !lean_is_exclusive(v_mctx_285_);
if (v_isSharedCheck_317_ == 0)
{
v___x_305_ = v_mctx_285_;
v_isShared_306_ = v_isSharedCheck_317_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_instanceTypedMVars_303_);
lean_inc(v_dAssignment_302_);
lean_inc(v_eAssignment_301_);
lean_inc(v_lAssignment_300_);
lean_inc(v_userNames_299_);
lean_inc(v_decls_298_);
lean_inc(v_lDecls_297_);
lean_inc(v_mvarCounter_296_);
lean_inc(v_lmvarCounter_295_);
lean_inc(v_levelAssignDepth_294_);
lean_inc(v_depth_293_);
lean_dec(v_mctx_285_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_317_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_307_ = lean_box(0);
v___x_308_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5___redArg(v_eAssignment_301_, v_mvarId_280_, v_val_281_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 8, v___x_308_);
v___x_310_ = v___x_305_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_depth_293_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_levelAssignDepth_294_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_lmvarCounter_295_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v_mvarCounter_296_);
lean_ctor_set(v_reuseFailAlloc_316_, 4, v_lDecls_297_);
lean_ctor_set(v_reuseFailAlloc_316_, 5, v_decls_298_);
lean_ctor_set(v_reuseFailAlloc_316_, 6, v_userNames_299_);
lean_ctor_set(v_reuseFailAlloc_316_, 7, v_lAssignment_300_);
lean_ctor_set(v_reuseFailAlloc_316_, 8, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_316_, 9, v_dAssignment_302_);
lean_ctor_set(v_reuseFailAlloc_316_, 10, v_instanceTypedMVars_303_);
v___x_310_ = v_reuseFailAlloc_316_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_312_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_310_);
v___x_312_ = v___x_291_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_cache_286_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_zetaDeltaFVarIds_287_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v_postponed_288_);
lean_ctor_set(v_reuseFailAlloc_315_, 4, v_diag_289_);
v___x_312_ = v_reuseFailAlloc_315_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_st_ref_put(v___y_282_, v___x_312_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_307_);
return v___x_314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5___redArg___boxed(lean_object* v_mvarId_319_, lean_object* v_val_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5___redArg(v_mvarId_319_, v_val_320_, v___y_321_);
lean_dec(v___y_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(lean_object* v___x_324_, lean_object* v_userName_325_, lean_object* v_lctx_326_, lean_object* v_localInstances_327_, lean_object* v_type_328_, lean_object* v_max_329_, lean_object* v_mvarId_330_, lean_object* v_lctx_331_, lean_object* v_localInsts_332_, lean_object* v_fvars_333_, lean_object* v_type_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = lean_array_get_size(v_fvars_333_);
v___x_343_ = lean_nat_dec_eq(v___x_342_, v___x_324_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
lean_inc_ref(v_fvars_333_);
lean_inc(v___x_324_);
v___x_344_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_334_, v___x_324_, v___x_342_, v_fvars_333_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; uint8_t v___x_346_; lean_object* v___x_347_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_344_, 1);
v___x_346_ = 2;
lean_inc(v___x_324_);
v___x_347_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_331_, v_localInsts_332_, v_a_345_, v___x_346_, v_userName_325_, v___x_324_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
v___x_349_ = l_Lean_Expr_mvarId_x21(v_a_348_);
lean_dec(v_a_348_);
v___x_350_ = lean_box(0);
lean_inc(v___x_324_);
lean_inc_ref(v_type_328_);
v___x_351_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_326_, v_localInstances_327_, v_type_328_, v___x_346_, v___x_350_, v___x_324_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc_n(v_a_352_, 2);
lean_dec_ref_known(v___x_351_, 1);
v___x_353_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkAppBVars(v_a_352_, v___x_342_);
v___x_354_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(v_max_329_, v___x_324_, v_type_328_, v___x_353_);
lean_dec_ref(v___x_353_);
lean_dec(v___x_324_);
v___x_355_ = l_Lean_Expr_mvarId_x21(v_a_352_);
lean_dec(v_a_352_);
lean_inc(v___x_349_);
lean_inc_ref(v_fvars_333_);
v___x_356_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4___redArg(v___x_355_, v_fvars_333_, v___x_349_, v___y_338_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v___x_357_; 
lean_dec_ref_known(v___x_356_, 1);
v___x_357_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5___redArg(v_mvarId_330_, v___x_354_, v___y_338_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_365_; 
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v___x_357_, 0);
lean_dec(v_unused_366_);
v___x_359_ = v___x_357_;
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
else
{
lean_dec(v___x_357_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_fvars_333_);
lean_ctor_set(v___x_361_, 1, v___x_349_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_361_);
v___x_363_ = v___x_359_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec(v___x_349_);
lean_dec_ref(v_fvars_333_);
v_a_367_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_357_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_357_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec_ref(v___x_354_);
lean_dec(v___x_349_);
lean_dec_ref(v_fvars_333_);
lean_dec(v_mvarId_330_);
v_a_375_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_356_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_356_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec(v___x_349_);
lean_dec_ref(v_fvars_333_);
lean_dec(v_mvarId_330_);
lean_dec_ref(v_type_328_);
lean_dec(v___x_324_);
v_a_383_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_351_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_351_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec_ref(v_fvars_333_);
lean_dec(v_mvarId_330_);
lean_dec_ref(v_type_328_);
lean_dec_ref(v_localInstances_327_);
lean_dec_ref(v_lctx_326_);
lean_dec(v___x_324_);
v_a_391_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_347_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_347_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec_ref(v_fvars_333_);
lean_dec_ref(v_localInsts_332_);
lean_dec_ref(v_lctx_331_);
lean_dec(v_mvarId_330_);
lean_dec_ref(v_type_328_);
lean_dec_ref(v_localInstances_327_);
lean_dec_ref(v_lctx_326_);
lean_dec(v_userName_325_);
lean_dec(v___x_324_);
v_a_399_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_344_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_344_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec_ref(v_type_334_);
lean_dec_ref(v_fvars_333_);
lean_dec_ref(v_localInsts_332_);
lean_dec_ref(v_lctx_331_);
lean_dec_ref(v_type_328_);
lean_dec_ref(v_localInstances_327_);
lean_dec_ref(v_lctx_326_);
lean_dec(v_userName_325_);
v___x_407_ = lean_mk_empty_array_with_capacity(v___x_324_);
lean_dec(v___x_324_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v_mvarId_330_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2___boxed(lean_object** _args){
lean_object* v___x_410_ = _args[0];
lean_object* v_userName_411_ = _args[1];
lean_object* v_lctx_412_ = _args[2];
lean_object* v_localInstances_413_ = _args[3];
lean_object* v_type_414_ = _args[4];
lean_object* v_max_415_ = _args[5];
lean_object* v_mvarId_416_ = _args[6];
lean_object* v_lctx_417_ = _args[7];
lean_object* v_localInsts_418_ = _args[8];
lean_object* v_fvars_419_ = _args[9];
lean_object* v_type_420_ = _args[10];
lean_object* v___y_421_ = _args[11];
lean_object* v___y_422_ = _args[12];
lean_object* v___y_423_ = _args[13];
lean_object* v___y_424_ = _args[14];
lean_object* v___y_425_ = _args[15];
lean_object* v___y_426_ = _args[16];
lean_object* v___y_427_ = _args[17];
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(v___x_410_, v_userName_411_, v_lctx_412_, v_localInstances_413_, v_type_414_, v_max_415_, v_mvarId_416_, v_lctx_417_, v_localInsts_418_, v_fvars_419_, v_type_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v_max_415_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(lean_object* v_localInsts_429_, lean_object* v_fvar_430_, lean_object* v_type_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Meta_Sym_isClass_x3f(v_type_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_451_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_451_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_451_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_451_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
if (lean_obj_tag(v_a_438_) == 1)
{
lean_object* v_val_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v_val_442_ = lean_ctor_get(v_a_438_, 0);
lean_inc(v_val_442_);
lean_dec_ref_known(v_a_438_, 1);
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v_val_442_);
lean_ctor_set(v___x_443_, 1, v_fvar_430_);
v___x_444_ = lean_array_push(v_localInsts_429_, v___x_443_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_444_);
v___x_446_ = v___x_440_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
else
{
lean_object* v___x_449_; 
lean_dec(v_a_438_);
lean_dec_ref(v_fvar_430_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v_localInsts_429_);
v___x_449_ = v___x_440_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_localInsts_429_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec_ref(v_fvar_430_);
lean_dec_ref(v_localInsts_429_);
v_a_452_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_437_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_437_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed(lean_object* v_localInsts_460_, lean_object* v_fvar_461_, lean_object* v_type_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(v_localInsts_460_, v_fvar_461_, v_type_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(lean_object* v_names_469_, uint8_t v_hygienic_470_, lean_object* v_lctx_471_, lean_object* v_binderName_472_, lean_object* v_i_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_array_get_size(v_names_469_);
v___x_480_ = lean_nat_dec_lt(v_i_473_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_471_, v_binderName_472_, v_hygienic_470_, v___y_476_, v___y_477_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec(v_binderName_472_);
v___x_482_ = lean_array_fget_borrowed(v_names_469_, v_i_473_);
lean_inc(v___x_482_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed(lean_object* v_names_484_, lean_object* v_hygienic_485_, lean_object* v_lctx_486_, lean_object* v_binderName_487_, lean_object* v_i_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
uint8_t v_hygienic_boxed_494_; lean_object* v_res_495_; 
v_hygienic_boxed_494_ = lean_unbox(v_hygienic_485_);
v_res_495_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(v_names_484_, v_hygienic_boxed_494_, v_lctx_486_, v_binderName_487_, v_i_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v_i_488_);
lean_dec_ref(v_lctx_486_);
lean_dec_ref(v_names_484_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1___redArg(lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; lean_object* v_ngen_499_; lean_object* v_namePrefix_500_; lean_object* v_idx_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_531_; 
v___x_498_ = lean_st_ref_get(v___y_496_);
v_ngen_499_ = lean_ctor_get(v___x_498_, 2);
lean_inc_ref(v_ngen_499_);
lean_dec(v___x_498_);
v_namePrefix_500_ = lean_ctor_get(v_ngen_499_, 0);
v_idx_501_ = lean_ctor_get(v_ngen_499_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_ngen_499_);
if (v_isSharedCheck_531_ == 0)
{
v___x_503_ = v_ngen_499_;
v_isShared_504_ = v_isSharedCheck_531_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_idx_501_);
lean_inc(v_namePrefix_500_);
lean_dec(v_ngen_499_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_531_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v_r_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_509_; 
lean_inc(v_idx_501_);
lean_inc(v_namePrefix_500_);
v_r_505_ = l_Lean_Name_num___override(v_namePrefix_500_, v_idx_501_);
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_add(v_idx_501_, v___x_506_);
lean_dec(v_idx_501_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_507_);
v___x_509_ = v___x_503_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_namePrefix_500_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_507_);
v___x_509_ = v_reuseFailAlloc_530_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_510_; lean_object* v_env_511_; lean_object* v_nextMacroScope_512_; lean_object* v_auxDeclNGen_513_; lean_object* v_traceState_514_; lean_object* v_cache_515_; lean_object* v_recordedDeps_516_; lean_object* v_messages_517_; lean_object* v_infoState_518_; lean_object* v_snapshotTasks_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_528_; 
v___x_510_ = lean_st_ref_take(v___y_496_);
v_env_511_ = lean_ctor_get(v___x_510_, 0);
v_nextMacroScope_512_ = lean_ctor_get(v___x_510_, 1);
v_auxDeclNGen_513_ = lean_ctor_get(v___x_510_, 3);
v_traceState_514_ = lean_ctor_get(v___x_510_, 4);
v_cache_515_ = lean_ctor_get(v___x_510_, 5);
v_recordedDeps_516_ = lean_ctor_get(v___x_510_, 6);
v_messages_517_ = lean_ctor_get(v___x_510_, 7);
v_infoState_518_ = lean_ctor_get(v___x_510_, 8);
v_snapshotTasks_519_ = lean_ctor_get(v___x_510_, 9);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v___x_510_, 2);
lean_dec(v_unused_529_);
v___x_521_ = v___x_510_;
v_isShared_522_ = v_isSharedCheck_528_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_snapshotTasks_519_);
lean_inc(v_infoState_518_);
lean_inc(v_messages_517_);
lean_inc(v_recordedDeps_516_);
lean_inc(v_cache_515_);
lean_inc(v_traceState_514_);
lean_inc(v_auxDeclNGen_513_);
lean_inc(v_nextMacroScope_512_);
lean_inc(v_env_511_);
lean_dec(v___x_510_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_528_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 2, v___x_509_);
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_env_511_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_nextMacroScope_512_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v_auxDeclNGen_513_);
lean_ctor_set(v_reuseFailAlloc_527_, 4, v_traceState_514_);
lean_ctor_set(v_reuseFailAlloc_527_, 5, v_cache_515_);
lean_ctor_set(v_reuseFailAlloc_527_, 6, v_recordedDeps_516_);
lean_ctor_set(v_reuseFailAlloc_527_, 7, v_messages_517_);
lean_ctor_set(v_reuseFailAlloc_527_, 8, v_infoState_518_);
lean_ctor_set(v_reuseFailAlloc_527_, 9, v_snapshotTasks_519_);
v___x_524_ = v_reuseFailAlloc_527_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_st_ref_put(v___y_496_, v___x_524_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v_r_505_);
return v___x_526_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1___redArg___boxed(lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1___redArg(v___y_532_);
lean_dec(v___y_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_542_; lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
v___x_542_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1___redArg(v___y_540_);
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___boxed(lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(size_t v_sz_559_, size_t v_i_560_, lean_object* v_bs_561_){
_start:
{
uint8_t v___x_562_; 
v___x_562_ = lean_usize_dec_lt(v_i_560_, v_sz_559_);
if (v___x_562_ == 0)
{
return v_bs_561_;
}
else
{
lean_object* v_v_563_; lean_object* v___x_564_; lean_object* v_bs_x27_565_; lean_object* v___x_566_; size_t v___x_567_; size_t v___x_568_; lean_object* v___x_569_; 
v_v_563_ = lean_array_uget(v_bs_561_, v_i_560_);
v___x_564_ = lean_unsigned_to_nat(0u);
v_bs_x27_565_ = lean_array_uset(v_bs_561_, v_i_560_, v___x_564_);
v___x_566_ = l_Lean_mkFVar(v_v_563_);
v___x_567_ = ((size_t)1ULL);
v___x_568_ = lean_usize_add(v_i_560_, v___x_567_);
v___x_569_ = lean_array_uset(v_bs_x27_565_, v_i_560_, v___x_566_);
v_i_560_ = v___x_568_;
v_bs_561_ = v___x_569_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0___boxed(lean_object* v_sz_571_, lean_object* v_i_572_, lean_object* v_bs_573_){
_start:
{
size_t v_sz_boxed_574_; size_t v_i_boxed_575_; lean_object* v_res_576_; 
v_sz_boxed_574_ = lean_unbox_usize(v_sz_571_);
lean_dec(v_sz_571_);
v_i_boxed_575_ = lean_unbox_usize(v_i_572_);
lean_dec(v_i_572_);
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v_sz_boxed_574_, v_i_boxed_575_, v_bs_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(lean_object* v_mvarId_582_, lean_object* v_max_583_, lean_object* v_names_584_, uint8_t v_hygienic_585_, lean_object* v_finalize_586_, lean_object* v_mkName_587_, lean_object* v_updateLocalInsts_588_, lean_object* v_i_589_, lean_object* v_lctx_590_, lean_object* v_localInsts_591_, lean_object* v_fvars_592_, lean_object* v_type_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_mvarId_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; uint8_t v___x_642_; 
v___x_642_ = lean_nat_dec_le(v_max_583_, v_i_589_);
if (v___x_642_ == 0)
{
switch(lean_obj_tag(v_type_593_))
{
case 10:
{
lean_object* v_expr_643_; 
v_expr_643_ = lean_ctor_get(v_type_593_, 1);
lean_inc_ref(v_expr_643_);
lean_dec_ref_known(v_type_593_, 2);
v_type_593_ = v_expr_643_;
goto _start;
}
case 7:
{
lean_object* v_binderName_645_; lean_object* v_binderType_646_; lean_object* v_body_647_; uint8_t v_binderInfo_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_binderName_645_ = lean_ctor_get(v_type_593_, 0);
lean_inc(v_binderName_645_);
v_binderType_646_ = lean_ctor_get(v_type_593_, 1);
lean_inc_ref(v_binderType_646_);
v_body_647_ = lean_ctor_get(v_type_593_, 2);
lean_inc_ref(v_body_647_);
v_binderInfo_648_ = lean_ctor_get_uint8(v_type_593_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_593_, 3);
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = lean_array_get_size(v_fvars_592_);
lean_inc_ref(v_fvars_592_);
v___x_651_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_binderType_646_, v___x_649_, v___x_650_, v_fvars_592_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v___x_653_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_655_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
lean_inc_ref(v_mkName_587_);
lean_inc(v_a_599_);
lean_inc_ref(v_a_598_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
lean_inc(v_i_589_);
lean_inc_ref(v_lctx_590_);
v___x_655_ = lean_apply_8(v_mkName_587_, v_lctx_590_, v_binderName_645_, v_i_589_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, lean_box(0));
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; uint8_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = l_Lean_LocalDeclKind_ofBinderName(v_a_656_);
lean_inc(v_a_652_);
lean_inc(v_a_654_);
v___x_658_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_590_, v_a_654_, v_a_656_, v_a_652_, v_binderInfo_648_, v___x_657_);
v___x_659_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__2___redArg(v_a_654_, v_a_595_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc_n(v_a_660_, 2);
lean_dec_ref_known(v___x_659_, 1);
v___x_661_ = lean_array_push(v_fvars_592_, v_a_660_);
lean_inc_ref(v_updateLocalInsts_588_);
lean_inc(v_a_599_);
lean_inc_ref(v_a_598_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
v___x_662_ = lean_apply_8(v_updateLocalInsts_588_, v_localInsts_591_, v_a_660_, v_a_652_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, lean_box(0));
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v___x_662_, 1);
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = lean_nat_add(v_i_589_, v___x_664_);
lean_dec(v_i_589_);
v_i_589_ = v___x_665_;
v_lctx_590_ = v___x_658_;
v_localInsts_591_ = v_a_663_;
v_fvars_592_ = v___x_661_;
v_type_593_ = v_body_647_;
goto _start;
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v___x_661_);
lean_dec_ref(v___x_658_);
lean_dec_ref(v_body_647_);
lean_dec(v_i_589_);
lean_dec_ref(v_updateLocalInsts_588_);
lean_dec_ref(v_mkName_587_);
lean_dec_ref(v_finalize_586_);
lean_dec(v_mvarId_582_);
v_a_667_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_662_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_662_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec_ref(v___x_658_);
lean_dec(v_a_652_);
lean_dec_ref(v_body_647_);
lean_dec_ref(v_fvars_592_);
lean_dec_ref(v_localInsts_591_);
lean_dec(v_i_589_);
lean_dec_ref(v_updateLocalInsts_588_);
lean_dec_ref(v_mkName_587_);
lean_dec_ref(v_finalize_586_);
lean_dec(v_mvarId_582_);
v_a_675_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_659_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_659_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec(v_a_654_);
lean_dec(v_a_652_);
lean_dec_ref(v_body_647_);
lean_dec_ref(v_fvars_592_);
lean_dec_ref(v_localInsts_591_);
lean_dec_ref(v_lctx_590_);
lean_dec(v_i_589_);
lean_dec_ref(v_updateLocalInsts_588_);
lean_dec_ref(v_mkName_587_);
lean_dec_ref(v_finalize_586_);
lean_dec(v_mvarId_582_);
v_a_683_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_655_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_655_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v_a_652_);
lean_dec_ref(v_body_647_);
lean_dec(v_binderName_645_);
lean_dec_ref(v_fvars_592_);
lean_dec_ref(v_localInsts_591_);
lean_dec_ref(v_lctx_590_);
lean_dec(v_i_589_);
lean_dec_ref(v_updateLocalInsts_588_);
lean_dec_ref(v_mkName_587_);
lean_dec_ref(v_finalize_586_);
lean_dec(v_mvarId_582_);
v_a_691_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_653_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_653_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec_ref(v_body_647_);
lean_dec(v_binderName_645_);
lean_dec_ref(v_fvars_592_);
lean_dec_ref(v_localInsts_591_);
lean_dec_ref(v_lctx_590_);
lean_dec(v_i_589_);
lean_dec_ref(v_updateLocalInsts_588_);
lean_dec_ref(v_mkName_587_);
lean_dec_ref(v_finalize_586_);
lean_dec(v_mvarId_582_);
v_a_699_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_651_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_651_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
case 8:
{
lean_object* v_declName_707_; lean_object* v_type_708_; lean_object* v_value_709_; lean_object* v_body_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_declName_707_ = lean_ctor_get(v_type_593_, 0);
lean_inc(v_declName_707_);
v_type_708_ = lean_ctor_get(v_type_593_, 1);
lean_inc_ref(v_type_708_);
v_value_709_ = lean_ctor_get(v_type_593_, 2);
lean_inc_ref(v_value_709_);
v_body_710_ = lean_ctor_get(v_type_593_, 3);
lean_inc_ref(v_body_710_);
lean_dec_ref_known(v_type_593_, 4);
v___x_711_ = lean_unsigned_to_nat(0u);
v___x_712_ = lean_array_get_size(v_fvars_592_);
lean_inc_ref(v_fvars_592_);
v___x_713_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_708_, v___x_711_, v___x_712_, v_fvars_592_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_715_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref_known(v___x_713_, 1);
lean_inc_ref(v_fvars_592_);
v___x_715_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_value_709_, v___x_711_, v___x_712_, v_fvars_592_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v___x_715_, 1);
v___x_717_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_719_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
lean_inc_ref(v_mkName_587_);
lean_inc(v_a_599_);
lean_inc_ref(v_a_598_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
lean_inc(v_i_589_);
lean_inc_ref(v_lctx_590_);
v___x_719_ = lean_apply_8(v_mkName_587_, v_lctx_590_, v_declName_707_, v_i_589_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, lean_box(0));
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; uint8_t v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_719_, 1);
v___x_721_ = l_Lean_LocalDeclKind_ofBinderName(v_a_720_);
lean_inc(v_a_714_);
lean_inc(v_a_718_);
v___x_722_ = l_Lean_LocalContext_mkLetDecl(v_lctx_590_, v_a_718_, v_a_720_, v_a_714_, v_a_716_, v___x_642_, v___x_721_);
v___x_723_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__2___redArg(v_a_718_, v_a_595_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc_n(v_a_724_, 2);
lean_dec_ref_known(v___x_723_, 1);
v___x_725_ = lean_array_push(v_fvars_592_, v_a_724_);
lean_inc_ref(v_updateLocalInsts_588_);
lean_inc(v_a_599_);
lean_inc_ref(v_a_598_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
v___x_726_ = lean_apply_8(v_updateLocalInsts_588_, v_localInsts_591_, v_a_724_, v_a_714_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, lean_box(0));
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = lean_nat_add(v_i_589_, v___x_728_);
lean_dec(v_i_589_);
v_i_589_ = v___x_729_;
v_lctx_590_ = v___x_722_;
v_localInsts_591_ = v_a_727_;
v_fvars_592_ = v___x_725_;
v_type_593_ = v_body_710_;
goto _start;
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v___x_725_);
lean_dec_ref(v___x_722_);
lean_dec_ref(v_body_710_);
lean_dec(v_i_589_);
lean_dec_ref(v_updateLocalInsts_588_);
lean_dec_ref(v_mkName_587_);
lean_dec_ref(v_finalize_586_);
lean_dec(v_mvarId_582_);
v_a_731_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_726_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_726_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec_ref(v___x_722_);
lean_dec(v_a_714_);
lean_dec_ref(v_body_710_);
lean_dec_ref(v_fvars_592_);
lean_dec_ref(v_localInsts_591_);
lean_dec(v_i_589_);
lean_dec_ref(v_updateLocalInsts_588_);
lean_dec_ref(v_mkName_587_);
lean_dec_ref(v_finalize_586_);
lean_dec(v_mvarId_582_);
v_a_739_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_723_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_723_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v_a_718_);
lean_dec(v_a_716_);
lean_dec(v_a_714_);
lean_dec_ref(v_body_710_);
lean_dec_ref(v_fvars_592_);
lean_dec_ref(v_localInsts_591_);
lean_dec_ref(v_lctx_590_);
lean_dec(v_i_589_);
lean_dec_ref(v_updateLocalInsts_588_);
lean_dec_ref(v_mkName_587_);
lean_dec_ref(v_finalize_586_);
lean_dec(v_mvarId_582_);
v_a_747_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_719_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_719_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_a_716_);
lean_dec(v_a_714_);
lean_dec_ref(v_body_710_);
lean_dec(v_declName_707_);
lean_dec_ref(v_fvars_592_);
lean_dec_ref(v_localInsts_591_);
lean_dec_ref(v_lctx_590_);
lean_dec(v_i_589_);
lean_dec_ref(v_updateLocalInsts_588_);
lean_dec_ref(v_mkName_587_);
lean_dec_ref(v_finalize_586_);
lean_dec(v_mvarId_582_);
v_a_755_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_717_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_717_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_a_714_);
lean_dec_ref(v_body_710_);
lean_dec(v_declName_707_);
lean_dec_ref(v_fvars_592_);
lean_dec_ref(v_localInsts_591_);
lean_dec_ref(v_lctx_590_);
lean_dec(v_i_589_);
lean_dec_ref(v_updateLocalInsts_588_);
lean_dec_ref(v_mkName_587_);
lean_dec_ref(v_finalize_586_);
lean_dec(v_mvarId_582_);
v_a_763_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_715_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_715_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v_body_710_);
lean_dec_ref(v_value_709_);
lean_dec(v_declName_707_);
lean_dec_ref(v_fvars_592_);
lean_dec_ref(v_localInsts_591_);
lean_dec_ref(v_lctx_590_);
lean_dec(v_i_589_);
lean_dec_ref(v_updateLocalInsts_588_);
lean_dec_ref(v_mkName_587_);
lean_dec_ref(v_finalize_586_);
lean_dec(v_mvarId_582_);
v_a_771_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_713_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_713_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
default: 
{
lean_object* v___x_779_; uint8_t v___x_780_; 
lean_dec_ref(v_updateLocalInsts_588_);
lean_dec_ref(v_mkName_587_);
v___x_779_ = l_Lean_Expr_getAppFn(v_type_593_);
v___x_780_ = l_Lean_Expr_isMVar(v___x_779_);
lean_dec_ref(v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_dec(v_i_589_);
lean_dec(v_mvarId_582_);
lean_inc(v_a_599_);
lean_inc_ref(v_a_598_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
lean_inc(v_a_595_);
lean_inc_ref(v_a_594_);
v___x_781_ = lean_apply_11(v_finalize_586_, v_lctx_590_, v_localInsts_591_, v_fvars_592_, v_type_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, lean_box(0));
return v___x_781_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = lean_array_get_size(v_fvars_592_);
lean_inc_ref(v_fvars_592_);
lean_inc_ref(v_type_593_);
v___x_784_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_593_, v___x_782_, v___x_783_, v_fvars_592_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_786_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_784_, 1);
v___x_786_ = l_Lean_Meta_Sym_instantiateAssignedMVarHeadS_x3f(v_a_785_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
if (lean_obj_tag(v_a_787_) == 1)
{
lean_object* v_val_788_; uint8_t v___x_789_; 
lean_dec_ref(v_type_593_);
v_val_788_ = lean_ctor_get(v_a_787_, 0);
lean_inc(v_val_788_);
lean_dec_ref_known(v_a_787_, 1);
v___x_789_ = lean_nat_dec_eq(v___x_783_, v___x_782_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
lean_dec(v_mvarId_582_);
lean_inc(v_a_599_);
lean_inc_ref(v_a_598_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
lean_inc(v_a_595_);
lean_inc_ref(v_a_594_);
lean_inc_ref(v_fvars_592_);
v___x_790_ = lean_apply_11(v_finalize_586_, v_lctx_590_, v_localInsts_591_, v_fvars_592_, v_val_788_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, lean_box(0));
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v_snd_792_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_790_, 1);
v_snd_792_ = lean_ctor_get(v_a_791_, 1);
lean_inc(v_snd_792_);
lean_dec(v_a_791_);
v_mvarId_602_ = v_snd_792_;
v___y_603_ = v_a_594_;
v___y_604_ = v_a_595_;
v___y_605_ = v_a_596_;
v___y_606_ = v_a_597_;
v___y_607_ = v_a_598_;
v___y_608_ = v_a_599_;
goto v___jp_601_;
}
else
{
lean_dec_ref(v_fvars_592_);
lean_dec(v_i_589_);
return v___x_790_;
}
}
else
{
lean_object* v___x_793_; 
lean_dec_ref(v_localInsts_591_);
lean_dec_ref(v_lctx_590_);
lean_dec_ref(v_finalize_586_);
lean_inc(v_mvarId_582_);
v___x_793_ = l_Lean_MVarId_setType___redArg(v_mvarId_582_, v_val_788_, v_a_597_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_dec_ref_known(v___x_793_, 1);
v_mvarId_602_ = v_mvarId_582_;
v___y_603_ = v_a_594_;
v___y_604_ = v_a_595_;
v___y_605_ = v_a_596_;
v___y_606_ = v_a_597_;
v___y_607_ = v_a_598_;
v___y_608_ = v_a_599_;
goto v___jp_601_;
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec_ref(v_fvars_592_);
lean_dec(v_i_589_);
lean_dec(v_mvarId_582_);
v_a_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
else
{
lean_object* v___x_802_; 
lean_dec(v_a_787_);
lean_dec(v_i_589_);
lean_dec(v_mvarId_582_);
lean_inc(v_a_599_);
lean_inc_ref(v_a_598_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
lean_inc(v_a_595_);
lean_inc_ref(v_a_594_);
v___x_802_ = lean_apply_11(v_finalize_586_, v_lctx_590_, v_localInsts_591_, v_fvars_592_, v_type_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, lean_box(0));
return v___x_802_;
}
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec_ref(v_type_593_);
lean_dec_ref(v_fvars_592_);
lean_dec_ref(v_localInsts_591_);
lean_dec_ref(v_lctx_590_);
lean_dec(v_i_589_);
lean_dec_ref(v_finalize_586_);
lean_dec(v_mvarId_582_);
v_a_803_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_786_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_786_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec_ref(v_type_593_);
lean_dec_ref(v_fvars_592_);
lean_dec_ref(v_localInsts_591_);
lean_dec_ref(v_lctx_590_);
lean_dec(v_i_589_);
lean_dec_ref(v_finalize_586_);
lean_dec(v_mvarId_582_);
v_a_811_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_784_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_784_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_819_; 
lean_dec(v_i_589_);
lean_dec_ref(v_updateLocalInsts_588_);
lean_dec_ref(v_mkName_587_);
lean_dec(v_mvarId_582_);
lean_inc(v_a_599_);
lean_inc_ref(v_a_598_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
lean_inc(v_a_595_);
lean_inc_ref(v_a_594_);
v___x_819_ = lean_apply_11(v_finalize_586_, v_lctx_590_, v_localInsts_591_, v_fvars_592_, v_type_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, lean_box(0));
return v___x_819_;
}
v___jp_601_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_609_ = lean_nat_sub(v_max_583_, v_i_589_);
v___x_610_ = lean_array_get_size(v_names_584_);
v___x_611_ = l_Array_extract___redArg(v_names_584_, v_i_589_, v___x_610_);
v___x_612_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_602_, v___x_609_, v___x_611_, v_hygienic_585_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_633_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_633_ == 0)
{
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_633_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_633_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v_fst_617_; lean_object* v_snd_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_632_; 
v_fst_617_ = lean_ctor_get(v_a_613_, 0);
v_snd_618_ = lean_ctor_get(v_a_613_, 1);
v_isSharedCheck_632_ = !lean_is_exclusive(v_a_613_);
if (v_isSharedCheck_632_ == 0)
{
v___x_620_ = v_a_613_;
v_isShared_621_ = v_isSharedCheck_632_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_snd_618_);
lean_inc(v_fst_617_);
lean_dec(v_a_613_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_632_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
size_t v_sz_622_; size_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v_sz_622_ = lean_array_size(v_fst_617_);
v___x_623_ = ((size_t)0ULL);
v___x_624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v_sz_622_, v___x_623_, v_fst_617_);
v___x_625_ = l_Array_append___redArg(v_fvars_592_, v___x_624_);
lean_dec_ref(v___x_624_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_625_);
v___x_627_ = v___x_620_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_snd_618_);
v___x_627_ = v_reuseFailAlloc_631_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_629_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_627_);
v___x_629_ = v___x_615_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec_ref(v_fvars_592_);
v_a_634_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_612_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_612_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(lean_object* v_mvarId_820_, lean_object* v_max_821_, lean_object* v_names_822_, uint8_t v_hygienic_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = lean_nat_dec_eq(v_max_821_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___f_834_; lean_object* v___f_835_; lean_object* v___x_836_; 
v___x_833_ = lean_box(v_hygienic_823_);
lean_inc_ref(v_names_822_);
v___f_834_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed), 10, 2);
lean_closure_set(v___f_834_, 0, v_names_822_);
lean_closure_set(v___f_834_, 1, v___x_833_);
v___f_835_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0));
lean_inc(v_mvarId_820_);
v___x_836_ = l_Lean_MVarId_getDecl(v_mvarId_820_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v_userName_838_; lean_object* v_lctx_839_; lean_object* v_type_840_; lean_object* v_localInstances_841_; lean_object* v___f_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref_known(v___x_836_, 1);
v_userName_838_ = lean_ctor_get(v_a_837_, 0);
lean_inc(v_userName_838_);
v_lctx_839_ = lean_ctor_get(v_a_837_, 1);
lean_inc_ref_n(v_lctx_839_, 2);
v_type_840_ = lean_ctor_get(v_a_837_, 2);
lean_inc_ref_n(v_type_840_, 2);
v_localInstances_841_ = lean_ctor_get(v_a_837_, 4);
lean_inc_ref_n(v_localInstances_841_, 2);
lean_dec(v_a_837_);
lean_inc(v_mvarId_820_);
lean_inc(v_max_821_);
v___f_842_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2___boxed), 18, 7);
lean_closure_set(v___f_842_, 0, v___x_831_);
lean_closure_set(v___f_842_, 1, v_userName_838_);
lean_closure_set(v___f_842_, 2, v_lctx_839_);
lean_closure_set(v___f_842_, 3, v_localInstances_841_);
lean_closure_set(v___f_842_, 4, v_type_840_);
lean_closure_set(v___f_842_, 5, v_max_821_);
lean_closure_set(v___f_842_, 6, v_mvarId_820_);
v___x_843_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
v___x_844_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(v_mvarId_820_, v_max_821_, v_names_822_, v_hygienic_823_, v___f_842_, v___f_834_, v___f_835_, v___x_831_, v_lctx_839_, v_localInstances_841_, v___x_843_, v_type_840_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
lean_dec_ref(v_names_822_);
lean_dec(v_max_821_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_864_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_864_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_864_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_864_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_fst_849_; lean_object* v_snd_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_863_; 
v_fst_849_ = lean_ctor_get(v_a_845_, 0);
v_snd_850_ = lean_ctor_get(v_a_845_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v_a_845_);
if (v_isSharedCheck_863_ == 0)
{
v___x_852_ = v_a_845_;
v_isShared_853_ = v_isSharedCheck_863_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_snd_850_);
lean_inc(v_fst_849_);
lean_dec(v_a_845_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_863_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
size_t v_sz_854_; size_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v_sz_854_ = lean_array_size(v_fst_849_);
v___x_855_ = ((size_t)0ULL);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__6(v_sz_854_, v___x_855_, v_fst_849_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_856_);
v___x_858_ = v___x_852_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_snd_850_);
v___x_858_ = v_reuseFailAlloc_862_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_860_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_858_);
v___x_860_ = v___x_847_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
v_a_865_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_844_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_844_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec_ref(v___f_834_);
lean_dec_ref(v_names_822_);
lean_dec(v_max_821_);
lean_dec(v_mvarId_820_);
v_a_873_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_836_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_836_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
lean_dec_ref(v_names_822_);
lean_dec(v_max_821_);
v___x_881_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__2));
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v_mvarId_820_);
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___boxed(lean_object* v_mvarId_884_, lean_object* v_max_885_, lean_object* v_names_886_, lean_object* v_hygienic_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
uint8_t v_hygienic_boxed_895_; lean_object* v_res_896_; 
v_hygienic_boxed_895_ = lean_unbox(v_hygienic_887_);
v_res_896_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_884_, v_max_885_, v_names_886_, v_hygienic_boxed_895_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit___boxed(lean_object** _args){
lean_object* v_mvarId_897_ = _args[0];
lean_object* v_max_898_ = _args[1];
lean_object* v_names_899_ = _args[2];
lean_object* v_hygienic_900_ = _args[3];
lean_object* v_finalize_901_ = _args[4];
lean_object* v_mkName_902_ = _args[5];
lean_object* v_updateLocalInsts_903_ = _args[6];
lean_object* v_i_904_ = _args[7];
lean_object* v_lctx_905_ = _args[8];
lean_object* v_localInsts_906_ = _args[9];
lean_object* v_fvars_907_ = _args[10];
lean_object* v_type_908_ = _args[11];
lean_object* v_a_909_ = _args[12];
lean_object* v_a_910_ = _args[13];
lean_object* v_a_911_ = _args[14];
lean_object* v_a_912_ = _args[15];
lean_object* v_a_913_ = _args[16];
lean_object* v_a_914_ = _args[17];
lean_object* v_a_915_ = _args[18];
_start:
{
uint8_t v_hygienic_boxed_916_; lean_object* v_res_917_; 
v_hygienic_boxed_916_ = lean_unbox(v_hygienic_900_);
v_res_917_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(v_mvarId_897_, v_max_898_, v_names_899_, v_hygienic_boxed_916_, v_finalize_901_, v_mkName_902_, v_updateLocalInsts_903_, v_i_904_, v_lctx_905_, v_localInsts_906_, v_fvars_907_, v_type_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec_ref(v_names_899_);
lean_dec(v_max_898_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1(lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1___redArg(v___y_923_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1___boxed(lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1(v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4(lean_object* v_mvarId_934_, lean_object* v_fvars_935_, lean_object* v_mvarIdPending_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4___redArg(v_mvarId_934_, v_fvars_935_, v_mvarIdPending_936_, v___y_938_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4___boxed(lean_object* v_mvarId_943_, lean_object* v_fvars_944_, lean_object* v_mvarIdPending_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4(v_mvarId_943_, v_fvars_944_, v_mvarIdPending_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5(lean_object* v_mvarId_952_, lean_object* v_val_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5___redArg(v_mvarId_952_, v_val_953_, v___y_955_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5___boxed(lean_object* v_mvarId_960_, lean_object* v_val_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5(v_mvarId_960_, v_val_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5(lean_object* v_00_u03b2_968_, lean_object* v_x_969_, lean_object* v_x_970_, lean_object* v_x_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5___redArg(v_x_969_, v_x_970_, v_x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_973_, lean_object* v_x_974_, size_t v_x_975_, size_t v_x_976_, lean_object* v_x_977_, lean_object* v_x_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg(v_x_974_, v_x_975_, v_x_976_, v_x_977_, v_x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b2_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v_x_984_, lean_object* v_x_985_){
_start:
{
size_t v_x_14353__boxed_986_; size_t v_x_14354__boxed_987_; lean_object* v_res_988_; 
v_x_14353__boxed_986_ = lean_unbox_usize(v_x_982_);
lean_dec(v_x_982_);
v_x_14354__boxed_987_ = lean_unbox_usize(v_x_983_);
lean_dec(v_x_983_);
v_res_988_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6(v_00_u03b2_980_, v_x_981_, v_x_14353__boxed_986_, v_x_14354__boxed_987_, v_x_984_, v_x_985_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__9(lean_object* v_00_u03b2_989_, lean_object* v_n_990_, lean_object* v_k_991_, lean_object* v_v_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__9___redArg(v_n_990_, v_k_991_, v_v_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__10(lean_object* v_00_u03b2_994_, size_t v_depth_995_, lean_object* v_keys_996_, lean_object* v_vals_997_, lean_object* v_heq_998_, lean_object* v_i_999_, lean_object* v_entries_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__10___redArg(v_depth_995_, v_keys_996_, v_vals_997_, v_i_999_, v_entries_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1002_, lean_object* v_depth_1003_, lean_object* v_keys_1004_, lean_object* v_vals_1005_, lean_object* v_heq_1006_, lean_object* v_i_1007_, lean_object* v_entries_1008_){
_start:
{
size_t v_depth_boxed_1009_; lean_object* v_res_1010_; 
v_depth_boxed_1009_ = lean_unbox_usize(v_depth_1003_);
lean_dec(v_depth_1003_);
v_res_1010_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__10(v_00_u03b2_1002_, v_depth_boxed_1009_, v_keys_1004_, v_vals_1005_, v_heq_1006_, v_i_1007_, v_entries_1008_);
lean_dec_ref(v_vals_1005_);
lean_dec_ref(v_keys_1004_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__9_spec__10(lean_object* v_00_u03b2_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_, lean_object* v_x_1014_, lean_object* v_x_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__9_spec__10___redArg(v_x_1012_, v_x_1013_, v_x_1014_, v_x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat(void){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_unsigned_to_nat(1000000u);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx___impl(lean_object* v_x_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_obj_tag_nat(v_x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx___impl___boxed(lean_object* v_x_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_Meta_Sym_IntrosResult_ctorIdx___impl(v_x_1020_);
lean_dec(v_x_1020_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(lean_object* v_t_1022_, lean_object* v_k_1023_){
_start:
{
if (lean_obj_tag(v_t_1022_) == 0)
{
return v_k_1023_;
}
else
{
lean_object* v_newDecls_1024_; lean_object* v_mvarId_1025_; lean_object* v___x_1026_; 
v_newDecls_1024_ = lean_ctor_get(v_t_1022_, 0);
lean_inc_ref(v_newDecls_1024_);
v_mvarId_1025_ = lean_ctor_get(v_t_1022_, 1);
lean_inc(v_mvarId_1025_);
lean_dec_ref_known(v_t_1022_, 2);
v___x_1026_ = lean_apply_2(v_k_1023_, v_newDecls_1024_, v_mvarId_1025_);
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim(lean_object* v_motive_1027_, lean_object* v_ctorIdx_1028_, lean_object* v_t_1029_, lean_object* v_h_1030_, lean_object* v_k_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_1029_, v_k_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___boxed(lean_object* v_motive_1033_, lean_object* v_ctorIdx_1034_, lean_object* v_t_1035_, lean_object* v_h_1036_, lean_object* v_k_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Meta_Sym_IntrosResult_ctorElim(v_motive_1033_, v_ctorIdx_1034_, v_t_1035_, v_h_1036_, v_k_1037_);
lean_dec(v_ctorIdx_1034_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim___redArg(lean_object* v_t_1039_, lean_object* v_failed_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_1039_, v_failed_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim(lean_object* v_motive_1042_, lean_object* v_t_1043_, lean_object* v_h_1044_, lean_object* v_failed_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_1043_, v_failed_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim___redArg(lean_object* v_t_1047_, lean_object* v_goal_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_1047_, v_goal_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim(lean_object* v_motive_1050_, lean_object* v_t_1051_, lean_object* v_h_1052_, lean_object* v_goal_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_1051_, v_goal_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros(lean_object* v_mvarId_1055_, lean_object* v_names_1056_, uint8_t v_hygienic_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_result_1066_; lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1082_ = lean_array_get_size(v_names_1056_);
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = lean_nat_dec_eq(v___x_1082_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; 
v___x_1085_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_1055_, v___x_1082_, v_names_1056_, v_hygienic_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v_result_1066_ = v_a_1086_;
goto v___jp_1065_;
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
v_a_1087_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1085_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1085_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec_ref(v_names_1056_);
v___x_1095_ = lean_unsigned_to_nat(1000000u);
v___x_1096_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__2));
v___x_1097_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_1055_, v___x_1095_, v___x_1096_, v_hygienic_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1097_, 1);
v_result_1066_ = v_a_1098_;
goto v___jp_1065_;
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
v_a_1099_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1097_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1097_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
v___jp_1065_:
{
lean_object* v_fst_1067_; lean_object* v_snd_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1081_; 
v_fst_1067_ = lean_ctor_get(v_result_1066_, 0);
v_snd_1068_ = lean_ctor_get(v_result_1066_, 1);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_result_1066_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1070_ = v_result_1066_;
v_isShared_1071_ = v_isSharedCheck_1081_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_snd_1068_);
lean_inc(v_fst_1067_);
lean_dec(v_result_1066_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1081_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1072_ = lean_array_get_size(v_fst_1067_);
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_nat_dec_eq(v___x_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1076_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 1);
v___x_1076_ = v___x_1070_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_fst_1067_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_snd_1068_);
v___x_1076_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
lean_del_object(v___x_1070_);
lean_dec(v_snd_1068_);
lean_dec(v_fst_1067_);
v___x_1079_ = lean_box(0);
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros___boxed(lean_object* v_mvarId_1107_, lean_object* v_names_1108_, lean_object* v_hygienic_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
uint8_t v_hygienic_boxed_1117_; lean_object* v_res_1118_; 
v_hygienic_boxed_1117_ = lean_unbox(v_hygienic_1109_);
v_res_1118_ = l_Lean_Meta_Sym_intros(v_mvarId_1107_, v_names_1108_, v_hygienic_boxed_1117_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN(lean_object* v_mvarId_1119_, lean_object* v_num_1120_, uint8_t v_hygienic_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__2));
lean_inc(v_num_1120_);
v___x_1130_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_1119_, v_num_1120_, v___x_1129_, v_hygienic_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1153_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1153_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1153_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v_fst_1135_; lean_object* v_snd_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1152_; 
v_fst_1135_ = lean_ctor_get(v_a_1131_, 0);
v_snd_1136_ = lean_ctor_get(v_a_1131_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_a_1131_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1138_ = v_a_1131_;
v_isShared_1139_ = v_isSharedCheck_1152_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_snd_1136_);
lean_inc(v_fst_1135_);
lean_dec(v_a_1131_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1152_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = lean_array_get_size(v_fst_1135_);
v___x_1141_ = lean_nat_dec_eq(v___x_1140_, v_num_1120_);
lean_dec(v_num_1120_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
lean_del_object(v___x_1138_);
lean_dec(v_snd_1136_);
lean_dec(v_fst_1135_);
v___x_1142_ = lean_box(0);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1142_);
v___x_1144_ = v___x_1133_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
else
{
lean_object* v___x_1147_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set_tag(v___x_1138_, 1);
v___x_1147_ = v___x_1138_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_fst_1135_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_snd_1136_);
v___x_1147_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1149_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1147_);
v___x_1149_ = v___x_1133_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v_num_1120_);
v_a_1154_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1130_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1130_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN___boxed(lean_object* v_mvarId_1162_, lean_object* v_num_1163_, lean_object* v_hygienic_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
uint8_t v_hygienic_boxed_1172_; lean_object* v_res_1173_; 
v_hygienic_boxed_1172_ = lean_unbox(v_hygienic_1164_);
v_res_1173_ = l_Lean_Meta_Sym_introN(v_mvarId_1162_, v_num_1163_, v_hygienic_boxed_1172_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
return v_res_1173_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_IsClass(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Intro(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_IsClass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat = _init_l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat();
lean_mark_persistent(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Intro(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_IsClass(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Intro(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_IsClass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Intro(builtin);
}
#ifdef __cplusplus
}
#endif
