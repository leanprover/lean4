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
size_t v_x_13121__boxed_223_; size_t v_x_13122__boxed_224_; lean_object* v_res_225_; 
v_x_13121__boxed_223_ = lean_unbox_usize(v_x_219_);
lean_dec(v_x_219_);
v_x_13122__boxed_224_ = lean_unbox_usize(v_x_220_);
lean_dec(v_x_220_);
v_res_225_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg(v_x_218_, v_x_13121__boxed_223_, v_x_13122__boxed_224_, v_x_221_, v_x_222_);
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
lean_object* v___x_238_; lean_object* v_mctx_239_; lean_object* v_cache_240_; lean_object* v_zetaDeltaFVarIds_241_; lean_object* v_postponed_242_; lean_object* v_diag_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_272_; 
v___x_238_ = lean_st_ref_take(v___y_236_);
v_mctx_239_ = lean_ctor_get(v___x_238_, 0);
v_cache_240_ = lean_ctor_get(v___x_238_, 1);
v_zetaDeltaFVarIds_241_ = lean_ctor_get(v___x_238_, 2);
v_postponed_242_ = lean_ctor_get(v___x_238_, 3);
v_diag_243_ = lean_ctor_get(v___x_238_, 4);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_272_ == 0)
{
v___x_245_ = v___x_238_;
v_isShared_246_ = v_isSharedCheck_272_;
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
v_isShared_246_ = v_isSharedCheck_272_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_depth_247_; lean_object* v_levelAssignDepth_248_; lean_object* v_lmvarCounter_249_; lean_object* v_mvarCounter_250_; lean_object* v_lDecls_251_; lean_object* v_decls_252_; lean_object* v_userNames_253_; lean_object* v_lAssignment_254_; lean_object* v_eAssignment_255_; lean_object* v_dAssignment_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_271_; 
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
v_isSharedCheck_271_ = !lean_is_exclusive(v_mctx_239_);
if (v_isSharedCheck_271_ == 0)
{
v___x_258_ = v_mctx_239_;
v_isShared_259_ = v_isSharedCheck_271_;
goto v_resetjp_257_;
}
else
{
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
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_271_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_260_ = lean_box(0);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v_fvars_234_);
lean_ctor_set(v___x_261_, 1, v_mvarIdPending_235_);
v___x_262_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5___redArg(v_dAssignment_256_, v_mvarId_233_, v___x_261_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 9, v___x_262_);
v___x_264_ = v___x_258_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_depth_247_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_levelAssignDepth_248_);
lean_ctor_set(v_reuseFailAlloc_270_, 2, v_lmvarCounter_249_);
lean_ctor_set(v_reuseFailAlloc_270_, 3, v_mvarCounter_250_);
lean_ctor_set(v_reuseFailAlloc_270_, 4, v_lDecls_251_);
lean_ctor_set(v_reuseFailAlloc_270_, 5, v_decls_252_);
lean_ctor_set(v_reuseFailAlloc_270_, 6, v_userNames_253_);
lean_ctor_set(v_reuseFailAlloc_270_, 7, v_lAssignment_254_);
lean_ctor_set(v_reuseFailAlloc_270_, 8, v_eAssignment_255_);
lean_ctor_set(v_reuseFailAlloc_270_, 9, v___x_262_);
v___x_264_ = v_reuseFailAlloc_270_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_266_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_264_);
v___x_266_ = v___x_245_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_cache_240_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_zetaDeltaFVarIds_241_);
lean_ctor_set(v_reuseFailAlloc_269_, 3, v_postponed_242_);
lean_ctor_set(v_reuseFailAlloc_269_, 4, v_diag_243_);
v___x_266_ = v_reuseFailAlloc_269_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_st_ref_put(v___y_236_, v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_260_);
return v___x_268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4___redArg___boxed(lean_object* v_mvarId_273_, lean_object* v_fvars_274_, lean_object* v_mvarIdPending_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4___redArg(v_mvarId_273_, v_fvars_274_, v_mvarIdPending_275_, v___y_276_);
lean_dec(v___y_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5___redArg(lean_object* v_mvarId_279_, lean_object* v_val_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___x_283_; lean_object* v_mctx_284_; lean_object* v_cache_285_; lean_object* v_zetaDeltaFVarIds_286_; lean_object* v_postponed_287_; lean_object* v_diag_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_316_; 
v___x_283_ = lean_st_ref_take(v___y_281_);
v_mctx_284_ = lean_ctor_get(v___x_283_, 0);
v_cache_285_ = lean_ctor_get(v___x_283_, 1);
v_zetaDeltaFVarIds_286_ = lean_ctor_get(v___x_283_, 2);
v_postponed_287_ = lean_ctor_get(v___x_283_, 3);
v_diag_288_ = lean_ctor_get(v___x_283_, 4);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_316_ == 0)
{
v___x_290_ = v___x_283_;
v_isShared_291_ = v_isSharedCheck_316_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_diag_288_);
lean_inc(v_postponed_287_);
lean_inc(v_zetaDeltaFVarIds_286_);
lean_inc(v_cache_285_);
lean_inc(v_mctx_284_);
lean_dec(v___x_283_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_316_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_depth_292_; lean_object* v_levelAssignDepth_293_; lean_object* v_lmvarCounter_294_; lean_object* v_mvarCounter_295_; lean_object* v_lDecls_296_; lean_object* v_decls_297_; lean_object* v_userNames_298_; lean_object* v_lAssignment_299_; lean_object* v_eAssignment_300_; lean_object* v_dAssignment_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_315_; 
v_depth_292_ = lean_ctor_get(v_mctx_284_, 0);
v_levelAssignDepth_293_ = lean_ctor_get(v_mctx_284_, 1);
v_lmvarCounter_294_ = lean_ctor_get(v_mctx_284_, 2);
v_mvarCounter_295_ = lean_ctor_get(v_mctx_284_, 3);
v_lDecls_296_ = lean_ctor_get(v_mctx_284_, 4);
v_decls_297_ = lean_ctor_get(v_mctx_284_, 5);
v_userNames_298_ = lean_ctor_get(v_mctx_284_, 6);
v_lAssignment_299_ = lean_ctor_get(v_mctx_284_, 7);
v_eAssignment_300_ = lean_ctor_get(v_mctx_284_, 8);
v_dAssignment_301_ = lean_ctor_get(v_mctx_284_, 9);
v_isSharedCheck_315_ = !lean_is_exclusive(v_mctx_284_);
if (v_isSharedCheck_315_ == 0)
{
v___x_303_ = v_mctx_284_;
v_isShared_304_ = v_isSharedCheck_315_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_dAssignment_301_);
lean_inc(v_eAssignment_300_);
lean_inc(v_lAssignment_299_);
lean_inc(v_userNames_298_);
lean_inc(v_decls_297_);
lean_inc(v_lDecls_296_);
lean_inc(v_mvarCounter_295_);
lean_inc(v_lmvarCounter_294_);
lean_inc(v_levelAssignDepth_293_);
lean_inc(v_depth_292_);
lean_dec(v_mctx_284_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_315_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_305_ = lean_box(0);
v___x_306_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5___redArg(v_eAssignment_300_, v_mvarId_279_, v_val_280_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 8, v___x_306_);
v___x_308_ = v___x_303_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_depth_292_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_levelAssignDepth_293_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v_lmvarCounter_294_);
lean_ctor_set(v_reuseFailAlloc_314_, 3, v_mvarCounter_295_);
lean_ctor_set(v_reuseFailAlloc_314_, 4, v_lDecls_296_);
lean_ctor_set(v_reuseFailAlloc_314_, 5, v_decls_297_);
lean_ctor_set(v_reuseFailAlloc_314_, 6, v_userNames_298_);
lean_ctor_set(v_reuseFailAlloc_314_, 7, v_lAssignment_299_);
lean_ctor_set(v_reuseFailAlloc_314_, 8, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_314_, 9, v_dAssignment_301_);
v___x_308_ = v_reuseFailAlloc_314_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_310_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_308_);
v___x_310_ = v___x_290_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_cache_285_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_zetaDeltaFVarIds_286_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v_postponed_287_);
lean_ctor_set(v_reuseFailAlloc_313_, 4, v_diag_288_);
v___x_310_ = v_reuseFailAlloc_313_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_st_ref_put(v___y_281_, v___x_310_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_305_);
return v___x_312_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5___redArg___boxed(lean_object* v_mvarId_317_, lean_object* v_val_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5___redArg(v_mvarId_317_, v_val_318_, v___y_319_);
lean_dec(v___y_319_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(lean_object* v___x_322_, lean_object* v_userName_323_, lean_object* v_lctx_324_, lean_object* v_localInstances_325_, lean_object* v_type_326_, lean_object* v_max_327_, lean_object* v_mvarId_328_, lean_object* v_lctx_329_, lean_object* v_localInsts_330_, lean_object* v_fvars_331_, lean_object* v_type_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = lean_array_get_size(v_fvars_331_);
v___x_341_ = lean_nat_dec_eq(v___x_340_, v___x_322_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
lean_inc_ref(v_fvars_331_);
lean_inc(v___x_322_);
v___x_342_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_332_, v___x_322_, v___x_340_, v_fvars_331_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; uint8_t v___x_344_; lean_object* v___x_345_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = 2;
lean_inc(v___x_322_);
v___x_345_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_329_, v_localInsts_330_, v_a_343_, v___x_344_, v_userName_323_, v___x_322_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 1);
v___x_347_ = l_Lean_Expr_mvarId_x21(v_a_346_);
lean_dec(v_a_346_);
v___x_348_ = lean_box(0);
lean_inc(v___x_322_);
lean_inc_ref(v_type_326_);
v___x_349_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_324_, v_localInstances_325_, v_type_326_, v___x_344_, v___x_348_, v___x_322_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc_n(v_a_350_, 2);
lean_dec_ref_known(v___x_349_, 1);
v___x_351_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkAppBVars(v_a_350_, v___x_340_);
v___x_352_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(v_max_327_, v___x_322_, v_type_326_, v___x_351_);
lean_dec_ref(v___x_351_);
lean_dec(v___x_322_);
v___x_353_ = l_Lean_Expr_mvarId_x21(v_a_350_);
lean_dec(v_a_350_);
lean_inc(v___x_347_);
lean_inc_ref(v_fvars_331_);
v___x_354_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4___redArg(v___x_353_, v_fvars_331_, v___x_347_, v___y_336_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v___x_355_; 
lean_dec_ref_known(v___x_354_, 1);
v___x_355_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5___redArg(v_mvarId_328_, v___x_352_, v___y_336_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_363_; 
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_363_ == 0)
{
lean_object* v_unused_364_; 
v_unused_364_ = lean_ctor_get(v___x_355_, 0);
lean_dec(v_unused_364_);
v___x_357_ = v___x_355_;
v_isShared_358_ = v_isSharedCheck_363_;
goto v_resetjp_356_;
}
else
{
lean_dec(v___x_355_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_363_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_fvars_331_);
lean_ctor_set(v___x_359_, 1, v___x_347_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_359_);
v___x_361_ = v___x_357_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
lean_dec(v___x_347_);
lean_dec_ref(v_fvars_331_);
v_a_365_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_355_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_355_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec_ref(v___x_352_);
lean_dec(v___x_347_);
lean_dec_ref(v_fvars_331_);
lean_dec(v_mvarId_328_);
v_a_373_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_354_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_354_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec(v___x_347_);
lean_dec_ref(v_fvars_331_);
lean_dec(v_mvarId_328_);
lean_dec_ref(v_type_326_);
lean_dec(v___x_322_);
v_a_381_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_349_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_349_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec_ref(v_fvars_331_);
lean_dec(v_mvarId_328_);
lean_dec_ref(v_type_326_);
lean_dec_ref(v_localInstances_325_);
lean_dec_ref(v_lctx_324_);
lean_dec(v___x_322_);
v_a_389_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_345_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_345_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec_ref(v_fvars_331_);
lean_dec_ref(v_localInsts_330_);
lean_dec_ref(v_lctx_329_);
lean_dec(v_mvarId_328_);
lean_dec_ref(v_type_326_);
lean_dec_ref(v_localInstances_325_);
lean_dec_ref(v_lctx_324_);
lean_dec(v_userName_323_);
lean_dec(v___x_322_);
v_a_397_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_342_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_342_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec_ref(v_type_332_);
lean_dec_ref(v_fvars_331_);
lean_dec_ref(v_localInsts_330_);
lean_dec_ref(v_lctx_329_);
lean_dec_ref(v_type_326_);
lean_dec_ref(v_localInstances_325_);
lean_dec_ref(v_lctx_324_);
lean_dec(v_userName_323_);
v___x_405_ = lean_mk_empty_array_with_capacity(v___x_322_);
lean_dec(v___x_322_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v_mvarId_328_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2___boxed(lean_object** _args){
lean_object* v___x_408_ = _args[0];
lean_object* v_userName_409_ = _args[1];
lean_object* v_lctx_410_ = _args[2];
lean_object* v_localInstances_411_ = _args[3];
lean_object* v_type_412_ = _args[4];
lean_object* v_max_413_ = _args[5];
lean_object* v_mvarId_414_ = _args[6];
lean_object* v_lctx_415_ = _args[7];
lean_object* v_localInsts_416_ = _args[8];
lean_object* v_fvars_417_ = _args[9];
lean_object* v_type_418_ = _args[10];
lean_object* v___y_419_ = _args[11];
lean_object* v___y_420_ = _args[12];
lean_object* v___y_421_ = _args[13];
lean_object* v___y_422_ = _args[14];
lean_object* v___y_423_ = _args[15];
lean_object* v___y_424_ = _args[16];
lean_object* v___y_425_ = _args[17];
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(v___x_408_, v_userName_409_, v_lctx_410_, v_localInstances_411_, v_type_412_, v_max_413_, v_mvarId_414_, v_lctx_415_, v_localInsts_416_, v_fvars_417_, v_type_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v_max_413_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(lean_object* v_localInsts_427_, lean_object* v_fvar_428_, lean_object* v_type_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Meta_Sym_isClass_x3f(v_type_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_449_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_449_ == 0)
{
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_449_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_449_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
if (lean_obj_tag(v_a_436_) == 1)
{
lean_object* v_val_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v_val_440_ = lean_ctor_get(v_a_436_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v_a_436_, 1);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v_val_440_);
lean_ctor_set(v___x_441_, 1, v_fvar_428_);
v___x_442_ = lean_array_push(v_localInsts_427_, v___x_441_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_442_);
v___x_444_ = v___x_438_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
else
{
lean_object* v___x_447_; 
lean_dec(v_a_436_);
lean_dec_ref(v_fvar_428_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v_localInsts_427_);
v___x_447_ = v___x_438_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_localInsts_427_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec_ref(v_fvar_428_);
lean_dec_ref(v_localInsts_427_);
v_a_450_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_435_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_435_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed(lean_object* v_localInsts_458_, lean_object* v_fvar_459_, lean_object* v_type_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(v_localInsts_458_, v_fvar_459_, v_type_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(lean_object* v_names_467_, uint8_t v_hygienic_468_, lean_object* v_lctx_469_, lean_object* v_binderName_470_, lean_object* v_i_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_477_ = lean_array_get_size(v_names_467_);
v___x_478_ = lean_nat_dec_lt(v_i_471_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_469_, v_binderName_470_, v_hygienic_468_, v___y_474_, v___y_475_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v_binderName_470_);
v___x_480_ = lean_array_fget_borrowed(v_names_467_, v_i_471_);
lean_inc(v___x_480_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed(lean_object* v_names_482_, lean_object* v_hygienic_483_, lean_object* v_lctx_484_, lean_object* v_binderName_485_, lean_object* v_i_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
uint8_t v_hygienic_boxed_492_; lean_object* v_res_493_; 
v_hygienic_boxed_492_ = lean_unbox(v_hygienic_483_);
v_res_493_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(v_names_482_, v_hygienic_boxed_492_, v_lctx_484_, v_binderName_485_, v_i_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v_i_486_);
lean_dec_ref(v_lctx_484_);
lean_dec_ref(v_names_482_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1___redArg(lean_object* v___y_494_){
_start:
{
lean_object* v___x_496_; lean_object* v_ngen_497_; lean_object* v_namePrefix_498_; lean_object* v_idx_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_529_; 
v___x_496_ = lean_st_ref_get(v___y_494_);
v_ngen_497_ = lean_ctor_get(v___x_496_, 2);
lean_inc_ref(v_ngen_497_);
lean_dec(v___x_496_);
v_namePrefix_498_ = lean_ctor_get(v_ngen_497_, 0);
v_idx_499_ = lean_ctor_get(v_ngen_497_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v_ngen_497_);
if (v_isSharedCheck_529_ == 0)
{
v___x_501_ = v_ngen_497_;
v_isShared_502_ = v_isSharedCheck_529_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_idx_499_);
lean_inc(v_namePrefix_498_);
lean_dec(v_ngen_497_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_529_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v_r_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
lean_inc(v_idx_499_);
lean_inc(v_namePrefix_498_);
v_r_503_ = l_Lean_Name_num___override(v_namePrefix_498_, v_idx_499_);
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = lean_nat_add(v_idx_499_, v___x_504_);
lean_dec(v_idx_499_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 1, v___x_505_);
v___x_507_ = v___x_501_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_namePrefix_498_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___x_505_);
v___x_507_ = v_reuseFailAlloc_528_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; lean_object* v_env_509_; lean_object* v_nextMacroScope_510_; lean_object* v_auxDeclNGen_511_; lean_object* v_traceState_512_; lean_object* v_cache_513_; lean_object* v_recordedDeps_514_; lean_object* v_messages_515_; lean_object* v_infoState_516_; lean_object* v_snapshotTasks_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_526_; 
v___x_508_ = lean_st_ref_take(v___y_494_);
v_env_509_ = lean_ctor_get(v___x_508_, 0);
v_nextMacroScope_510_ = lean_ctor_get(v___x_508_, 1);
v_auxDeclNGen_511_ = lean_ctor_get(v___x_508_, 3);
v_traceState_512_ = lean_ctor_get(v___x_508_, 4);
v_cache_513_ = lean_ctor_get(v___x_508_, 5);
v_recordedDeps_514_ = lean_ctor_get(v___x_508_, 6);
v_messages_515_ = lean_ctor_get(v___x_508_, 7);
v_infoState_516_ = lean_ctor_get(v___x_508_, 8);
v_snapshotTasks_517_ = lean_ctor_get(v___x_508_, 9);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_526_ == 0)
{
lean_object* v_unused_527_; 
v_unused_527_ = lean_ctor_get(v___x_508_, 2);
lean_dec(v_unused_527_);
v___x_519_ = v___x_508_;
v_isShared_520_ = v_isSharedCheck_526_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_snapshotTasks_517_);
lean_inc(v_infoState_516_);
lean_inc(v_messages_515_);
lean_inc(v_recordedDeps_514_);
lean_inc(v_cache_513_);
lean_inc(v_traceState_512_);
lean_inc(v_auxDeclNGen_511_);
lean_inc(v_nextMacroScope_510_);
lean_inc(v_env_509_);
lean_dec(v___x_508_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_526_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 2, v___x_507_);
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_env_509_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_nextMacroScope_510_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_525_, 3, v_auxDeclNGen_511_);
lean_ctor_set(v_reuseFailAlloc_525_, 4, v_traceState_512_);
lean_ctor_set(v_reuseFailAlloc_525_, 5, v_cache_513_);
lean_ctor_set(v_reuseFailAlloc_525_, 6, v_recordedDeps_514_);
lean_ctor_set(v_reuseFailAlloc_525_, 7, v_messages_515_);
lean_ctor_set(v_reuseFailAlloc_525_, 8, v_infoState_516_);
lean_ctor_set(v_reuseFailAlloc_525_, 9, v_snapshotTasks_517_);
v___x_522_ = v_reuseFailAlloc_525_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_st_ref_put(v___y_494_, v___x_522_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v_r_503_);
return v___x_524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1___redArg___boxed(lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1___redArg(v___y_530_);
lean_dec(v___y_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___x_540_; lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v___x_540_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1___redArg(v___y_538_);
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___boxed(lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(size_t v_sz_557_, size_t v_i_558_, lean_object* v_bs_559_){
_start:
{
uint8_t v___x_560_; 
v___x_560_ = lean_usize_dec_lt(v_i_558_, v_sz_557_);
if (v___x_560_ == 0)
{
return v_bs_559_;
}
else
{
lean_object* v_v_561_; lean_object* v___x_562_; lean_object* v_bs_x27_563_; lean_object* v___x_564_; size_t v___x_565_; size_t v___x_566_; lean_object* v___x_567_; 
v_v_561_ = lean_array_uget(v_bs_559_, v_i_558_);
v___x_562_ = lean_unsigned_to_nat(0u);
v_bs_x27_563_ = lean_array_uset(v_bs_559_, v_i_558_, v___x_562_);
v___x_564_ = l_Lean_mkFVar(v_v_561_);
v___x_565_ = ((size_t)1ULL);
v___x_566_ = lean_usize_add(v_i_558_, v___x_565_);
v___x_567_ = lean_array_uset(v_bs_x27_563_, v_i_558_, v___x_564_);
v_i_558_ = v___x_566_;
v_bs_559_ = v___x_567_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0___boxed(lean_object* v_sz_569_, lean_object* v_i_570_, lean_object* v_bs_571_){
_start:
{
size_t v_sz_boxed_572_; size_t v_i_boxed_573_; lean_object* v_res_574_; 
v_sz_boxed_572_ = lean_unbox_usize(v_sz_569_);
lean_dec(v_sz_569_);
v_i_boxed_573_ = lean_unbox_usize(v_i_570_);
lean_dec(v_i_570_);
v_res_574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v_sz_boxed_572_, v_i_boxed_573_, v_bs_571_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(lean_object* v_mvarId_580_, lean_object* v_max_581_, lean_object* v_names_582_, uint8_t v_hygienic_583_, lean_object* v_finalize_584_, lean_object* v_mkName_585_, lean_object* v_updateLocalInsts_586_, lean_object* v_i_587_, lean_object* v_lctx_588_, lean_object* v_localInsts_589_, lean_object* v_fvars_590_, lean_object* v_type_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_mvarId_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; uint8_t v___x_640_; 
v___x_640_ = lean_nat_dec_le(v_max_581_, v_i_587_);
if (v___x_640_ == 0)
{
switch(lean_obj_tag(v_type_591_))
{
case 10:
{
lean_object* v_expr_641_; 
v_expr_641_ = lean_ctor_get(v_type_591_, 1);
lean_inc_ref(v_expr_641_);
lean_dec_ref_known(v_type_591_, 2);
v_type_591_ = v_expr_641_;
goto _start;
}
case 7:
{
lean_object* v_binderName_643_; lean_object* v_binderType_644_; lean_object* v_body_645_; uint8_t v_binderInfo_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_binderName_643_ = lean_ctor_get(v_type_591_, 0);
lean_inc(v_binderName_643_);
v_binderType_644_ = lean_ctor_get(v_type_591_, 1);
lean_inc_ref(v_binderType_644_);
v_body_645_ = lean_ctor_get(v_type_591_, 2);
lean_inc_ref(v_body_645_);
v_binderInfo_646_ = lean_ctor_get_uint8(v_type_591_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_591_, 3);
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_array_get_size(v_fvars_590_);
lean_inc_ref(v_fvars_590_);
v___x_649_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_binderType_644_, v___x_647_, v___x_648_, v_fvars_590_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_651_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref_known(v___x_649_, 1);
v___x_651_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
lean_inc_ref(v_mkName_585_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
lean_inc(v_a_595_);
lean_inc_ref(v_a_594_);
lean_inc(v_i_587_);
lean_inc_ref(v_lctx_588_);
v___x_653_ = lean_apply_8(v_mkName_585_, v_lctx_588_, v_binderName_643_, v_i_587_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, lean_box(0));
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; uint8_t v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = l_Lean_LocalDeclKind_ofBinderName(v_a_654_);
lean_inc(v_a_650_);
lean_inc(v_a_652_);
v___x_656_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_588_, v_a_652_, v_a_654_, v_a_650_, v_binderInfo_646_, v___x_655_);
v___x_657_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__2___redArg(v_a_652_, v_a_593_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc_n(v_a_658_, 2);
lean_dec_ref_known(v___x_657_, 1);
v___x_659_ = lean_array_push(v_fvars_590_, v_a_658_);
lean_inc_ref(v_updateLocalInsts_586_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
lean_inc(v_a_595_);
lean_inc_ref(v_a_594_);
v___x_660_ = lean_apply_8(v_updateLocalInsts_586_, v_localInsts_589_, v_a_658_, v_a_650_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, lean_box(0));
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_660_, 1);
v___x_662_ = lean_unsigned_to_nat(1u);
v___x_663_ = lean_nat_add(v_i_587_, v___x_662_);
lean_dec(v_i_587_);
v_i_587_ = v___x_663_;
v_lctx_588_ = v___x_656_;
v_localInsts_589_ = v_a_661_;
v_fvars_590_ = v___x_659_;
v_type_591_ = v_body_645_;
goto _start;
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref(v___x_659_);
lean_dec_ref(v___x_656_);
lean_dec_ref(v_body_645_);
lean_dec(v_i_587_);
lean_dec_ref(v_updateLocalInsts_586_);
lean_dec_ref(v_mkName_585_);
lean_dec_ref(v_finalize_584_);
lean_dec(v_mvarId_580_);
v_a_665_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_660_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_660_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v___x_656_);
lean_dec(v_a_650_);
lean_dec_ref(v_body_645_);
lean_dec_ref(v_fvars_590_);
lean_dec_ref(v_localInsts_589_);
lean_dec(v_i_587_);
lean_dec_ref(v_updateLocalInsts_586_);
lean_dec_ref(v_mkName_585_);
lean_dec_ref(v_finalize_584_);
lean_dec(v_mvarId_580_);
v_a_673_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_657_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_657_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec(v_a_652_);
lean_dec(v_a_650_);
lean_dec_ref(v_body_645_);
lean_dec_ref(v_fvars_590_);
lean_dec_ref(v_localInsts_589_);
lean_dec_ref(v_lctx_588_);
lean_dec(v_i_587_);
lean_dec_ref(v_updateLocalInsts_586_);
lean_dec_ref(v_mkName_585_);
lean_dec_ref(v_finalize_584_);
lean_dec(v_mvarId_580_);
v_a_681_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_653_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_653_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v_a_650_);
lean_dec_ref(v_body_645_);
lean_dec(v_binderName_643_);
lean_dec_ref(v_fvars_590_);
lean_dec_ref(v_localInsts_589_);
lean_dec_ref(v_lctx_588_);
lean_dec(v_i_587_);
lean_dec_ref(v_updateLocalInsts_586_);
lean_dec_ref(v_mkName_585_);
lean_dec_ref(v_finalize_584_);
lean_dec(v_mvarId_580_);
v_a_689_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_651_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_651_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec_ref(v_body_645_);
lean_dec(v_binderName_643_);
lean_dec_ref(v_fvars_590_);
lean_dec_ref(v_localInsts_589_);
lean_dec_ref(v_lctx_588_);
lean_dec(v_i_587_);
lean_dec_ref(v_updateLocalInsts_586_);
lean_dec_ref(v_mkName_585_);
lean_dec_ref(v_finalize_584_);
lean_dec(v_mvarId_580_);
v_a_697_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_649_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_649_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
case 8:
{
lean_object* v_declName_705_; lean_object* v_type_706_; lean_object* v_value_707_; lean_object* v_body_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_declName_705_ = lean_ctor_get(v_type_591_, 0);
lean_inc(v_declName_705_);
v_type_706_ = lean_ctor_get(v_type_591_, 1);
lean_inc_ref(v_type_706_);
v_value_707_ = lean_ctor_get(v_type_591_, 2);
lean_inc_ref(v_value_707_);
v_body_708_ = lean_ctor_get(v_type_591_, 3);
lean_inc_ref(v_body_708_);
lean_dec_ref_known(v_type_591_, 4);
v___x_709_ = lean_unsigned_to_nat(0u);
v___x_710_ = lean_array_get_size(v_fvars_590_);
lean_inc_ref(v_fvars_590_);
v___x_711_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_706_, v___x_709_, v___x_710_, v_fvars_590_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_713_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
lean_inc_ref(v_fvars_590_);
v___x_713_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_value_707_, v___x_709_, v___x_710_, v_fvars_590_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_715_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref_known(v___x_713_, 1);
v___x_715_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v___x_715_, 1);
lean_inc_ref(v_mkName_585_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
lean_inc(v_a_595_);
lean_inc_ref(v_a_594_);
lean_inc(v_i_587_);
lean_inc_ref(v_lctx_588_);
v___x_717_ = lean_apply_8(v_mkName_585_, v_lctx_588_, v_declName_705_, v_i_587_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, lean_box(0));
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; uint8_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
v___x_719_ = l_Lean_LocalDeclKind_ofBinderName(v_a_718_);
lean_inc(v_a_712_);
lean_inc(v_a_716_);
v___x_720_ = l_Lean_LocalContext_mkLetDecl(v_lctx_588_, v_a_716_, v_a_718_, v_a_712_, v_a_714_, v___x_640_, v___x_719_);
v___x_721_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__2___redArg(v_a_716_, v_a_593_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc_n(v_a_722_, 2);
lean_dec_ref_known(v___x_721_, 1);
v___x_723_ = lean_array_push(v_fvars_590_, v_a_722_);
lean_inc_ref(v_updateLocalInsts_586_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
lean_inc(v_a_595_);
lean_inc_ref(v_a_594_);
v___x_724_ = lean_apply_8(v_updateLocalInsts_586_, v_localInsts_589_, v_a_722_, v_a_712_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, lean_box(0));
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref_known(v___x_724_, 1);
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = lean_nat_add(v_i_587_, v___x_726_);
lean_dec(v_i_587_);
v_i_587_ = v___x_727_;
v_lctx_588_ = v___x_720_;
v_localInsts_589_ = v_a_725_;
v_fvars_590_ = v___x_723_;
v_type_591_ = v_body_708_;
goto _start;
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref(v___x_723_);
lean_dec_ref(v___x_720_);
lean_dec_ref(v_body_708_);
lean_dec(v_i_587_);
lean_dec_ref(v_updateLocalInsts_586_);
lean_dec_ref(v_mkName_585_);
lean_dec_ref(v_finalize_584_);
lean_dec(v_mvarId_580_);
v_a_729_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_724_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_724_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec_ref(v___x_720_);
lean_dec(v_a_712_);
lean_dec_ref(v_body_708_);
lean_dec_ref(v_fvars_590_);
lean_dec_ref(v_localInsts_589_);
lean_dec(v_i_587_);
lean_dec_ref(v_updateLocalInsts_586_);
lean_dec_ref(v_mkName_585_);
lean_dec_ref(v_finalize_584_);
lean_dec(v_mvarId_580_);
v_a_737_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_721_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_721_);
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
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v_a_716_);
lean_dec(v_a_714_);
lean_dec(v_a_712_);
lean_dec_ref(v_body_708_);
lean_dec_ref(v_fvars_590_);
lean_dec_ref(v_localInsts_589_);
lean_dec_ref(v_lctx_588_);
lean_dec(v_i_587_);
lean_dec_ref(v_updateLocalInsts_586_);
lean_dec_ref(v_mkName_585_);
lean_dec_ref(v_finalize_584_);
lean_dec(v_mvarId_580_);
v_a_745_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_717_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_717_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec(v_a_714_);
lean_dec(v_a_712_);
lean_dec_ref(v_body_708_);
lean_dec(v_declName_705_);
lean_dec_ref(v_fvars_590_);
lean_dec_ref(v_localInsts_589_);
lean_dec_ref(v_lctx_588_);
lean_dec(v_i_587_);
lean_dec_ref(v_updateLocalInsts_586_);
lean_dec_ref(v_mkName_585_);
lean_dec_ref(v_finalize_584_);
lean_dec(v_mvarId_580_);
v_a_753_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_715_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_715_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v_a_712_);
lean_dec_ref(v_body_708_);
lean_dec(v_declName_705_);
lean_dec_ref(v_fvars_590_);
lean_dec_ref(v_localInsts_589_);
lean_dec_ref(v_lctx_588_);
lean_dec(v_i_587_);
lean_dec_ref(v_updateLocalInsts_586_);
lean_dec_ref(v_mkName_585_);
lean_dec_ref(v_finalize_584_);
lean_dec(v_mvarId_580_);
v_a_761_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_713_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_713_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v_body_708_);
lean_dec_ref(v_value_707_);
lean_dec(v_declName_705_);
lean_dec_ref(v_fvars_590_);
lean_dec_ref(v_localInsts_589_);
lean_dec_ref(v_lctx_588_);
lean_dec(v_i_587_);
lean_dec_ref(v_updateLocalInsts_586_);
lean_dec_ref(v_mkName_585_);
lean_dec_ref(v_finalize_584_);
lean_dec(v_mvarId_580_);
v_a_769_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_711_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_711_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
default: 
{
lean_object* v___x_777_; uint8_t v___x_778_; 
lean_dec_ref(v_updateLocalInsts_586_);
lean_dec_ref(v_mkName_585_);
v___x_777_ = l_Lean_Expr_getAppFn(v_type_591_);
v___x_778_ = l_Lean_Expr_isMVar(v___x_777_);
lean_dec_ref(v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
lean_dec(v_i_587_);
lean_dec(v_mvarId_580_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
lean_inc(v_a_595_);
lean_inc_ref(v_a_594_);
lean_inc(v_a_593_);
lean_inc_ref(v_a_592_);
v___x_779_ = lean_apply_11(v_finalize_584_, v_lctx_588_, v_localInsts_589_, v_fvars_590_, v_type_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, lean_box(0));
return v___x_779_;
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = lean_array_get_size(v_fvars_590_);
lean_inc_ref(v_fvars_590_);
lean_inc_ref(v_type_591_);
v___x_782_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_591_, v___x_780_, v___x_781_, v_fvars_590_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_784_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_782_, 1);
v___x_784_ = l_Lean_Meta_Sym_instantiateAssignedMVarHeadS_x3f(v_a_783_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_784_, 1);
if (lean_obj_tag(v_a_785_) == 1)
{
lean_object* v_val_786_; uint8_t v___x_787_; 
lean_dec_ref(v_type_591_);
v_val_786_ = lean_ctor_get(v_a_785_, 0);
lean_inc(v_val_786_);
lean_dec_ref_known(v_a_785_, 1);
v___x_787_ = lean_nat_dec_eq(v___x_781_, v___x_780_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
lean_dec(v_mvarId_580_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
lean_inc(v_a_595_);
lean_inc_ref(v_a_594_);
lean_inc(v_a_593_);
lean_inc_ref(v_a_592_);
lean_inc_ref(v_fvars_590_);
v___x_788_ = lean_apply_11(v_finalize_584_, v_lctx_588_, v_localInsts_589_, v_fvars_590_, v_val_786_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, lean_box(0));
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v_snd_790_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v_snd_790_ = lean_ctor_get(v_a_789_, 1);
lean_inc(v_snd_790_);
lean_dec(v_a_789_);
v_mvarId_600_ = v_snd_790_;
v___y_601_ = v_a_592_;
v___y_602_ = v_a_593_;
v___y_603_ = v_a_594_;
v___y_604_ = v_a_595_;
v___y_605_ = v_a_596_;
v___y_606_ = v_a_597_;
goto v___jp_599_;
}
else
{
lean_dec_ref(v_fvars_590_);
lean_dec(v_i_587_);
return v___x_788_;
}
}
else
{
lean_object* v___x_791_; 
lean_dec_ref(v_localInsts_589_);
lean_dec_ref(v_lctx_588_);
lean_dec_ref(v_finalize_584_);
lean_inc(v_mvarId_580_);
v___x_791_ = l_Lean_MVarId_setType___redArg(v_mvarId_580_, v_val_786_, v_a_595_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_dec_ref_known(v___x_791_, 1);
v_mvarId_600_ = v_mvarId_580_;
v___y_601_ = v_a_592_;
v___y_602_ = v_a_593_;
v___y_603_ = v_a_594_;
v___y_604_ = v_a_595_;
v___y_605_ = v_a_596_;
v___y_606_ = v_a_597_;
goto v___jp_599_;
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec_ref(v_fvars_590_);
lean_dec(v_i_587_);
lean_dec(v_mvarId_580_);
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
else
{
lean_object* v___x_800_; 
lean_dec(v_a_785_);
lean_dec(v_i_587_);
lean_dec(v_mvarId_580_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
lean_inc(v_a_595_);
lean_inc_ref(v_a_594_);
lean_inc(v_a_593_);
lean_inc_ref(v_a_592_);
v___x_800_ = lean_apply_11(v_finalize_584_, v_lctx_588_, v_localInsts_589_, v_fvars_590_, v_type_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, lean_box(0));
return v___x_800_;
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec_ref(v_type_591_);
lean_dec_ref(v_fvars_590_);
lean_dec_ref(v_localInsts_589_);
lean_dec_ref(v_lctx_588_);
lean_dec(v_i_587_);
lean_dec_ref(v_finalize_584_);
lean_dec(v_mvarId_580_);
v_a_801_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_784_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_784_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_type_591_);
lean_dec_ref(v_fvars_590_);
lean_dec_ref(v_localInsts_589_);
lean_dec_ref(v_lctx_588_);
lean_dec(v_i_587_);
lean_dec_ref(v_finalize_584_);
lean_dec(v_mvarId_580_);
v_a_809_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_782_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_782_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_817_; 
lean_dec(v_i_587_);
lean_dec_ref(v_updateLocalInsts_586_);
lean_dec_ref(v_mkName_585_);
lean_dec(v_mvarId_580_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
lean_inc(v_a_595_);
lean_inc_ref(v_a_594_);
lean_inc(v_a_593_);
lean_inc_ref(v_a_592_);
v___x_817_ = lean_apply_11(v_finalize_584_, v_lctx_588_, v_localInsts_589_, v_fvars_590_, v_type_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, lean_box(0));
return v___x_817_;
}
v___jp_599_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_607_ = lean_nat_sub(v_max_581_, v_i_587_);
v___x_608_ = lean_array_get_size(v_names_582_);
v___x_609_ = l_Array_extract___redArg(v_names_582_, v_i_587_, v___x_608_);
v___x_610_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_600_, v___x_607_, v___x_609_, v_hygienic_583_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_631_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_631_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_631_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_631_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_fst_615_; lean_object* v_snd_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_630_; 
v_fst_615_ = lean_ctor_get(v_a_611_, 0);
v_snd_616_ = lean_ctor_get(v_a_611_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v_a_611_);
if (v_isSharedCheck_630_ == 0)
{
v___x_618_ = v_a_611_;
v_isShared_619_ = v_isSharedCheck_630_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_snd_616_);
lean_inc(v_fst_615_);
lean_dec(v_a_611_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_630_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
size_t v_sz_620_; size_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v_sz_620_ = lean_array_size(v_fst_615_);
v___x_621_ = ((size_t)0ULL);
v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v_sz_620_, v___x_621_, v_fst_615_);
v___x_623_ = l_Array_append___redArg(v_fvars_590_, v___x_622_);
lean_dec_ref(v___x_622_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_623_);
v___x_625_ = v___x_618_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_snd_616_);
v___x_625_ = v_reuseFailAlloc_629_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_627_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_625_);
v___x_627_ = v___x_613_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec_ref(v_fvars_590_);
v_a_632_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_610_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_610_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(lean_object* v_mvarId_818_, lean_object* v_max_819_, lean_object* v_names_820_, uint8_t v_hygienic_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_nat_dec_eq(v_max_819_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___f_832_; lean_object* v___f_833_; lean_object* v___x_834_; 
v___x_831_ = lean_box(v_hygienic_821_);
lean_inc_ref(v_names_820_);
v___f_832_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed), 10, 2);
lean_closure_set(v___f_832_, 0, v_names_820_);
lean_closure_set(v___f_832_, 1, v___x_831_);
v___f_833_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0));
lean_inc(v_mvarId_818_);
v___x_834_ = l_Lean_MVarId_getDecl(v_mvarId_818_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v_userName_836_; lean_object* v_lctx_837_; lean_object* v_type_838_; lean_object* v_localInstances_839_; lean_object* v___f_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
lean_dec_ref_known(v___x_834_, 1);
v_userName_836_ = lean_ctor_get(v_a_835_, 0);
lean_inc(v_userName_836_);
v_lctx_837_ = lean_ctor_get(v_a_835_, 1);
lean_inc_ref_n(v_lctx_837_, 2);
v_type_838_ = lean_ctor_get(v_a_835_, 2);
lean_inc_ref_n(v_type_838_, 2);
v_localInstances_839_ = lean_ctor_get(v_a_835_, 4);
lean_inc_ref_n(v_localInstances_839_, 2);
lean_dec(v_a_835_);
lean_inc(v_mvarId_818_);
lean_inc(v_max_819_);
v___f_840_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2___boxed), 18, 7);
lean_closure_set(v___f_840_, 0, v___x_829_);
lean_closure_set(v___f_840_, 1, v_userName_836_);
lean_closure_set(v___f_840_, 2, v_lctx_837_);
lean_closure_set(v___f_840_, 3, v_localInstances_839_);
lean_closure_set(v___f_840_, 4, v_type_838_);
lean_closure_set(v___f_840_, 5, v_max_819_);
lean_closure_set(v___f_840_, 6, v_mvarId_818_);
v___x_841_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
v___x_842_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(v_mvarId_818_, v_max_819_, v_names_820_, v_hygienic_821_, v___f_840_, v___f_832_, v___f_833_, v___x_829_, v_lctx_837_, v_localInstances_839_, v___x_841_, v_type_838_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
lean_dec_ref(v_names_820_);
lean_dec(v_max_819_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_862_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_862_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_862_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_862_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_fst_847_; lean_object* v_snd_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_861_; 
v_fst_847_ = lean_ctor_get(v_a_843_, 0);
v_snd_848_ = lean_ctor_get(v_a_843_, 1);
v_isSharedCheck_861_ = !lean_is_exclusive(v_a_843_);
if (v_isSharedCheck_861_ == 0)
{
v___x_850_ = v_a_843_;
v_isShared_851_ = v_isSharedCheck_861_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_snd_848_);
lean_inc(v_fst_847_);
lean_dec(v_a_843_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_861_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
size_t v_sz_852_; size_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v_sz_852_ = lean_array_size(v_fst_847_);
v___x_853_ = ((size_t)0ULL);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__6(v_sz_852_, v___x_853_, v_fst_847_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_854_);
v___x_856_ = v___x_850_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_snd_848_);
v___x_856_ = v_reuseFailAlloc_860_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_858_; 
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_856_);
v___x_858_ = v___x_845_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
v_a_863_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_842_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_842_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec_ref(v___f_832_);
lean_dec_ref(v_names_820_);
lean_dec(v_max_819_);
lean_dec(v_mvarId_818_);
v_a_871_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_834_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_834_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec_ref(v_names_820_);
lean_dec(v_max_819_);
v___x_879_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__2));
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v_mvarId_818_);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___boxed(lean_object* v_mvarId_882_, lean_object* v_max_883_, lean_object* v_names_884_, lean_object* v_hygienic_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
uint8_t v_hygienic_boxed_893_; lean_object* v_res_894_; 
v_hygienic_boxed_893_ = lean_unbox(v_hygienic_885_);
v_res_894_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_882_, v_max_883_, v_names_884_, v_hygienic_boxed_893_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit___boxed(lean_object** _args){
lean_object* v_mvarId_895_ = _args[0];
lean_object* v_max_896_ = _args[1];
lean_object* v_names_897_ = _args[2];
lean_object* v_hygienic_898_ = _args[3];
lean_object* v_finalize_899_ = _args[4];
lean_object* v_mkName_900_ = _args[5];
lean_object* v_updateLocalInsts_901_ = _args[6];
lean_object* v_i_902_ = _args[7];
lean_object* v_lctx_903_ = _args[8];
lean_object* v_localInsts_904_ = _args[9];
lean_object* v_fvars_905_ = _args[10];
lean_object* v_type_906_ = _args[11];
lean_object* v_a_907_ = _args[12];
lean_object* v_a_908_ = _args[13];
lean_object* v_a_909_ = _args[14];
lean_object* v_a_910_ = _args[15];
lean_object* v_a_911_ = _args[16];
lean_object* v_a_912_ = _args[17];
lean_object* v_a_913_ = _args[18];
_start:
{
uint8_t v_hygienic_boxed_914_; lean_object* v_res_915_; 
v_hygienic_boxed_914_ = lean_unbox(v_hygienic_898_);
v_res_915_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(v_mvarId_895_, v_max_896_, v_names_897_, v_hygienic_boxed_914_, v_finalize_899_, v_mkName_900_, v_updateLocalInsts_901_, v_i_902_, v_lctx_903_, v_localInsts_904_, v_fvars_905_, v_type_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec_ref(v_names_897_);
lean_dec(v_max_896_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1(lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1___redArg(v___y_921_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1___boxed(lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_spec__1(v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4(lean_object* v_mvarId_932_, lean_object* v_fvars_933_, lean_object* v_mvarIdPending_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4___redArg(v_mvarId_932_, v_fvars_933_, v_mvarIdPending_934_, v___y_936_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4___boxed(lean_object* v_mvarId_941_, lean_object* v_fvars_942_, lean_object* v_mvarIdPending_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4(v_mvarId_941_, v_fvars_942_, v_mvarIdPending_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5(lean_object* v_mvarId_950_, lean_object* v_val_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5___redArg(v_mvarId_950_, v_val_951_, v___y_953_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5___boxed(lean_object* v_mvarId_958_, lean_object* v_val_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__5(v_mvarId_958_, v_val_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5(lean_object* v_00_u03b2_966_, lean_object* v_x_967_, lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5___redArg(v_x_967_, v_x_968_, v_x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_971_, lean_object* v_x_972_, size_t v_x_973_, size_t v_x_974_, lean_object* v_x_975_, lean_object* v_x_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___redArg(v_x_972_, v_x_973_, v_x_974_, v_x_975_, v_x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b2_978_, lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
size_t v_x_14345__boxed_984_; size_t v_x_14346__boxed_985_; lean_object* v_res_986_; 
v_x_14345__boxed_984_ = lean_unbox_usize(v_x_980_);
lean_dec(v_x_980_);
v_x_14346__boxed_985_ = lean_unbox_usize(v_x_981_);
lean_dec(v_x_981_);
v_res_986_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6(v_00_u03b2_978_, v_x_979_, v_x_14345__boxed_984_, v_x_14346__boxed_985_, v_x_982_, v_x_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__9(lean_object* v_00_u03b2_987_, lean_object* v_n_988_, lean_object* v_k_989_, lean_object* v_v_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__9___redArg(v_n_988_, v_k_989_, v_v_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__10(lean_object* v_00_u03b2_992_, size_t v_depth_993_, lean_object* v_keys_994_, lean_object* v_vals_995_, lean_object* v_heq_996_, lean_object* v_i_997_, lean_object* v_entries_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__10___redArg(v_depth_993_, v_keys_994_, v_vals_995_, v_i_997_, v_entries_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1000_, lean_object* v_depth_1001_, lean_object* v_keys_1002_, lean_object* v_vals_1003_, lean_object* v_heq_1004_, lean_object* v_i_1005_, lean_object* v_entries_1006_){
_start:
{
size_t v_depth_boxed_1007_; lean_object* v_res_1008_; 
v_depth_boxed_1007_ = lean_unbox_usize(v_depth_1001_);
lean_dec(v_depth_1001_);
v_res_1008_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__10(v_00_u03b2_1000_, v_depth_boxed_1007_, v_keys_1002_, v_vals_1003_, v_heq_1004_, v_i_1005_, v_entries_1006_);
lean_dec_ref(v_vals_1003_);
lean_dec_ref(v_keys_1002_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__9_spec__10(lean_object* v_00_u03b2_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__4_spec__5_spec__6_spec__9_spec__10___redArg(v_x_1010_, v_x_1011_, v_x_1012_, v_x_1013_);
return v___x_1014_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat(void){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_unsigned_to_nat(1000000u);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx___impl(lean_object* v_x_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_obj_tag_nat(v_x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx___impl___boxed(lean_object* v_x_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_Meta_Sym_IntrosResult_ctorIdx___impl(v_x_1018_);
lean_dec(v_x_1018_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(lean_object* v_t_1020_, lean_object* v_k_1021_){
_start:
{
if (lean_obj_tag(v_t_1020_) == 0)
{
return v_k_1021_;
}
else
{
lean_object* v_newDecls_1022_; lean_object* v_mvarId_1023_; lean_object* v___x_1024_; 
v_newDecls_1022_ = lean_ctor_get(v_t_1020_, 0);
lean_inc_ref(v_newDecls_1022_);
v_mvarId_1023_ = lean_ctor_get(v_t_1020_, 1);
lean_inc(v_mvarId_1023_);
lean_dec_ref_known(v_t_1020_, 2);
v___x_1024_ = lean_apply_2(v_k_1021_, v_newDecls_1022_, v_mvarId_1023_);
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim(lean_object* v_motive_1025_, lean_object* v_ctorIdx_1026_, lean_object* v_t_1027_, lean_object* v_h_1028_, lean_object* v_k_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_1027_, v_k_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___boxed(lean_object* v_motive_1031_, lean_object* v_ctorIdx_1032_, lean_object* v_t_1033_, lean_object* v_h_1034_, lean_object* v_k_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_Meta_Sym_IntrosResult_ctorElim(v_motive_1031_, v_ctorIdx_1032_, v_t_1033_, v_h_1034_, v_k_1035_);
lean_dec(v_ctorIdx_1032_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim___redArg(lean_object* v_t_1037_, lean_object* v_failed_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_1037_, v_failed_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim(lean_object* v_motive_1040_, lean_object* v_t_1041_, lean_object* v_h_1042_, lean_object* v_failed_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_1041_, v_failed_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim___redArg(lean_object* v_t_1045_, lean_object* v_goal_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_1045_, v_goal_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim(lean_object* v_motive_1048_, lean_object* v_t_1049_, lean_object* v_h_1050_, lean_object* v_goal_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_1049_, v_goal_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros(lean_object* v_mvarId_1053_, lean_object* v_names_1054_, uint8_t v_hygienic_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_result_1064_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1080_ = lean_array_get_size(v_names_1054_);
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = lean_nat_dec_eq(v___x_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; 
v___x_1083_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_1053_, v___x_1080_, v_names_1054_, v_hygienic_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
v_result_1064_ = v_a_1084_;
goto v___jp_1063_;
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
v_a_1085_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1083_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1083_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_dec_ref(v_names_1054_);
v___x_1093_ = lean_unsigned_to_nat(1000000u);
v___x_1094_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__2));
v___x_1095_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_1053_, v___x_1093_, v___x_1094_, v_hygienic_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v_result_1064_ = v_a_1096_;
goto v___jp_1063_;
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
v_a_1097_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1095_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1095_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
v___jp_1063_:
{
lean_object* v_fst_1065_; lean_object* v_snd_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1079_; 
v_fst_1065_ = lean_ctor_get(v_result_1064_, 0);
v_snd_1066_ = lean_ctor_get(v_result_1064_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_result_1064_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1068_ = v_result_1064_;
v_isShared_1069_ = v_isSharedCheck_1079_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_snd_1066_);
lean_inc(v_fst_1065_);
lean_dec(v_result_1064_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1079_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1070_ = lean_array_get_size(v_fst_1065_);
v___x_1071_ = lean_unsigned_to_nat(0u);
v___x_1072_ = lean_nat_dec_eq(v___x_1070_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1074_; 
if (v_isShared_1069_ == 0)
{
lean_ctor_set_tag(v___x_1068_, 1);
v___x_1074_ = v___x_1068_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_fst_1065_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_snd_1066_);
v___x_1074_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_del_object(v___x_1068_);
lean_dec(v_snd_1066_);
lean_dec(v_fst_1065_);
v___x_1077_ = lean_box(0);
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros___boxed(lean_object* v_mvarId_1105_, lean_object* v_names_1106_, lean_object* v_hygienic_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
uint8_t v_hygienic_boxed_1115_; lean_object* v_res_1116_; 
v_hygienic_boxed_1115_ = lean_unbox(v_hygienic_1107_);
v_res_1116_ = l_Lean_Meta_Sym_intros(v_mvarId_1105_, v_names_1106_, v_hygienic_boxed_1115_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN(lean_object* v_mvarId_1117_, lean_object* v_num_1118_, uint8_t v_hygienic_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__2));
lean_inc(v_num_1118_);
v___x_1128_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_1117_, v_num_1118_, v___x_1127_, v_hygienic_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1151_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1151_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1151_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v_fst_1133_; lean_object* v_snd_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1150_; 
v_fst_1133_ = lean_ctor_get(v_a_1129_, 0);
v_snd_1134_ = lean_ctor_get(v_a_1129_, 1);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_a_1129_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1136_ = v_a_1129_;
v_isShared_1137_ = v_isSharedCheck_1150_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_snd_1134_);
lean_inc(v_fst_1133_);
lean_dec(v_a_1129_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1150_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_array_get_size(v_fst_1133_);
v___x_1139_ = lean_nat_dec_eq(v___x_1138_, v_num_1118_);
lean_dec(v_num_1118_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
lean_del_object(v___x_1136_);
lean_dec(v_snd_1134_);
lean_dec(v_fst_1133_);
v___x_1140_ = lean_box(0);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1140_);
v___x_1142_ = v___x_1131_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
else
{
lean_object* v___x_1145_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set_tag(v___x_1136_, 1);
v___x_1145_ = v___x_1136_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_fst_1133_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_snd_1134_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1145_);
v___x_1147_ = v___x_1131_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v_num_1118_);
v_a_1152_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1128_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1128_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN___boxed(lean_object* v_mvarId_1160_, lean_object* v_num_1161_, lean_object* v_hygienic_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
uint8_t v_hygienic_boxed_1170_; lean_object* v_res_1171_; 
v_hygienic_boxed_1170_ = lean_unbox(v_hygienic_1162_);
v_res_1171_ = l_Lean_Meta_Sym_introN(v_mvarId_1160_, v_num_1161_, v_hygienic_boxed_1170_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
return v_res_1171_;
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
