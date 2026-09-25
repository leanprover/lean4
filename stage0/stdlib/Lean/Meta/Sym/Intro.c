// Lean compiler output
// Module: Lean.Meta.Sym.Intro
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.Tactic.Intro import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.IsClass import Lean.Meta.Sym.AlphaShareBuilder
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_Sym_isClass_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkAppBVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(lean_object* v_fvarId_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = l_Lean_Expr_fvar___override(v_fvarId_39_);
v___x_43_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_42_, v___y_40_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg___boxed(lean_object* v_fvarId_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(v_fvarId_44_, v___y_45_);
lean_dec(v___y_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(lean_object* v_fvarId_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(v_fvarId_48_, v___y_50_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___boxed(lean_object* v_fvarId_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(v_fvarId_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; lean_object* v_ngen_69_; lean_object* v_namePrefix_70_; lean_object* v_idx_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_101_; 
v___x_68_ = lean_st_ref_get(v___y_66_);
v_ngen_69_ = lean_ctor_get(v___x_68_, 2);
lean_inc_ref(v_ngen_69_);
lean_dec(v___x_68_);
v_namePrefix_70_ = lean_ctor_get(v_ngen_69_, 0);
v_idx_71_ = lean_ctor_get(v_ngen_69_, 1);
v_isSharedCheck_101_ = !lean_is_exclusive(v_ngen_69_);
if (v_isSharedCheck_101_ == 0)
{
v___x_73_ = v_ngen_69_;
v_isShared_74_ = v_isSharedCheck_101_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_idx_71_);
lean_inc(v_namePrefix_70_);
lean_dec(v_ngen_69_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_101_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v_r_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_79_; 
lean_inc(v_idx_71_);
lean_inc(v_namePrefix_70_);
v_r_75_ = l_Lean_Name_num___override(v_namePrefix_70_, v_idx_71_);
v___x_76_ = lean_unsigned_to_nat(1u);
v___x_77_ = lean_nat_add(v_idx_71_, v___x_76_);
lean_dec(v_idx_71_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___x_77_);
v___x_79_ = v___x_73_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_namePrefix_70_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v___x_77_);
v___x_79_ = v_reuseFailAlloc_100_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_object* v___x_80_; lean_object* v_env_81_; lean_object* v_nextMacroScope_82_; lean_object* v_auxDeclNGen_83_; lean_object* v_traceState_84_; lean_object* v_cache_85_; lean_object* v_recordedDeps_86_; lean_object* v_messages_87_; lean_object* v_infoState_88_; lean_object* v_snapshotTasks_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_98_; 
v___x_80_ = lean_st_ref_take(v___y_66_);
v_env_81_ = lean_ctor_get(v___x_80_, 0);
v_nextMacroScope_82_ = lean_ctor_get(v___x_80_, 1);
v_auxDeclNGen_83_ = lean_ctor_get(v___x_80_, 3);
v_traceState_84_ = lean_ctor_get(v___x_80_, 4);
v_cache_85_ = lean_ctor_get(v___x_80_, 5);
v_recordedDeps_86_ = lean_ctor_get(v___x_80_, 6);
v_messages_87_ = lean_ctor_get(v___x_80_, 7);
v_infoState_88_ = lean_ctor_get(v___x_80_, 8);
v_snapshotTasks_89_ = lean_ctor_get(v___x_80_, 9);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_98_ == 0)
{
lean_object* v_unused_99_; 
v_unused_99_ = lean_ctor_get(v___x_80_, 2);
lean_dec(v_unused_99_);
v___x_91_ = v___x_80_;
v_isShared_92_ = v_isSharedCheck_98_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_snapshotTasks_89_);
lean_inc(v_infoState_88_);
lean_inc(v_messages_87_);
lean_inc(v_recordedDeps_86_);
lean_inc(v_cache_85_);
lean_inc(v_traceState_84_);
lean_inc(v_auxDeclNGen_83_);
lean_inc(v_nextMacroScope_82_);
lean_inc(v_env_81_);
lean_dec(v___x_80_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_98_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 2, v___x_79_);
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_env_81_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_nextMacroScope_82_);
lean_ctor_set(v_reuseFailAlloc_97_, 2, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_97_, 3, v_auxDeclNGen_83_);
lean_ctor_set(v_reuseFailAlloc_97_, 4, v_traceState_84_);
lean_ctor_set(v_reuseFailAlloc_97_, 5, v_cache_85_);
lean_ctor_set(v_reuseFailAlloc_97_, 6, v_recordedDeps_86_);
lean_ctor_set(v_reuseFailAlloc_97_, 7, v_messages_87_);
lean_ctor_set(v_reuseFailAlloc_97_, 8, v_infoState_88_);
lean_ctor_set(v_reuseFailAlloc_97_, 9, v_snapshotTasks_89_);
v___x_94_ = v_reuseFailAlloc_97_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_st_ref_put(v___y_66_, v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v_r_75_);
return v___x_96_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg___boxed(lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(v___y_102_);
lean_dec(v___y_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
v___x_112_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(v___y_110_);
v_a_113_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v___x_112_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_112_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0___boxed(lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(lean_object* v_max_129_, lean_object* v_finalize_130_, lean_object* v_mkName_131_, lean_object* v_updateLocalInsts_132_, lean_object* v_i_133_, lean_object* v_lctx_134_, lean_object* v_localInsts_135_, lean_object* v_fvars_136_, lean_object* v_type_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
uint8_t v___x_145_; 
v___x_145_ = lean_nat_dec_le(v_max_129_, v_i_133_);
if (v___x_145_ == 0)
{
switch(lean_obj_tag(v_type_137_))
{
case 10:
{
lean_object* v_expr_146_; 
v_expr_146_ = lean_ctor_get(v_type_137_, 1);
lean_inc_ref(v_expr_146_);
lean_dec_ref_known(v_type_137_, 2);
v_type_137_ = v_expr_146_;
goto _start;
}
case 7:
{
lean_object* v_binderName_148_; lean_object* v_binderType_149_; lean_object* v_body_150_; uint8_t v_binderInfo_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_binderName_148_ = lean_ctor_get(v_type_137_, 0);
lean_inc(v_binderName_148_);
v_binderType_149_ = lean_ctor_get(v_type_137_, 1);
lean_inc_ref(v_binderType_149_);
v_body_150_ = lean_ctor_get(v_type_137_, 2);
lean_inc_ref(v_body_150_);
v_binderInfo_151_ = lean_ctor_get_uint8(v_type_137_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_137_, 3);
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_array_get_size(v_fvars_136_);
lean_inc_ref(v_fvars_136_);
v___x_154_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_binderType_149_, v___x_152_, v___x_153_, v_fvars_136_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_156_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v___x_154_, 1);
v___x_156_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v___x_158_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_a_157_);
lean_dec_ref_known(v___x_156_, 1);
lean_inc_ref(v_mkName_131_);
lean_inc(v_a_143_);
lean_inc_ref(v_a_142_);
lean_inc(v_a_141_);
lean_inc_ref(v_a_140_);
lean_inc(v_i_133_);
lean_inc_ref(v_lctx_134_);
v___x_158_ = lean_apply_8(v_mkName_131_, v_lctx_134_, v_binderName_148_, v_i_133_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, lean_box(0));
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_158_, 1);
v___x_160_ = 0;
lean_inc(v_a_155_);
lean_inc(v_a_157_);
v___x_161_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_134_, v_a_157_, v_a_159_, v_a_155_, v_binderInfo_151_, v___x_160_);
v___x_162_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(v_a_157_, v_a_139_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc_n(v_a_163_, 2);
lean_dec_ref_known(v___x_162_, 1);
v___x_164_ = lean_array_push(v_fvars_136_, v_a_163_);
lean_inc_ref(v_updateLocalInsts_132_);
v___x_165_ = lean_apply_3(v_updateLocalInsts_132_, v_localInsts_135_, v_a_163_, v_a_155_);
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_nat_add(v_i_133_, v___x_166_);
lean_dec(v_i_133_);
v_i_133_ = v___x_167_;
v_lctx_134_ = v___x_161_;
v_localInsts_135_ = v___x_165_;
v_fvars_136_ = v___x_164_;
v_type_137_ = v_body_150_;
goto _start;
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
lean_dec_ref(v___x_161_);
lean_dec(v_a_155_);
lean_dec_ref(v_body_150_);
lean_dec_ref(v_fvars_136_);
lean_dec_ref(v_localInsts_135_);
lean_dec(v_i_133_);
lean_dec_ref(v_updateLocalInsts_132_);
lean_dec_ref(v_mkName_131_);
lean_dec_ref(v_finalize_130_);
v_a_169_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_162_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_162_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_dec(v_a_157_);
lean_dec(v_a_155_);
lean_dec_ref(v_body_150_);
lean_dec_ref(v_fvars_136_);
lean_dec_ref(v_localInsts_135_);
lean_dec_ref(v_lctx_134_);
lean_dec(v_i_133_);
lean_dec_ref(v_updateLocalInsts_132_);
lean_dec_ref(v_mkName_131_);
lean_dec_ref(v_finalize_130_);
v_a_177_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_158_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_158_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec(v_a_155_);
lean_dec_ref(v_body_150_);
lean_dec(v_binderName_148_);
lean_dec_ref(v_fvars_136_);
lean_dec_ref(v_localInsts_135_);
lean_dec_ref(v_lctx_134_);
lean_dec(v_i_133_);
lean_dec_ref(v_updateLocalInsts_132_);
lean_dec_ref(v_mkName_131_);
lean_dec_ref(v_finalize_130_);
v_a_185_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_156_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_156_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec_ref(v_body_150_);
lean_dec(v_binderName_148_);
lean_dec_ref(v_fvars_136_);
lean_dec_ref(v_localInsts_135_);
lean_dec_ref(v_lctx_134_);
lean_dec(v_i_133_);
lean_dec_ref(v_updateLocalInsts_132_);
lean_dec_ref(v_mkName_131_);
lean_dec_ref(v_finalize_130_);
v_a_193_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_154_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_154_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
case 8:
{
lean_object* v_declName_201_; lean_object* v_type_202_; lean_object* v_value_203_; lean_object* v_body_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_declName_201_ = lean_ctor_get(v_type_137_, 0);
lean_inc(v_declName_201_);
v_type_202_ = lean_ctor_get(v_type_137_, 1);
lean_inc_ref(v_type_202_);
v_value_203_ = lean_ctor_get(v_type_137_, 2);
lean_inc_ref(v_value_203_);
v_body_204_ = lean_ctor_get(v_type_137_, 3);
lean_inc_ref(v_body_204_);
lean_dec_ref_known(v_type_137_, 4);
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_array_get_size(v_fvars_136_);
lean_inc_ref(v_fvars_136_);
v___x_207_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_202_, v___x_205_, v___x_206_, v_fvars_136_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_209_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_207_, 1);
lean_inc_ref(v_fvars_136_);
v___x_209_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_value_203_, v___x_205_, v___x_206_, v_fvars_136_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_211_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_209_, 1);
v___x_211_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_213_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
lean_inc_ref(v_mkName_131_);
lean_inc(v_a_143_);
lean_inc_ref(v_a_142_);
lean_inc(v_a_141_);
lean_inc_ref(v_a_140_);
lean_inc(v_i_133_);
lean_inc_ref(v_lctx_134_);
v___x_213_ = lean_apply_8(v_mkName_131_, v_lctx_134_, v_declName_201_, v_i_133_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, lean_box(0));
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_213_, 1);
v___x_215_ = 0;
lean_inc(v_a_208_);
lean_inc(v_a_212_);
v___x_216_ = l_Lean_LocalContext_mkLetDecl(v_lctx_134_, v_a_212_, v_a_214_, v_a_208_, v_a_210_, v___x_145_, v___x_215_);
v___x_217_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(v_a_212_, v_a_139_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc_n(v_a_218_, 2);
lean_dec_ref_known(v___x_217_, 1);
v___x_219_ = lean_array_push(v_fvars_136_, v_a_218_);
lean_inc_ref(v_updateLocalInsts_132_);
v___x_220_ = lean_apply_3(v_updateLocalInsts_132_, v_localInsts_135_, v_a_218_, v_a_208_);
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_add(v_i_133_, v___x_221_);
lean_dec(v_i_133_);
v_i_133_ = v___x_222_;
v_lctx_134_ = v___x_216_;
v_localInsts_135_ = v___x_220_;
v_fvars_136_ = v___x_219_;
v_type_137_ = v_body_204_;
goto _start;
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
lean_dec_ref(v___x_216_);
lean_dec(v_a_208_);
lean_dec_ref(v_body_204_);
lean_dec_ref(v_fvars_136_);
lean_dec_ref(v_localInsts_135_);
lean_dec(v_i_133_);
lean_dec_ref(v_updateLocalInsts_132_);
lean_dec_ref(v_mkName_131_);
lean_dec_ref(v_finalize_130_);
v_a_224_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_217_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_217_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_dec(v_a_212_);
lean_dec(v_a_210_);
lean_dec(v_a_208_);
lean_dec_ref(v_body_204_);
lean_dec_ref(v_fvars_136_);
lean_dec_ref(v_localInsts_135_);
lean_dec_ref(v_lctx_134_);
lean_dec(v_i_133_);
lean_dec_ref(v_updateLocalInsts_132_);
lean_dec_ref(v_mkName_131_);
lean_dec_ref(v_finalize_130_);
v_a_232_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_213_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_213_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec(v_a_210_);
lean_dec(v_a_208_);
lean_dec_ref(v_body_204_);
lean_dec(v_declName_201_);
lean_dec_ref(v_fvars_136_);
lean_dec_ref(v_localInsts_135_);
lean_dec_ref(v_lctx_134_);
lean_dec(v_i_133_);
lean_dec_ref(v_updateLocalInsts_132_);
lean_dec_ref(v_mkName_131_);
lean_dec_ref(v_finalize_130_);
v_a_240_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_211_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_211_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
lean_dec(v_a_208_);
lean_dec_ref(v_body_204_);
lean_dec(v_declName_201_);
lean_dec_ref(v_fvars_136_);
lean_dec_ref(v_localInsts_135_);
lean_dec_ref(v_lctx_134_);
lean_dec(v_i_133_);
lean_dec_ref(v_updateLocalInsts_132_);
lean_dec_ref(v_mkName_131_);
lean_dec_ref(v_finalize_130_);
v_a_248_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_209_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_209_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec_ref(v_body_204_);
lean_dec_ref(v_value_203_);
lean_dec(v_declName_201_);
lean_dec_ref(v_fvars_136_);
lean_dec_ref(v_localInsts_135_);
lean_dec_ref(v_lctx_134_);
lean_dec(v_i_133_);
lean_dec_ref(v_updateLocalInsts_132_);
lean_dec_ref(v_mkName_131_);
lean_dec_ref(v_finalize_130_);
v_a_256_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_207_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_207_);
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
default: 
{
lean_object* v___x_264_; 
lean_dec(v_i_133_);
lean_dec_ref(v_updateLocalInsts_132_);
lean_dec_ref(v_mkName_131_);
lean_inc(v_a_143_);
lean_inc_ref(v_a_142_);
lean_inc(v_a_141_);
lean_inc_ref(v_a_140_);
lean_inc(v_a_139_);
lean_inc_ref(v_a_138_);
v___x_264_ = lean_apply_11(v_finalize_130_, v_lctx_134_, v_localInsts_135_, v_fvars_136_, v_type_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, lean_box(0));
return v___x_264_;
}
}
}
else
{
lean_object* v___x_265_; 
lean_dec(v_i_133_);
lean_dec_ref(v_updateLocalInsts_132_);
lean_dec_ref(v_mkName_131_);
lean_inc(v_a_143_);
lean_inc_ref(v_a_142_);
lean_inc(v_a_141_);
lean_inc_ref(v_a_140_);
lean_inc(v_a_139_);
lean_inc_ref(v_a_138_);
v___x_265_ = lean_apply_11(v_finalize_130_, v_lctx_134_, v_localInsts_135_, v_fvars_136_, v_type_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, lean_box(0));
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit___boxed(lean_object* v_max_266_, lean_object* v_finalize_267_, lean_object* v_mkName_268_, lean_object* v_updateLocalInsts_269_, lean_object* v_i_270_, lean_object* v_lctx_271_, lean_object* v_localInsts_272_, lean_object* v_fvars_273_, lean_object* v_type_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(v_max_266_, v_finalize_267_, v_mkName_268_, v_updateLocalInsts_269_, v_i_270_, v_lctx_271_, v_localInsts_272_, v_fvars_273_, v_type_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_max_266_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0(lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(v___y_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___boxed(lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0(v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(lean_object* v_names_299_, uint8_t v_hygienic_300_, lean_object* v_lctx_301_, lean_object* v_binderName_302_, lean_object* v_i_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = lean_array_get_size(v_names_299_);
v___x_310_ = lean_nat_dec_lt(v_i_303_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_301_, v_binderName_302_, v_hygienic_300_, v___y_306_, v___y_307_);
return v___x_311_;
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec(v_binderName_302_);
v___x_312_ = lean_array_fget_borrowed(v_names_299_, v_i_303_);
lean_inc(v___x_312_);
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed(lean_object* v_names_314_, lean_object* v_hygienic_315_, lean_object* v_lctx_316_, lean_object* v_binderName_317_, lean_object* v_i_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
uint8_t v_hygienic_boxed_324_; lean_object* v_res_325_; 
v_hygienic_boxed_324_ = lean_unbox(v_hygienic_315_);
v_res_325_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(v_names_314_, v_hygienic_boxed_324_, v_lctx_316_, v_binderName_317_, v_i_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v_i_318_);
lean_dec_ref(v_lctx_316_);
lean_dec_ref(v_names_314_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(lean_object* v_env_326_, lean_object* v_localInsts_327_, lean_object* v_fvar_328_, lean_object* v_type_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_Meta_Sym_isClass_x3f(v_env_326_, v_type_329_);
if (lean_obj_tag(v___x_330_) == 1)
{
lean_object* v_val_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_val_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_val_331_);
lean_dec_ref_known(v___x_330_, 1);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_val_331_);
lean_ctor_set(v___x_332_, 1, v_fvar_328_);
v___x_333_ = lean_array_push(v_localInsts_327_, v___x_332_);
return v___x_333_;
}
else
{
lean_dec(v___x_330_);
lean_dec_ref(v_fvar_328_);
return v_localInsts_327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed(lean_object* v_env_334_, lean_object* v_localInsts_335_, lean_object* v_fvar_336_, lean_object* v_type_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(v_env_334_, v_localInsts_335_, v_fvar_336_, v_type_337_);
lean_dec_ref(v_type_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
lean_object* v_ks_343_; lean_object* v_vs_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_368_; 
v_ks_343_ = lean_ctor_get(v_x_339_, 0);
v_vs_344_ = lean_ctor_get(v_x_339_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_x_339_);
if (v_isSharedCheck_368_ == 0)
{
v___x_346_ = v_x_339_;
v_isShared_347_ = v_isSharedCheck_368_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_vs_344_);
lean_inc(v_ks_343_);
lean_dec(v_x_339_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_368_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_array_get_size(v_ks_343_);
v___x_349_ = lean_nat_dec_lt(v_x_340_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
lean_dec(v_x_340_);
v___x_350_ = lean_array_push(v_ks_343_, v_x_341_);
v___x_351_ = lean_array_push(v_vs_344_, v_x_342_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_351_);
lean_ctor_set(v___x_346_, 0, v___x_350_);
v___x_353_ = v___x_346_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
else
{
lean_object* v_k_x27_355_; uint8_t v___x_356_; 
v_k_x27_355_ = lean_array_fget_borrowed(v_ks_343_, v_x_340_);
v___x_356_ = l_Lean_instBEqMVarId_beq(v_x_341_, v_k_x27_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_358_; 
if (v_isShared_347_ == 0)
{
v___x_358_ = v___x_346_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_ks_343_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_vs_344_);
v___x_358_ = v_reuseFailAlloc_362_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = lean_nat_add(v_x_340_, v___x_359_);
lean_dec(v_x_340_);
v_x_339_ = v___x_358_;
v_x_340_ = v___x_360_;
goto _start;
}
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_363_ = lean_array_fset(v_ks_343_, v_x_340_, v_x_341_);
v___x_364_ = lean_array_fset(v_vs_344_, v_x_340_, v_x_342_);
lean_dec(v_x_340_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_364_);
lean_ctor_set(v___x_346_, 0, v___x_363_);
v___x_366_ = v___x_346_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_n_369_, lean_object* v_k_370_, lean_object* v_v_371_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_n_369_, v___x_372_, v_k_370_, v_v_371_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_375_, size_t v_x_376_, size_t v_x_377_, lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
if (lean_obj_tag(v_x_375_) == 0)
{
lean_object* v_es_380_; size_t v___x_381_; size_t v___x_382_; lean_object* v_j_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v_es_380_ = lean_ctor_get(v_x_375_, 0);
v___x_381_ = ((size_t)31ULL);
v___x_382_ = lean_usize_land(v_x_376_, v___x_381_);
v_j_383_ = lean_usize_to_nat(v___x_382_);
v___x_384_ = lean_array_get_size(v_es_380_);
v___x_385_ = lean_nat_dec_lt(v_j_383_, v___x_384_);
if (v___x_385_ == 0)
{
lean_dec(v_j_383_);
lean_dec(v_x_379_);
lean_dec(v_x_378_);
return v_x_375_;
}
else
{
lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_424_; 
lean_inc_ref(v_es_380_);
v_isSharedCheck_424_ = !lean_is_exclusive(v_x_375_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v_x_375_, 0);
lean_dec(v_unused_425_);
v___x_387_ = v_x_375_;
v_isShared_388_ = v_isSharedCheck_424_;
goto v_resetjp_386_;
}
else
{
lean_dec(v_x_375_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_424_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_v_389_; lean_object* v___x_390_; lean_object* v_xs_x27_391_; lean_object* v___y_393_; 
v_v_389_ = lean_array_fget(v_es_380_, v_j_383_);
v___x_390_ = lean_box(0);
v_xs_x27_391_ = lean_array_fset(v_es_380_, v_j_383_, v___x_390_);
switch(lean_obj_tag(v_v_389_))
{
case 0:
{
lean_object* v_key_398_; lean_object* v_val_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_409_; 
v_key_398_ = lean_ctor_get(v_v_389_, 0);
v_val_399_ = lean_ctor_get(v_v_389_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v_v_389_);
if (v_isSharedCheck_409_ == 0)
{
v___x_401_ = v_v_389_;
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_val_399_);
lean_inc(v_key_398_);
lean_dec(v_v_389_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
uint8_t v___x_403_; 
v___x_403_ = l_Lean_instBEqMVarId_beq(v_x_378_, v_key_398_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_del_object(v___x_401_);
v___x_404_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_398_, v_val_399_, v_x_378_, v_x_379_);
v___x_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
v___y_393_ = v___x_405_;
goto v___jp_392_;
}
else
{
lean_object* v___x_407_; 
lean_dec(v_val_399_);
lean_dec(v_key_398_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 1, v_x_379_);
lean_ctor_set(v___x_401_, 0, v_x_378_);
v___x_407_ = v___x_401_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_x_378_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_x_379_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
v___y_393_ = v___x_407_;
goto v___jp_392_;
}
}
}
}
case 1:
{
lean_object* v_node_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_422_; 
v_node_410_ = lean_ctor_get(v_v_389_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v_v_389_);
if (v_isSharedCheck_422_ == 0)
{
v___x_412_ = v_v_389_;
v_isShared_413_ = v_isSharedCheck_422_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_node_410_);
lean_dec(v_v_389_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_422_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
size_t v___x_414_; size_t v___x_415_; size_t v___x_416_; size_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_414_ = ((size_t)5ULL);
v___x_415_ = lean_usize_shift_right(v_x_376_, v___x_414_);
v___x_416_ = ((size_t)1ULL);
v___x_417_ = lean_usize_add(v_x_377_, v___x_416_);
v___x_418_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_node_410_, v___x_415_, v___x_417_, v_x_378_, v_x_379_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_418_);
v___x_420_ = v___x_412_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
v___y_393_ = v___x_420_;
goto v___jp_392_;
}
}
}
default: 
{
lean_object* v___x_423_; 
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v_x_378_);
lean_ctor_set(v___x_423_, 1, v_x_379_);
v___y_393_ = v___x_423_;
goto v___jp_392_;
}
}
v___jp_392_:
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_array_fset(v_xs_x27_391_, v_j_383_, v___y_393_);
lean_dec(v_j_383_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_394_);
v___x_396_ = v___x_387_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
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
}
else
{
lean_object* v_ks_426_; lean_object* v_vs_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_445_; 
v_ks_426_ = lean_ctor_get(v_x_375_, 0);
v_vs_427_ = lean_ctor_get(v_x_375_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_x_375_);
if (v_isSharedCheck_445_ == 0)
{
v___x_429_ = v_x_375_;
v_isShared_430_ = v_isSharedCheck_445_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_vs_427_);
lean_inc(v_ks_426_);
lean_dec(v_x_375_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_445_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_ks_426_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_vs_427_);
v___x_432_ = v_reuseFailAlloc_444_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v_newNode_433_; size_t v___x_434_; uint8_t v___x_435_; 
v_newNode_433_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(v___x_432_, v_x_378_, v_x_379_);
v___x_434_ = ((size_t)7ULL);
v___x_435_ = lean_usize_dec_le(v___x_434_, v_x_377_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_436_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_433_);
v___x_437_ = lean_unsigned_to_nat(4u);
v___x_438_ = lean_nat_dec_lt(v___x_436_, v___x_437_);
lean_dec(v___x_436_);
if (v___x_438_ == 0)
{
lean_object* v_ks_439_; lean_object* v_vs_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_ks_439_ = lean_ctor_get(v_newNode_433_, 0);
lean_inc_ref(v_ks_439_);
v_vs_440_ = lean_ctor_get(v_newNode_433_, 1);
lean_inc_ref(v_vs_440_);
lean_dec_ref(v_newNode_433_);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_443_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_377_, v_ks_439_, v_vs_440_, v___x_441_, v___x_442_);
lean_dec_ref(v_vs_440_);
lean_dec_ref(v_ks_439_);
return v___x_443_;
}
else
{
return v_newNode_433_;
}
}
else
{
return v_newNode_433_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(size_t v_depth_446_, lean_object* v_keys_447_, lean_object* v_vals_448_, lean_object* v_i_449_, lean_object* v_entries_450_){
_start:
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = lean_array_get_size(v_keys_447_);
v___x_452_ = lean_nat_dec_lt(v_i_449_, v___x_451_);
if (v___x_452_ == 0)
{
lean_dec(v_i_449_);
return v_entries_450_;
}
else
{
lean_object* v_k_453_; lean_object* v_v_454_; uint64_t v___x_455_; size_t v_h_456_; size_t v___x_457_; lean_object* v___x_458_; size_t v___x_459_; size_t v___x_460_; size_t v___x_461_; size_t v_h_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_k_453_ = lean_array_fget_borrowed(v_keys_447_, v_i_449_);
v_v_454_ = lean_array_fget_borrowed(v_vals_448_, v_i_449_);
v___x_455_ = l_Lean_instHashableMVarId_hash(v_k_453_);
v_h_456_ = lean_uint64_to_usize(v___x_455_);
v___x_457_ = ((size_t)5ULL);
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = ((size_t)1ULL);
v___x_460_ = lean_usize_sub(v_depth_446_, v___x_459_);
v___x_461_ = lean_usize_mul(v___x_457_, v___x_460_);
v_h_462_ = lean_usize_shift_right(v_h_456_, v___x_461_);
v___x_463_ = lean_nat_add(v_i_449_, v___x_458_);
lean_dec(v_i_449_);
lean_inc(v_v_454_);
lean_inc(v_k_453_);
v___x_464_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_entries_450_, v_h_462_, v_depth_446_, v_k_453_, v_v_454_);
v_i_449_ = v___x_463_;
v_entries_450_ = v___x_464_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_depth_466_, lean_object* v_keys_467_, lean_object* v_vals_468_, lean_object* v_i_469_, lean_object* v_entries_470_){
_start:
{
size_t v_depth_boxed_471_; lean_object* v_res_472_; 
v_depth_boxed_471_ = lean_unbox_usize(v_depth_466_);
lean_dec(v_depth_466_);
v_res_472_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_boxed_471_, v_keys_467_, v_vals_468_, v_i_469_, v_entries_470_);
lean_dec_ref(v_vals_468_);
lean_dec_ref(v_keys_467_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_473_, lean_object* v_x_474_, lean_object* v_x_475_, lean_object* v_x_476_, lean_object* v_x_477_){
_start:
{
size_t v_x_5167__boxed_478_; size_t v_x_5168__boxed_479_; lean_object* v_res_480_; 
v_x_5167__boxed_478_ = lean_unbox_usize(v_x_474_);
lean_dec(v_x_474_);
v_x_5168__boxed_479_ = lean_unbox_usize(v_x_475_);
lean_dec(v_x_475_);
v_res_480_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_473_, v_x_5167__boxed_478_, v_x_5168__boxed_479_, v_x_476_, v_x_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
uint64_t v___x_484_; size_t v___x_485_; size_t v___x_486_; lean_object* v___x_487_; 
v___x_484_ = l_Lean_instHashableMVarId_hash(v_x_482_);
v___x_485_ = lean_uint64_to_usize(v___x_484_);
v___x_486_ = ((size_t)1ULL);
v___x_487_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_481_, v___x_485_, v___x_486_, v_x_482_, v_x_483_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(lean_object* v_mvarId_488_, lean_object* v_val_489_, lean_object* v___y_490_){
_start:
{
lean_object* v___x_492_; lean_object* v_mctx_493_; lean_object* v_cache_494_; lean_object* v_zetaDeltaFVarIds_495_; lean_object* v_postponed_496_; lean_object* v_diag_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_526_; 
v___x_492_ = lean_st_ref_take(v___y_490_);
v_mctx_493_ = lean_ctor_get(v___x_492_, 0);
v_cache_494_ = lean_ctor_get(v___x_492_, 1);
v_zetaDeltaFVarIds_495_ = lean_ctor_get(v___x_492_, 2);
v_postponed_496_ = lean_ctor_get(v___x_492_, 3);
v_diag_497_ = lean_ctor_get(v___x_492_, 4);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_526_ == 0)
{
v___x_499_ = v___x_492_;
v_isShared_500_ = v_isSharedCheck_526_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_diag_497_);
lean_inc(v_postponed_496_);
lean_inc(v_zetaDeltaFVarIds_495_);
lean_inc(v_cache_494_);
lean_inc(v_mctx_493_);
lean_dec(v___x_492_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_526_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v_depth_501_; lean_object* v_levelAssignDepth_502_; lean_object* v_lmvarCounter_503_; lean_object* v_mvarCounter_504_; lean_object* v_lDecls_505_; lean_object* v_decls_506_; lean_object* v_userNames_507_; lean_object* v_lAssignment_508_; lean_object* v_eAssignment_509_; lean_object* v_dAssignment_510_; lean_object* v_instanceTypedMVars_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_525_; 
v_depth_501_ = lean_ctor_get(v_mctx_493_, 0);
v_levelAssignDepth_502_ = lean_ctor_get(v_mctx_493_, 1);
v_lmvarCounter_503_ = lean_ctor_get(v_mctx_493_, 2);
v_mvarCounter_504_ = lean_ctor_get(v_mctx_493_, 3);
v_lDecls_505_ = lean_ctor_get(v_mctx_493_, 4);
v_decls_506_ = lean_ctor_get(v_mctx_493_, 5);
v_userNames_507_ = lean_ctor_get(v_mctx_493_, 6);
v_lAssignment_508_ = lean_ctor_get(v_mctx_493_, 7);
v_eAssignment_509_ = lean_ctor_get(v_mctx_493_, 8);
v_dAssignment_510_ = lean_ctor_get(v_mctx_493_, 9);
v_instanceTypedMVars_511_ = lean_ctor_get(v_mctx_493_, 10);
v_isSharedCheck_525_ = !lean_is_exclusive(v_mctx_493_);
if (v_isSharedCheck_525_ == 0)
{
v___x_513_ = v_mctx_493_;
v_isShared_514_ = v_isSharedCheck_525_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_instanceTypedMVars_511_);
lean_inc(v_dAssignment_510_);
lean_inc(v_eAssignment_509_);
lean_inc(v_lAssignment_508_);
lean_inc(v_userNames_507_);
lean_inc(v_decls_506_);
lean_inc(v_lDecls_505_);
lean_inc(v_mvarCounter_504_);
lean_inc(v_lmvarCounter_503_);
lean_inc(v_levelAssignDepth_502_);
lean_inc(v_depth_501_);
lean_dec(v_mctx_493_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_525_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_515_ = lean_box(0);
v___x_516_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_eAssignment_509_, v_mvarId_488_, v_val_489_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 8, v___x_516_);
v___x_518_ = v___x_513_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_depth_501_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_levelAssignDepth_502_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_lmvarCounter_503_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v_mvarCounter_504_);
lean_ctor_set(v_reuseFailAlloc_524_, 4, v_lDecls_505_);
lean_ctor_set(v_reuseFailAlloc_524_, 5, v_decls_506_);
lean_ctor_set(v_reuseFailAlloc_524_, 6, v_userNames_507_);
lean_ctor_set(v_reuseFailAlloc_524_, 7, v_lAssignment_508_);
lean_ctor_set(v_reuseFailAlloc_524_, 8, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_524_, 9, v_dAssignment_510_);
lean_ctor_set(v_reuseFailAlloc_524_, 10, v_instanceTypedMVars_511_);
v___x_518_ = v_reuseFailAlloc_524_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_520_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_518_);
v___x_520_ = v___x_499_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_cache_494_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_zetaDeltaFVarIds_495_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v_postponed_496_);
lean_ctor_set(v_reuseFailAlloc_523_, 4, v_diag_497_);
v___x_520_ = v_reuseFailAlloc_523_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_st_ref_put(v___y_490_, v___x_520_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_515_);
return v___x_522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg___boxed(lean_object* v_mvarId_527_, lean_object* v_val_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_527_, v_val_528_, v___y_529_);
lean_dec(v___y_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(lean_object* v_mvarId_532_, lean_object* v_fvars_533_, lean_object* v_mvarIdPending_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___x_537_; lean_object* v_mctx_538_; lean_object* v_cache_539_; lean_object* v_zetaDeltaFVarIds_540_; lean_object* v_postponed_541_; lean_object* v_diag_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_572_; 
v___x_537_ = lean_st_ref_take(v___y_535_);
v_mctx_538_ = lean_ctor_get(v___x_537_, 0);
v_cache_539_ = lean_ctor_get(v___x_537_, 1);
v_zetaDeltaFVarIds_540_ = lean_ctor_get(v___x_537_, 2);
v_postponed_541_ = lean_ctor_get(v___x_537_, 3);
v_diag_542_ = lean_ctor_get(v___x_537_, 4);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_572_ == 0)
{
v___x_544_ = v___x_537_;
v_isShared_545_ = v_isSharedCheck_572_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_diag_542_);
lean_inc(v_postponed_541_);
lean_inc(v_zetaDeltaFVarIds_540_);
lean_inc(v_cache_539_);
lean_inc(v_mctx_538_);
lean_dec(v___x_537_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_572_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v_depth_546_; lean_object* v_levelAssignDepth_547_; lean_object* v_lmvarCounter_548_; lean_object* v_mvarCounter_549_; lean_object* v_lDecls_550_; lean_object* v_decls_551_; lean_object* v_userNames_552_; lean_object* v_lAssignment_553_; lean_object* v_eAssignment_554_; lean_object* v_dAssignment_555_; lean_object* v_instanceTypedMVars_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_571_; 
v_depth_546_ = lean_ctor_get(v_mctx_538_, 0);
v_levelAssignDepth_547_ = lean_ctor_get(v_mctx_538_, 1);
v_lmvarCounter_548_ = lean_ctor_get(v_mctx_538_, 2);
v_mvarCounter_549_ = lean_ctor_get(v_mctx_538_, 3);
v_lDecls_550_ = lean_ctor_get(v_mctx_538_, 4);
v_decls_551_ = lean_ctor_get(v_mctx_538_, 5);
v_userNames_552_ = lean_ctor_get(v_mctx_538_, 6);
v_lAssignment_553_ = lean_ctor_get(v_mctx_538_, 7);
v_eAssignment_554_ = lean_ctor_get(v_mctx_538_, 8);
v_dAssignment_555_ = lean_ctor_get(v_mctx_538_, 9);
v_instanceTypedMVars_556_ = lean_ctor_get(v_mctx_538_, 10);
v_isSharedCheck_571_ = !lean_is_exclusive(v_mctx_538_);
if (v_isSharedCheck_571_ == 0)
{
v___x_558_ = v_mctx_538_;
v_isShared_559_ = v_isSharedCheck_571_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_instanceTypedMVars_556_);
lean_inc(v_dAssignment_555_);
lean_inc(v_eAssignment_554_);
lean_inc(v_lAssignment_553_);
lean_inc(v_userNames_552_);
lean_inc(v_decls_551_);
lean_inc(v_lDecls_550_);
lean_inc(v_mvarCounter_549_);
lean_inc(v_lmvarCounter_548_);
lean_inc(v_levelAssignDepth_547_);
lean_inc(v_depth_546_);
lean_dec(v_mctx_538_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_571_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_560_ = lean_box(0);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v_fvars_533_);
lean_ctor_set(v___x_561_, 1, v_mvarIdPending_534_);
v___x_562_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_dAssignment_555_, v_mvarId_532_, v___x_561_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 9, v___x_562_);
v___x_564_ = v___x_558_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_depth_546_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_levelAssignDepth_547_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v_lmvarCounter_548_);
lean_ctor_set(v_reuseFailAlloc_570_, 3, v_mvarCounter_549_);
lean_ctor_set(v_reuseFailAlloc_570_, 4, v_lDecls_550_);
lean_ctor_set(v_reuseFailAlloc_570_, 5, v_decls_551_);
lean_ctor_set(v_reuseFailAlloc_570_, 6, v_userNames_552_);
lean_ctor_set(v_reuseFailAlloc_570_, 7, v_lAssignment_553_);
lean_ctor_set(v_reuseFailAlloc_570_, 8, v_eAssignment_554_);
lean_ctor_set(v_reuseFailAlloc_570_, 9, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_570_, 10, v_instanceTypedMVars_556_);
v___x_564_ = v_reuseFailAlloc_570_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_566_; 
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_564_);
v___x_566_ = v___x_544_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_cache_539_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_zetaDeltaFVarIds_540_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_postponed_541_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v_diag_542_);
v___x_566_ = v_reuseFailAlloc_569_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_st_ref_put(v___y_535_, v___x_566_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_560_);
return v___x_568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg___boxed(lean_object* v_mvarId_573_, lean_object* v_fvars_574_, lean_object* v_mvarIdPending_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_573_, v_fvars_574_, v_mvarIdPending_575_, v___y_576_);
lean_dec(v___y_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(lean_object* v___x_579_, lean_object* v_userName_580_, lean_object* v_lctx_581_, lean_object* v_localInstances_582_, lean_object* v_type_583_, lean_object* v_max_584_, lean_object* v_mvarId_585_, lean_object* v_lctx_586_, lean_object* v_localInsts_587_, lean_object* v_fvars_588_, lean_object* v_type_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_597_ = lean_array_get_size(v_fvars_588_);
v___x_598_ = lean_nat_dec_eq(v___x_597_, v___x_579_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
lean_inc_ref(v_fvars_588_);
lean_inc(v___x_579_);
v___x_599_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_589_, v___x_579_, v___x_597_, v_fvars_588_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; uint8_t v___x_601_; lean_object* v___x_602_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v___x_601_ = 2;
lean_inc(v___x_579_);
v___x_602_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_586_, v_localInsts_587_, v_a_600_, v___x_601_, v_userName_580_, v___x_579_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_604_; lean_object* v___y_606_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v___x_604_ = l_Lean_Expr_mvarId_x21(v_a_603_);
lean_dec(v_a_603_);
v___x_616_ = lean_box(0);
lean_inc(v___x_579_);
lean_inc_ref(v_type_583_);
v___x_617_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_581_, v_localInstances_582_, v_type_583_, v___x_601_, v___x_616_, v___x_579_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc_n(v_a_618_, 2);
lean_dec_ref_known(v___x_617_, 1);
v___x_619_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkAppBVars(v_a_618_, v___x_597_);
v___x_620_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(v_max_584_, v___x_579_, v_type_583_, v___x_619_);
lean_dec_ref(v___x_619_);
lean_dec(v___x_579_);
v___x_621_ = l_Lean_Expr_mvarId_x21(v_a_618_);
lean_dec(v_a_618_);
lean_inc(v___x_604_);
lean_inc_ref(v_fvars_588_);
v___x_622_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v___x_621_, v_fvars_588_, v___x_604_, v___y_593_);
lean_dec_ref(v___x_622_);
v___x_623_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_585_, v___x_620_, v___y_593_);
v___y_606_ = v___x_623_;
goto v___jp_605_;
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec(v___x_604_);
lean_dec_ref(v_fvars_588_);
lean_dec(v_mvarId_585_);
lean_dec_ref(v_type_583_);
lean_dec(v___x_579_);
v_a_624_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_617_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_617_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
v___jp_605_:
{
lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_614_; 
v_isSharedCheck_614_ = !lean_is_exclusive(v___y_606_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v___y_606_, 0);
lean_dec(v_unused_615_);
v___x_608_ = v___y_606_;
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
else
{
lean_dec(v___y_606_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v_fvars_588_);
lean_ctor_set(v___x_610_, 1, v___x_604_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_610_);
v___x_612_ = v___x_608_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec_ref(v_fvars_588_);
lean_dec(v_mvarId_585_);
lean_dec_ref(v_type_583_);
lean_dec_ref(v_localInstances_582_);
lean_dec_ref(v_lctx_581_);
lean_dec(v___x_579_);
v_a_632_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_602_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_602_);
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
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v_fvars_588_);
lean_dec_ref(v_localInsts_587_);
lean_dec_ref(v_lctx_586_);
lean_dec(v_mvarId_585_);
lean_dec_ref(v_type_583_);
lean_dec_ref(v_localInstances_582_);
lean_dec_ref(v_lctx_581_);
lean_dec(v_userName_580_);
lean_dec(v___x_579_);
v_a_640_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_599_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_599_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
lean_dec_ref(v_type_589_);
lean_dec_ref(v_fvars_588_);
lean_dec_ref(v_localInsts_587_);
lean_dec_ref(v_lctx_586_);
lean_dec_ref(v_type_583_);
lean_dec_ref(v_localInstances_582_);
lean_dec_ref(v_lctx_581_);
lean_dec(v_userName_580_);
v___x_648_ = lean_mk_empty_array_with_capacity(v___x_579_);
lean_dec(v___x_579_);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v_mvarId_585_);
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2___boxed(lean_object** _args){
lean_object* v___x_651_ = _args[0];
lean_object* v_userName_652_ = _args[1];
lean_object* v_lctx_653_ = _args[2];
lean_object* v_localInstances_654_ = _args[3];
lean_object* v_type_655_ = _args[4];
lean_object* v_max_656_ = _args[5];
lean_object* v_mvarId_657_ = _args[6];
lean_object* v_lctx_658_ = _args[7];
lean_object* v_localInsts_659_ = _args[8];
lean_object* v_fvars_660_ = _args[9];
lean_object* v_type_661_ = _args[10];
lean_object* v___y_662_ = _args[11];
lean_object* v___y_663_ = _args[12];
lean_object* v___y_664_ = _args[13];
lean_object* v___y_665_ = _args[14];
lean_object* v___y_666_ = _args[15];
lean_object* v___y_667_ = _args[16];
lean_object* v___y_668_ = _args[17];
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(v___x_651_, v_userName_652_, v_lctx_653_, v_localInstances_654_, v_type_655_, v_max_656_, v_mvarId_657_, v_lctx_658_, v_localInsts_659_, v_fvars_660_, v_type_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v_max_656_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(size_t v_sz_670_, size_t v_i_671_, lean_object* v_bs_672_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = lean_usize_dec_lt(v_i_671_, v_sz_670_);
if (v___x_673_ == 0)
{
return v_bs_672_;
}
else
{
lean_object* v_v_674_; lean_object* v___x_675_; lean_object* v_bs_x27_676_; lean_object* v___x_677_; size_t v___x_678_; size_t v___x_679_; lean_object* v___x_680_; 
v_v_674_ = lean_array_uget(v_bs_672_, v_i_671_);
v___x_675_ = lean_unsigned_to_nat(0u);
v_bs_x27_676_ = lean_array_uset(v_bs_672_, v_i_671_, v___x_675_);
v___x_677_ = l_Lean_Expr_fvarId_x21(v_v_674_);
lean_dec(v_v_674_);
v___x_678_ = ((size_t)1ULL);
v___x_679_ = lean_usize_add(v_i_671_, v___x_678_);
v___x_680_ = lean_array_uset(v_bs_x27_676_, v_i_671_, v___x_677_);
v_i_671_ = v___x_679_;
v_bs_672_ = v___x_680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2___boxed(lean_object* v_sz_682_, lean_object* v_i_683_, lean_object* v_bs_684_){
_start:
{
size_t v_sz_boxed_685_; size_t v_i_boxed_686_; lean_object* v_res_687_; 
v_sz_boxed_685_ = lean_unbox_usize(v_sz_682_);
lean_dec(v_sz_682_);
v_i_boxed_686_ = lean_unbox_usize(v_i_683_);
lean_dec(v_i_683_);
v_res_687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_boxed_685_, v_i_boxed_686_, v_bs_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(lean_object* v_mvarId_692_, lean_object* v_max_693_, lean_object* v_names_694_, uint8_t v_hygienic_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_nat_dec_eq(v_max_693_, v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___f_706_; lean_object* v___x_707_; lean_object* v_env_708_; lean_object* v___f_709_; lean_object* v___x_710_; 
v___x_705_ = lean_box(v_hygienic_695_);
v___f_706_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed), 10, 2);
lean_closure_set(v___f_706_, 0, v_names_694_);
lean_closure_set(v___f_706_, 1, v___x_705_);
v___x_707_ = lean_st_ref_get(v_a_701_);
v_env_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc_ref(v_env_708_);
lean_dec(v___x_707_);
v___f_709_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed), 4, 1);
lean_closure_set(v___f_709_, 0, v_env_708_);
lean_inc(v_mvarId_692_);
v___x_710_ = l_Lean_MVarId_getDecl(v_mvarId_692_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v_userName_712_; lean_object* v_lctx_713_; lean_object* v_type_714_; lean_object* v_localInstances_715_; lean_object* v___f_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v_userName_712_ = lean_ctor_get(v_a_711_, 0);
lean_inc(v_userName_712_);
v_lctx_713_ = lean_ctor_get(v_a_711_, 1);
lean_inc_ref_n(v_lctx_713_, 2);
v_type_714_ = lean_ctor_get(v_a_711_, 2);
lean_inc_ref_n(v_type_714_, 2);
v_localInstances_715_ = lean_ctor_get(v_a_711_, 4);
lean_inc_ref_n(v_localInstances_715_, 2);
lean_dec(v_a_711_);
lean_inc(v_max_693_);
v___f_716_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2___boxed), 18, 7);
lean_closure_set(v___f_716_, 0, v___x_703_);
lean_closure_set(v___f_716_, 1, v_userName_712_);
lean_closure_set(v___f_716_, 2, v_lctx_713_);
lean_closure_set(v___f_716_, 3, v_localInstances_715_);
lean_closure_set(v___f_716_, 4, v_type_714_);
lean_closure_set(v___f_716_, 5, v_max_693_);
lean_closure_set(v___f_716_, 6, v_mvarId_692_);
v___x_717_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0));
v___x_718_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(v_max_693_, v___f_716_, v___f_706_, v___f_709_, v___x_703_, v_lctx_713_, v_localInstances_715_, v___x_717_, v_type_714_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
lean_dec(v_max_693_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_738_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_738_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_738_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_738_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v_fst_723_; lean_object* v_snd_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_737_; 
v_fst_723_ = lean_ctor_get(v_a_719_, 0);
v_snd_724_ = lean_ctor_get(v_a_719_, 1);
v_isSharedCheck_737_ = !lean_is_exclusive(v_a_719_);
if (v_isSharedCheck_737_ == 0)
{
v___x_726_ = v_a_719_;
v_isShared_727_ = v_isSharedCheck_737_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_snd_724_);
lean_inc(v_fst_723_);
lean_dec(v_a_719_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_737_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
size_t v_sz_728_; size_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v_sz_728_ = lean_array_size(v_fst_723_);
v___x_729_ = ((size_t)0ULL);
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_728_, v___x_729_, v_fst_723_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_730_);
v___x_732_ = v___x_726_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_snd_724_);
v___x_732_ = v_reuseFailAlloc_736_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_734_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_732_);
v___x_734_ = v___x_721_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
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
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
v_a_739_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_718_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_718_);
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
lean_dec_ref(v___f_709_);
lean_dec_ref(v___f_706_);
lean_dec(v_max_693_);
lean_dec(v_mvarId_692_);
v_a_747_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_710_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_710_);
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
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec_ref(v_names_694_);
lean_dec(v_max_693_);
v___x_755_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v_mvarId_692_);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___boxed(lean_object* v_mvarId_758_, lean_object* v_max_759_, lean_object* v_names_760_, lean_object* v_hygienic_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
uint8_t v_hygienic_boxed_769_; lean_object* v_res_770_; 
v_hygienic_boxed_769_ = lean_unbox(v_hygienic_761_);
v_res_770_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_758_, v_max_759_, v_names_760_, v_hygienic_boxed_769_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(lean_object* v_mvarId_771_, lean_object* v_fvars_772_, lean_object* v_mvarIdPending_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_771_, v_fvars_772_, v_mvarIdPending_773_, v___y_775_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___boxed(lean_object* v_mvarId_780_, lean_object* v_fvars_781_, lean_object* v_mvarIdPending_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(v_mvarId_780_, v_fvars_781_, v_mvarIdPending_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(lean_object* v_mvarId_789_, lean_object* v_val_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_789_, v_val_790_, v___y_792_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___boxed(lean_object* v_mvarId_797_, lean_object* v_val_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(v_mvarId_797_, v_val_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0(lean_object* v_00_u03b2_805_, lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_x_806_, v_x_807_, v_x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_810_, lean_object* v_x_811_, size_t v_x_812_, size_t v_x_813_, lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_811_, v_x_812_, v_x_813_, v_x_814_, v_x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_817_, lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
size_t v_x_5728__boxed_823_; size_t v_x_5729__boxed_824_; lean_object* v_res_825_; 
v_x_5728__boxed_823_ = lean_unbox_usize(v_x_819_);
lean_dec(v_x_819_);
v_x_5729__boxed_824_ = lean_unbox_usize(v_x_820_);
lean_dec(v_x_820_);
v_res_825_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(v_00_u03b2_817_, v_x_818_, v_x_5728__boxed_823_, v_x_5729__boxed_824_, v_x_821_, v_x_822_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_826_, lean_object* v_n_827_, lean_object* v_k_828_, lean_object* v_v_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(v_n_827_, v_k_828_, v_v_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_831_, size_t v_depth_832_, lean_object* v_keys_833_, lean_object* v_vals_834_, lean_object* v_heq_835_, lean_object* v_i_836_, lean_object* v_entries_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_832_, v_keys_833_, v_vals_834_, v_i_836_, v_entries_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_839_, lean_object* v_depth_840_, lean_object* v_keys_841_, lean_object* v_vals_842_, lean_object* v_heq_843_, lean_object* v_i_844_, lean_object* v_entries_845_){
_start:
{
size_t v_depth_boxed_846_; lean_object* v_res_847_; 
v_depth_boxed_846_ = lean_unbox_usize(v_depth_840_);
lean_dec(v_depth_840_);
v_res_847_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_839_, v_depth_boxed_846_, v_keys_841_, v_vals_842_, v_heq_843_, v_i_844_, v_entries_845_);
lean_dec_ref(v_vals_842_);
lean_dec_ref(v_keys_841_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_x_849_, v_x_850_, v_x_851_, v_x_852_);
return v___x_853_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat(void){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = lean_unsigned_to_nat(1000000u);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx(lean_object* v_x_855_){
_start:
{
if (lean_obj_tag(v_x_855_) == 0)
{
lean_object* v___x_856_; 
v___x_856_ = lean_unsigned_to_nat(0u);
return v___x_856_;
}
else
{
lean_object* v___x_857_; 
v___x_857_ = lean_unsigned_to_nat(1u);
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx___boxed(lean_object* v_x_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_Meta_Sym_IntrosResult_ctorIdx(v_x_858_);
lean_dec(v_x_858_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(lean_object* v_t_860_, lean_object* v_k_861_){
_start:
{
if (lean_obj_tag(v_t_860_) == 0)
{
return v_k_861_;
}
else
{
lean_object* v_newDecls_862_; lean_object* v_mvarId_863_; lean_object* v___x_864_; 
v_newDecls_862_ = lean_ctor_get(v_t_860_, 0);
lean_inc_ref(v_newDecls_862_);
v_mvarId_863_ = lean_ctor_get(v_t_860_, 1);
lean_inc(v_mvarId_863_);
lean_dec_ref_known(v_t_860_, 2);
v___x_864_ = lean_apply_2(v_k_861_, v_newDecls_862_, v_mvarId_863_);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim(lean_object* v_motive_865_, lean_object* v_ctorIdx_866_, lean_object* v_t_867_, lean_object* v_h_868_, lean_object* v_k_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_867_, v_k_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___boxed(lean_object* v_motive_871_, lean_object* v_ctorIdx_872_, lean_object* v_t_873_, lean_object* v_h_874_, lean_object* v_k_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Meta_Sym_IntrosResult_ctorElim(v_motive_871_, v_ctorIdx_872_, v_t_873_, v_h_874_, v_k_875_);
lean_dec(v_ctorIdx_872_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim___redArg(lean_object* v_t_877_, lean_object* v_failed_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_877_, v_failed_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim(lean_object* v_motive_880_, lean_object* v_t_881_, lean_object* v_h_882_, lean_object* v_failed_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_881_, v_failed_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim___redArg(lean_object* v_t_885_, lean_object* v_goal_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_885_, v_goal_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim(lean_object* v_motive_888_, lean_object* v_t_889_, lean_object* v_h_890_, lean_object* v_goal_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_889_, v_goal_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros(lean_object* v_mvarId_893_, lean_object* v_names_894_, uint8_t v_hygienic_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_result_904_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_920_ = lean_array_get_size(v_names_894_);
v___x_921_ = lean_unsigned_to_nat(0u);
v___x_922_ = lean_nat_dec_eq(v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; 
v___x_923_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_893_, v___x_920_, v_names_894_, v_hygienic_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v___x_923_, 1);
v_result_904_ = v_a_924_;
goto v___jp_903_;
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
v_a_925_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_923_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_923_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec_ref(v_names_894_);
v___x_933_ = lean_unsigned_to_nat(1000000u);
v___x_934_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
v___x_935_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_893_, v___x_933_, v___x_934_, v_hygienic_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 1);
v_result_904_ = v_a_936_;
goto v___jp_903_;
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
v_a_937_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_935_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_935_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
v___jp_903_:
{
lean_object* v_fst_905_; lean_object* v_snd_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_919_; 
v_fst_905_ = lean_ctor_get(v_result_904_, 0);
v_snd_906_ = lean_ctor_get(v_result_904_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v_result_904_);
if (v_isSharedCheck_919_ == 0)
{
v___x_908_ = v_result_904_;
v_isShared_909_ = v_isSharedCheck_919_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_snd_906_);
lean_inc(v_fst_905_);
lean_dec(v_result_904_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_919_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_910_ = lean_array_get_size(v_fst_905_);
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = lean_nat_dec_eq(v___x_910_, v___x_911_);
if (v___x_912_ == 0)
{
lean_object* v___x_914_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set_tag(v___x_908_, 1);
v___x_914_ = v___x_908_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_fst_905_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_snd_906_);
v___x_914_ = v_reuseFailAlloc_916_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_915_; 
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; 
lean_del_object(v___x_908_);
lean_dec(v_snd_906_);
lean_dec(v_fst_905_);
v___x_917_ = lean_box(0);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros___boxed(lean_object* v_mvarId_945_, lean_object* v_names_946_, lean_object* v_hygienic_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
uint8_t v_hygienic_boxed_955_; lean_object* v_res_956_; 
v_hygienic_boxed_955_ = lean_unbox(v_hygienic_947_);
v_res_956_ = l_Lean_Meta_Sym_intros(v_mvarId_945_, v_names_946_, v_hygienic_boxed_955_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN(lean_object* v_mvarId_957_, lean_object* v_num_958_, uint8_t v_hygienic_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
lean_inc(v_num_958_);
v___x_968_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_957_, v_num_958_, v___x_967_, v_hygienic_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_991_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_991_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_991_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_991_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v_fst_973_; lean_object* v_snd_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_990_; 
v_fst_973_ = lean_ctor_get(v_a_969_, 0);
v_snd_974_ = lean_ctor_get(v_a_969_, 1);
v_isSharedCheck_990_ = !lean_is_exclusive(v_a_969_);
if (v_isSharedCheck_990_ == 0)
{
v___x_976_ = v_a_969_;
v_isShared_977_ = v_isSharedCheck_990_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_snd_974_);
lean_inc(v_fst_973_);
lean_dec(v_a_969_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_990_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_978_ = lean_array_get_size(v_fst_973_);
v___x_979_ = lean_nat_dec_eq(v___x_978_, v_num_958_);
lean_dec(v_num_958_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_982_; 
lean_del_object(v___x_976_);
lean_dec(v_snd_974_);
lean_dec(v_fst_973_);
v___x_980_ = lean_box(0);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_980_);
v___x_982_ = v___x_971_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
else
{
lean_object* v___x_985_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set_tag(v___x_976_, 1);
v___x_985_ = v___x_976_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_fst_973_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_snd_974_);
v___x_985_ = v_reuseFailAlloc_989_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_987_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_985_);
v___x_987_ = v___x_971_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec(v_num_958_);
v_a_992_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_968_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_968_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN___boxed(lean_object* v_mvarId_1000_, lean_object* v_num_1001_, lean_object* v_hygienic_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
uint8_t v_hygienic_boxed_1010_; lean_object* v_res_1011_; 
v_hygienic_boxed_1010_ = lean_unbox(v_hygienic_1002_);
v_res_1011_ = l_Lean_Meta_Sym_introN(v_mvarId_1000_, v_num_1001_, v_hygienic_boxed_1010_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
return v_res_1011_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_IsClass(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
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
