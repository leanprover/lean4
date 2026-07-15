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
lean_object* l_Lean_Meta_Sym_isClass_x3f(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_68_; lean_object* v_ngen_69_; lean_object* v_namePrefix_70_; lean_object* v_idx_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_100_; 
v___x_68_ = lean_st_ref_get(v___y_66_);
v_ngen_69_ = lean_ctor_get(v___x_68_, 2);
lean_inc_ref(v_ngen_69_);
lean_dec(v___x_68_);
v_namePrefix_70_ = lean_ctor_get(v_ngen_69_, 0);
v_idx_71_ = lean_ctor_get(v_ngen_69_, 1);
v_isSharedCheck_100_ = !lean_is_exclusive(v_ngen_69_);
if (v_isSharedCheck_100_ == 0)
{
v___x_73_ = v_ngen_69_;
v_isShared_74_ = v_isSharedCheck_100_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_idx_71_);
lean_inc(v_namePrefix_70_);
lean_dec(v_ngen_69_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_100_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; lean_object* v_env_76_; lean_object* v_nextMacroScope_77_; lean_object* v_auxDeclNGen_78_; lean_object* v_traceState_79_; lean_object* v_cache_80_; lean_object* v_messages_81_; lean_object* v_infoState_82_; lean_object* v_snapshotTasks_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_98_; 
v___x_75_ = lean_st_ref_take(v___y_66_);
v_env_76_ = lean_ctor_get(v___x_75_, 0);
v_nextMacroScope_77_ = lean_ctor_get(v___x_75_, 1);
v_auxDeclNGen_78_ = lean_ctor_get(v___x_75_, 3);
v_traceState_79_ = lean_ctor_get(v___x_75_, 4);
v_cache_80_ = lean_ctor_get(v___x_75_, 5);
v_messages_81_ = lean_ctor_get(v___x_75_, 6);
v_infoState_82_ = lean_ctor_get(v___x_75_, 7);
v_snapshotTasks_83_ = lean_ctor_get(v___x_75_, 8);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_98_ == 0)
{
lean_object* v_unused_99_; 
v_unused_99_ = lean_ctor_get(v___x_75_, 2);
lean_dec(v_unused_99_);
v___x_85_ = v___x_75_;
v_isShared_86_ = v_isSharedCheck_98_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_snapshotTasks_83_);
lean_inc(v_infoState_82_);
lean_inc(v_messages_81_);
lean_inc(v_cache_80_);
lean_inc(v_traceState_79_);
lean_inc(v_auxDeclNGen_78_);
lean_inc(v_nextMacroScope_77_);
lean_inc(v_env_76_);
lean_dec(v___x_75_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_98_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v_r_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_91_; 
lean_inc(v_idx_71_);
lean_inc(v_namePrefix_70_);
v_r_87_ = l_Lean_Name_num___override(v_namePrefix_70_, v_idx_71_);
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = lean_nat_add(v_idx_71_, v___x_88_);
lean_dec(v_idx_71_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___x_89_);
v___x_91_ = v___x_73_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_namePrefix_70_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v___x_89_);
v___x_91_ = v_reuseFailAlloc_97_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_93_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 2, v___x_91_);
v___x_93_ = v___x_85_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_env_76_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_nextMacroScope_77_);
lean_ctor_set(v_reuseFailAlloc_96_, 2, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_96_, 3, v_auxDeclNGen_78_);
lean_ctor_set(v_reuseFailAlloc_96_, 4, v_traceState_79_);
lean_ctor_set(v_reuseFailAlloc_96_, 5, v_cache_80_);
lean_ctor_set(v_reuseFailAlloc_96_, 6, v_messages_81_);
lean_ctor_set(v_reuseFailAlloc_96_, 7, v_infoState_82_);
lean_ctor_set(v_reuseFailAlloc_96_, 8, v_snapshotTasks_83_);
v___x_93_ = v_reuseFailAlloc_96_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_st_ref_set(v___y_66_, v___x_93_);
v___x_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_95_, 0, v_r_87_);
return v___x_95_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg___boxed(lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(v___y_101_);
lean_dec(v___y_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___x_111_; lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
v___x_111_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(v___y_109_);
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0___boxed(lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(lean_object* v_max_128_, lean_object* v_finalize_129_, lean_object* v_mkName_130_, lean_object* v_updateLocalInsts_131_, lean_object* v_i_132_, lean_object* v_lctx_133_, lean_object* v_localInsts_134_, lean_object* v_fvars_135_, lean_object* v_type_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
uint8_t v___x_144_; 
v___x_144_ = lean_nat_dec_le(v_max_128_, v_i_132_);
if (v___x_144_ == 0)
{
switch(lean_obj_tag(v_type_136_))
{
case 10:
{
lean_object* v_expr_145_; 
v_expr_145_ = lean_ctor_get(v_type_136_, 1);
lean_inc_ref(v_expr_145_);
lean_dec_ref_known(v_type_136_, 2);
v_type_136_ = v_expr_145_;
goto _start;
}
case 7:
{
lean_object* v_binderName_147_; lean_object* v_binderType_148_; lean_object* v_body_149_; uint8_t v_binderInfo_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_binderName_147_ = lean_ctor_get(v_type_136_, 0);
lean_inc(v_binderName_147_);
v_binderType_148_ = lean_ctor_get(v_type_136_, 1);
lean_inc_ref(v_binderType_148_);
v_body_149_ = lean_ctor_get(v_type_136_, 2);
lean_inc_ref(v_body_149_);
v_binderInfo_150_ = lean_ctor_get_uint8(v_type_136_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_136_, 3);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_array_get_size(v_fvars_135_);
lean_inc_ref(v_fvars_135_);
v___x_153_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_binderType_148_, v___x_151_, v___x_152_, v_fvars_135_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_155_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_a_154_);
lean_dec_ref_known(v___x_153_, 1);
v___x_155_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_157_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref_known(v___x_155_, 1);
lean_inc_ref(v_mkName_130_);
lean_inc(v_a_142_);
lean_inc_ref(v_a_141_);
lean_inc(v_a_140_);
lean_inc_ref(v_a_139_);
lean_inc(v_i_132_);
lean_inc_ref(v_lctx_133_);
v___x_157_ = lean_apply_8(v_mkName_130_, v_lctx_133_, v_binderName_147_, v_i_132_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, lean_box(0));
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref_known(v___x_157_, 1);
v___x_159_ = 0;
lean_inc(v_a_154_);
lean_inc(v_a_156_);
v___x_160_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_133_, v_a_156_, v_a_158_, v_a_154_, v_binderInfo_150_, v___x_159_);
v___x_161_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(v_a_156_, v_a_138_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc_n(v_a_162_, 2);
lean_dec_ref_known(v___x_161_, 1);
v___x_163_ = lean_array_push(v_fvars_135_, v_a_162_);
lean_inc_ref(v_updateLocalInsts_131_);
v___x_164_ = lean_apply_3(v_updateLocalInsts_131_, v_localInsts_134_, v_a_162_, v_a_154_);
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_nat_add(v_i_132_, v___x_165_);
lean_dec(v_i_132_);
v_i_132_ = v___x_166_;
v_lctx_133_ = v___x_160_;
v_localInsts_134_ = v___x_164_;
v_fvars_135_ = v___x_163_;
v_type_136_ = v_body_149_;
goto _start;
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
lean_dec_ref(v___x_160_);
lean_dec(v_a_154_);
lean_dec_ref(v_body_149_);
lean_dec_ref(v_fvars_135_);
lean_dec_ref(v_localInsts_134_);
lean_dec(v_i_132_);
lean_dec_ref(v_updateLocalInsts_131_);
lean_dec_ref(v_mkName_130_);
lean_dec_ref(v_finalize_129_);
v_a_168_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_161_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_161_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
lean_dec(v_a_156_);
lean_dec(v_a_154_);
lean_dec_ref(v_body_149_);
lean_dec_ref(v_fvars_135_);
lean_dec_ref(v_localInsts_134_);
lean_dec_ref(v_lctx_133_);
lean_dec(v_i_132_);
lean_dec_ref(v_updateLocalInsts_131_);
lean_dec_ref(v_mkName_130_);
lean_dec_ref(v_finalize_129_);
v_a_176_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_157_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_157_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
lean_dec(v_a_154_);
lean_dec_ref(v_body_149_);
lean_dec(v_binderName_147_);
lean_dec_ref(v_fvars_135_);
lean_dec_ref(v_localInsts_134_);
lean_dec_ref(v_lctx_133_);
lean_dec(v_i_132_);
lean_dec_ref(v_updateLocalInsts_131_);
lean_dec_ref(v_mkName_130_);
lean_dec_ref(v_finalize_129_);
v_a_184_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_155_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_155_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec_ref(v_body_149_);
lean_dec(v_binderName_147_);
lean_dec_ref(v_fvars_135_);
lean_dec_ref(v_localInsts_134_);
lean_dec_ref(v_lctx_133_);
lean_dec(v_i_132_);
lean_dec_ref(v_updateLocalInsts_131_);
lean_dec_ref(v_mkName_130_);
lean_dec_ref(v_finalize_129_);
v_a_192_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_153_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_153_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
case 8:
{
lean_object* v_declName_200_; lean_object* v_type_201_; lean_object* v_value_202_; lean_object* v_body_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_declName_200_ = lean_ctor_get(v_type_136_, 0);
lean_inc(v_declName_200_);
v_type_201_ = lean_ctor_get(v_type_136_, 1);
lean_inc_ref(v_type_201_);
v_value_202_ = lean_ctor_get(v_type_136_, 2);
lean_inc_ref(v_value_202_);
v_body_203_ = lean_ctor_get(v_type_136_, 3);
lean_inc_ref(v_body_203_);
lean_dec_ref_known(v_type_136_, 4);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_array_get_size(v_fvars_135_);
lean_inc_ref(v_fvars_135_);
v___x_206_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_201_, v___x_204_, v___x_205_, v_fvars_135_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_208_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref_known(v___x_206_, 1);
lean_inc_ref(v_fvars_135_);
v___x_208_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_value_202_, v___x_204_, v___x_205_, v_fvars_135_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_210_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_208_, 1);
v___x_210_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_212_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
lean_dec_ref_known(v___x_210_, 1);
lean_inc_ref(v_mkName_130_);
lean_inc(v_a_142_);
lean_inc_ref(v_a_141_);
lean_inc(v_a_140_);
lean_inc_ref(v_a_139_);
lean_inc(v_i_132_);
lean_inc_ref(v_lctx_133_);
v___x_212_ = lean_apply_8(v_mkName_130_, v_lctx_133_, v_declName_200_, v_i_132_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, lean_box(0));
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; uint8_t v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref_known(v___x_212_, 1);
v___x_214_ = 0;
lean_inc(v_a_207_);
lean_inc(v_a_211_);
v___x_215_ = l_Lean_LocalContext_mkLetDecl(v_lctx_133_, v_a_211_, v_a_213_, v_a_207_, v_a_209_, v___x_144_, v___x_214_);
v___x_216_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(v_a_211_, v_a_138_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc_n(v_a_217_, 2);
lean_dec_ref_known(v___x_216_, 1);
v___x_218_ = lean_array_push(v_fvars_135_, v_a_217_);
lean_inc_ref(v_updateLocalInsts_131_);
v___x_219_ = lean_apply_3(v_updateLocalInsts_131_, v_localInsts_134_, v_a_217_, v_a_207_);
v___x_220_ = lean_unsigned_to_nat(1u);
v___x_221_ = lean_nat_add(v_i_132_, v___x_220_);
lean_dec(v_i_132_);
v_i_132_ = v___x_221_;
v_lctx_133_ = v___x_215_;
v_localInsts_134_ = v___x_219_;
v_fvars_135_ = v___x_218_;
v_type_136_ = v_body_203_;
goto _start;
}
else
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
lean_dec_ref(v___x_215_);
lean_dec(v_a_207_);
lean_dec_ref(v_body_203_);
lean_dec_ref(v_fvars_135_);
lean_dec_ref(v_localInsts_134_);
lean_dec(v_i_132_);
lean_dec_ref(v_updateLocalInsts_131_);
lean_dec_ref(v_mkName_130_);
lean_dec_ref(v_finalize_129_);
v_a_223_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_216_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_216_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec(v_a_211_);
lean_dec(v_a_209_);
lean_dec(v_a_207_);
lean_dec_ref(v_body_203_);
lean_dec_ref(v_fvars_135_);
lean_dec_ref(v_localInsts_134_);
lean_dec_ref(v_lctx_133_);
lean_dec(v_i_132_);
lean_dec_ref(v_updateLocalInsts_131_);
lean_dec_ref(v_mkName_130_);
lean_dec_ref(v_finalize_129_);
v_a_231_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_212_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_212_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec(v_a_209_);
lean_dec(v_a_207_);
lean_dec_ref(v_body_203_);
lean_dec(v_declName_200_);
lean_dec_ref(v_fvars_135_);
lean_dec_ref(v_localInsts_134_);
lean_dec_ref(v_lctx_133_);
lean_dec(v_i_132_);
lean_dec_ref(v_updateLocalInsts_131_);
lean_dec_ref(v_mkName_130_);
lean_dec_ref(v_finalize_129_);
v_a_239_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_210_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_210_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec(v_a_207_);
lean_dec_ref(v_body_203_);
lean_dec(v_declName_200_);
lean_dec_ref(v_fvars_135_);
lean_dec_ref(v_localInsts_134_);
lean_dec_ref(v_lctx_133_);
lean_dec(v_i_132_);
lean_dec_ref(v_updateLocalInsts_131_);
lean_dec_ref(v_mkName_130_);
lean_dec_ref(v_finalize_129_);
v_a_247_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_208_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_208_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec_ref(v_body_203_);
lean_dec_ref(v_value_202_);
lean_dec(v_declName_200_);
lean_dec_ref(v_fvars_135_);
lean_dec_ref(v_localInsts_134_);
lean_dec_ref(v_lctx_133_);
lean_dec(v_i_132_);
lean_dec_ref(v_updateLocalInsts_131_);
lean_dec_ref(v_mkName_130_);
lean_dec_ref(v_finalize_129_);
v_a_255_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_206_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_206_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
default: 
{
lean_object* v___x_263_; 
lean_dec(v_i_132_);
lean_dec_ref(v_updateLocalInsts_131_);
lean_dec_ref(v_mkName_130_);
lean_inc(v_a_142_);
lean_inc_ref(v_a_141_);
lean_inc(v_a_140_);
lean_inc_ref(v_a_139_);
lean_inc(v_a_138_);
lean_inc_ref(v_a_137_);
v___x_263_ = lean_apply_11(v_finalize_129_, v_lctx_133_, v_localInsts_134_, v_fvars_135_, v_type_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, lean_box(0));
return v___x_263_;
}
}
}
else
{
lean_object* v___x_264_; 
lean_dec(v_i_132_);
lean_dec_ref(v_updateLocalInsts_131_);
lean_dec_ref(v_mkName_130_);
lean_inc(v_a_142_);
lean_inc_ref(v_a_141_);
lean_inc(v_a_140_);
lean_inc_ref(v_a_139_);
lean_inc(v_a_138_);
lean_inc_ref(v_a_137_);
v___x_264_ = lean_apply_11(v_finalize_129_, v_lctx_133_, v_localInsts_134_, v_fvars_135_, v_type_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, lean_box(0));
return v___x_264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit___boxed(lean_object* v_max_265_, lean_object* v_finalize_266_, lean_object* v_mkName_267_, lean_object* v_updateLocalInsts_268_, lean_object* v_i_269_, lean_object* v_lctx_270_, lean_object* v_localInsts_271_, lean_object* v_fvars_272_, lean_object* v_type_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(v_max_265_, v_finalize_266_, v_mkName_267_, v_updateLocalInsts_268_, v_i_269_, v_lctx_270_, v_localInsts_271_, v_fvars_272_, v_type_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_max_265_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0(lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(v___y_287_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___boxed(lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0(v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(lean_object* v_names_298_, uint8_t v_hygienic_299_, lean_object* v_lctx_300_, lean_object* v_binderName_301_, lean_object* v_i_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = lean_array_get_size(v_names_298_);
v___x_309_ = lean_nat_dec_lt(v_i_302_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_300_, v_binderName_301_, v_hygienic_299_, v___y_305_, v___y_306_);
return v___x_310_;
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec(v_binderName_301_);
v___x_311_ = lean_array_fget_borrowed(v_names_298_, v_i_302_);
lean_inc(v___x_311_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed(lean_object* v_names_313_, lean_object* v_hygienic_314_, lean_object* v_lctx_315_, lean_object* v_binderName_316_, lean_object* v_i_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
uint8_t v_hygienic_boxed_323_; lean_object* v_res_324_; 
v_hygienic_boxed_323_ = lean_unbox(v_hygienic_314_);
v_res_324_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(v_names_313_, v_hygienic_boxed_323_, v_lctx_315_, v_binderName_316_, v_i_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v_i_317_);
lean_dec_ref(v_lctx_315_);
lean_dec_ref(v_names_313_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
lean_object* v_ks_329_; lean_object* v_vs_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_354_; 
v_ks_329_ = lean_ctor_get(v_x_325_, 0);
v_vs_330_ = lean_ctor_get(v_x_325_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v_x_325_);
if (v_isSharedCheck_354_ == 0)
{
v___x_332_ = v_x_325_;
v_isShared_333_ = v_isSharedCheck_354_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_vs_330_);
lean_inc(v_ks_329_);
lean_dec(v_x_325_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_354_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_array_get_size(v_ks_329_);
v___x_335_ = lean_nat_dec_lt(v_x_326_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
lean_dec(v_x_326_);
v___x_336_ = lean_array_push(v_ks_329_, v_x_327_);
v___x_337_ = lean_array_push(v_vs_330_, v_x_328_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v___x_337_);
lean_ctor_set(v___x_332_, 0, v___x_336_);
v___x_339_ = v___x_332_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
else
{
lean_object* v_k_x27_341_; uint8_t v___x_342_; 
v_k_x27_341_ = lean_array_fget_borrowed(v_ks_329_, v_x_326_);
v___x_342_ = l_Lean_instBEqMVarId_beq(v_x_327_, v_k_x27_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_344_; 
if (v_isShared_333_ == 0)
{
v___x_344_ = v___x_332_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_ks_329_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_vs_330_);
v___x_344_ = v_reuseFailAlloc_348_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = lean_nat_add(v_x_326_, v___x_345_);
lean_dec(v_x_326_);
v_x_325_ = v___x_344_;
v_x_326_ = v___x_346_;
goto _start;
}
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_349_ = lean_array_fset(v_ks_329_, v_x_326_, v_x_327_);
v___x_350_ = lean_array_fset(v_vs_330_, v_x_326_, v_x_328_);
lean_dec(v_x_326_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v___x_350_);
lean_ctor_set(v___x_332_, 0, v___x_349_);
v___x_352_ = v___x_332_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_n_355_, lean_object* v_k_356_, lean_object* v_v_357_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_n_355_, v___x_358_, v_k_356_, v_v_357_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_361_, size_t v_x_362_, size_t v_x_363_, lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
if (lean_obj_tag(v_x_361_) == 0)
{
lean_object* v_es_366_; size_t v___x_367_; size_t v___x_368_; lean_object* v_j_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_es_366_ = lean_ctor_get(v_x_361_, 0);
v___x_367_ = ((size_t)31ULL);
v___x_368_ = lean_usize_land(v_x_362_, v___x_367_);
v_j_369_ = lean_usize_to_nat(v___x_368_);
v___x_370_ = lean_array_get_size(v_es_366_);
v___x_371_ = lean_nat_dec_lt(v_j_369_, v___x_370_);
if (v___x_371_ == 0)
{
lean_dec(v_j_369_);
lean_dec(v_x_365_);
lean_dec(v_x_364_);
return v_x_361_;
}
else
{
lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_410_; 
lean_inc_ref(v_es_366_);
v_isSharedCheck_410_ = !lean_is_exclusive(v_x_361_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v_x_361_, 0);
lean_dec(v_unused_411_);
v___x_373_ = v_x_361_;
v_isShared_374_ = v_isSharedCheck_410_;
goto v_resetjp_372_;
}
else
{
lean_dec(v_x_361_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_410_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v_v_375_; lean_object* v___x_376_; lean_object* v_xs_x27_377_; lean_object* v___y_379_; 
v_v_375_ = lean_array_fget(v_es_366_, v_j_369_);
v___x_376_ = lean_box(0);
v_xs_x27_377_ = lean_array_fset(v_es_366_, v_j_369_, v___x_376_);
switch(lean_obj_tag(v_v_375_))
{
case 0:
{
lean_object* v_key_384_; lean_object* v_val_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_395_; 
v_key_384_ = lean_ctor_get(v_v_375_, 0);
v_val_385_ = lean_ctor_get(v_v_375_, 1);
v_isSharedCheck_395_ = !lean_is_exclusive(v_v_375_);
if (v_isSharedCheck_395_ == 0)
{
v___x_387_ = v_v_375_;
v_isShared_388_ = v_isSharedCheck_395_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_val_385_);
lean_inc(v_key_384_);
lean_dec(v_v_375_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_395_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
uint8_t v___x_389_; 
v___x_389_ = l_Lean_instBEqMVarId_beq(v_x_364_, v_key_384_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_del_object(v___x_387_);
v___x_390_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_384_, v_val_385_, v_x_364_, v_x_365_);
v___x_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
v___y_379_ = v___x_391_;
goto v___jp_378_;
}
else
{
lean_object* v___x_393_; 
lean_dec(v_val_385_);
lean_dec(v_key_384_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v_x_365_);
lean_ctor_set(v___x_387_, 0, v_x_364_);
v___x_393_ = v___x_387_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_x_364_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_x_365_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
v___y_379_ = v___x_393_;
goto v___jp_378_;
}
}
}
}
case 1:
{
lean_object* v_node_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_408_; 
v_node_396_ = lean_ctor_get(v_v_375_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v_v_375_);
if (v_isSharedCheck_408_ == 0)
{
v___x_398_ = v_v_375_;
v_isShared_399_ = v_isSharedCheck_408_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_node_396_);
lean_dec(v_v_375_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_408_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
size_t v___x_400_; size_t v___x_401_; size_t v___x_402_; size_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_400_ = ((size_t)5ULL);
v___x_401_ = lean_usize_shift_right(v_x_362_, v___x_400_);
v___x_402_ = ((size_t)1ULL);
v___x_403_ = lean_usize_add(v_x_363_, v___x_402_);
v___x_404_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_node_396_, v___x_401_, v___x_403_, v_x_364_, v_x_365_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_404_);
v___x_406_ = v___x_398_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
v___y_379_ = v___x_406_;
goto v___jp_378_;
}
}
}
default: 
{
lean_object* v___x_409_; 
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v_x_364_);
lean_ctor_set(v___x_409_, 1, v_x_365_);
v___y_379_ = v___x_409_;
goto v___jp_378_;
}
}
v___jp_378_:
{
lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_380_ = lean_array_fset(v_xs_x27_377_, v_j_369_, v___y_379_);
lean_dec(v_j_369_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_380_);
v___x_382_ = v___x_373_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
else
{
lean_object* v_ks_412_; lean_object* v_vs_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_433_; 
v_ks_412_ = lean_ctor_get(v_x_361_, 0);
v_vs_413_ = lean_ctor_get(v_x_361_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_x_361_);
if (v_isSharedCheck_433_ == 0)
{
v___x_415_ = v_x_361_;
v_isShared_416_ = v_isSharedCheck_433_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_vs_413_);
lean_inc(v_ks_412_);
lean_dec(v_x_361_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_433_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_ks_412_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_vs_413_);
v___x_418_ = v_reuseFailAlloc_432_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v_newNode_419_; uint8_t v___y_421_; size_t v___x_427_; uint8_t v___x_428_; 
v_newNode_419_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(v___x_418_, v_x_364_, v_x_365_);
v___x_427_ = ((size_t)7ULL);
v___x_428_ = lean_usize_dec_le(v___x_427_, v_x_363_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_429_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_419_);
v___x_430_ = lean_unsigned_to_nat(4u);
v___x_431_ = lean_nat_dec_lt(v___x_429_, v___x_430_);
lean_dec(v___x_429_);
v___y_421_ = v___x_431_;
goto v___jp_420_;
}
else
{
v___y_421_ = v___x_428_;
goto v___jp_420_;
}
v___jp_420_:
{
if (v___y_421_ == 0)
{
lean_object* v_ks_422_; lean_object* v_vs_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_ks_422_ = lean_ctor_get(v_newNode_419_, 0);
lean_inc_ref(v_ks_422_);
v_vs_423_ = lean_ctor_get(v_newNode_419_, 1);
lean_inc_ref(v_vs_423_);
lean_dec_ref(v_newNode_419_);
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_426_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_363_, v_ks_422_, v_vs_423_, v___x_424_, v___x_425_);
lean_dec_ref(v_vs_423_);
lean_dec_ref(v_ks_422_);
return v___x_426_;
}
else
{
return v_newNode_419_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(size_t v_depth_434_, lean_object* v_keys_435_, lean_object* v_vals_436_, lean_object* v_i_437_, lean_object* v_entries_438_){
_start:
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = lean_array_get_size(v_keys_435_);
v___x_440_ = lean_nat_dec_lt(v_i_437_, v___x_439_);
if (v___x_440_ == 0)
{
lean_dec(v_i_437_);
return v_entries_438_;
}
else
{
lean_object* v_k_441_; lean_object* v_v_442_; uint64_t v___x_443_; size_t v_h_444_; size_t v___x_445_; lean_object* v___x_446_; size_t v___x_447_; size_t v___x_448_; size_t v___x_449_; size_t v_h_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_k_441_ = lean_array_fget_borrowed(v_keys_435_, v_i_437_);
v_v_442_ = lean_array_fget_borrowed(v_vals_436_, v_i_437_);
v___x_443_ = l_Lean_instHashableMVarId_hash(v_k_441_);
v_h_444_ = lean_uint64_to_usize(v___x_443_);
v___x_445_ = ((size_t)5ULL);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_sub(v_depth_434_, v___x_447_);
v___x_449_ = lean_usize_mul(v___x_445_, v___x_448_);
v_h_450_ = lean_usize_shift_right(v_h_444_, v___x_449_);
v___x_451_ = lean_nat_add(v_i_437_, v___x_446_);
lean_dec(v_i_437_);
lean_inc(v_v_442_);
lean_inc(v_k_441_);
v___x_452_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_entries_438_, v_h_450_, v_depth_434_, v_k_441_, v_v_442_);
v_i_437_ = v___x_451_;
v_entries_438_ = v___x_452_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_depth_454_, lean_object* v_keys_455_, lean_object* v_vals_456_, lean_object* v_i_457_, lean_object* v_entries_458_){
_start:
{
size_t v_depth_boxed_459_; lean_object* v_res_460_; 
v_depth_boxed_459_ = lean_unbox_usize(v_depth_454_);
lean_dec(v_depth_454_);
v_res_460_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_boxed_459_, v_keys_455_, v_vals_456_, v_i_457_, v_entries_458_);
lean_dec_ref(v_vals_456_);
lean_dec_ref(v_keys_455_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_461_, lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
size_t v_x_5846__boxed_466_; size_t v_x_5847__boxed_467_; lean_object* v_res_468_; 
v_x_5846__boxed_466_ = lean_unbox_usize(v_x_462_);
lean_dec(v_x_462_);
v_x_5847__boxed_467_ = lean_unbox_usize(v_x_463_);
lean_dec(v_x_463_);
v_res_468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_461_, v_x_5846__boxed_466_, v_x_5847__boxed_467_, v_x_464_, v_x_465_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(lean_object* v_x_469_, lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
uint64_t v___x_472_; size_t v___x_473_; size_t v___x_474_; lean_object* v___x_475_; 
v___x_472_ = l_Lean_instHashableMVarId_hash(v_x_470_);
v___x_473_ = lean_uint64_to_usize(v___x_472_);
v___x_474_ = ((size_t)1ULL);
v___x_475_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_469_, v___x_473_, v___x_474_, v_x_470_, v_x_471_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(lean_object* v_mvarId_476_, lean_object* v_val_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; lean_object* v_mctx_481_; lean_object* v_cache_482_; lean_object* v_zetaDeltaFVarIds_483_; lean_object* v_postponed_484_; lean_object* v_diag_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_513_; 
v___x_480_ = lean_st_ref_take(v___y_478_);
v_mctx_481_ = lean_ctor_get(v___x_480_, 0);
v_cache_482_ = lean_ctor_get(v___x_480_, 1);
v_zetaDeltaFVarIds_483_ = lean_ctor_get(v___x_480_, 2);
v_postponed_484_ = lean_ctor_get(v___x_480_, 3);
v_diag_485_ = lean_ctor_get(v___x_480_, 4);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_513_ == 0)
{
v___x_487_ = v___x_480_;
v_isShared_488_ = v_isSharedCheck_513_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_diag_485_);
lean_inc(v_postponed_484_);
lean_inc(v_zetaDeltaFVarIds_483_);
lean_inc(v_cache_482_);
lean_inc(v_mctx_481_);
lean_dec(v___x_480_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_513_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v_depth_489_; lean_object* v_levelAssignDepth_490_; lean_object* v_lmvarCounter_491_; lean_object* v_mvarCounter_492_; lean_object* v_lDecls_493_; lean_object* v_decls_494_; lean_object* v_userNames_495_; lean_object* v_lAssignment_496_; lean_object* v_eAssignment_497_; lean_object* v_dAssignment_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_512_; 
v_depth_489_ = lean_ctor_get(v_mctx_481_, 0);
v_levelAssignDepth_490_ = lean_ctor_get(v_mctx_481_, 1);
v_lmvarCounter_491_ = lean_ctor_get(v_mctx_481_, 2);
v_mvarCounter_492_ = lean_ctor_get(v_mctx_481_, 3);
v_lDecls_493_ = lean_ctor_get(v_mctx_481_, 4);
v_decls_494_ = lean_ctor_get(v_mctx_481_, 5);
v_userNames_495_ = lean_ctor_get(v_mctx_481_, 6);
v_lAssignment_496_ = lean_ctor_get(v_mctx_481_, 7);
v_eAssignment_497_ = lean_ctor_get(v_mctx_481_, 8);
v_dAssignment_498_ = lean_ctor_get(v_mctx_481_, 9);
v_isSharedCheck_512_ = !lean_is_exclusive(v_mctx_481_);
if (v_isSharedCheck_512_ == 0)
{
v___x_500_ = v_mctx_481_;
v_isShared_501_ = v_isSharedCheck_512_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_dAssignment_498_);
lean_inc(v_eAssignment_497_);
lean_inc(v_lAssignment_496_);
lean_inc(v_userNames_495_);
lean_inc(v_decls_494_);
lean_inc(v_lDecls_493_);
lean_inc(v_mvarCounter_492_);
lean_inc(v_lmvarCounter_491_);
lean_inc(v_levelAssignDepth_490_);
lean_inc(v_depth_489_);
lean_dec(v_mctx_481_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_512_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_eAssignment_497_, v_mvarId_476_, v_val_477_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 8, v___x_502_);
v___x_504_ = v___x_500_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_depth_489_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_levelAssignDepth_490_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_lmvarCounter_491_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_mvarCounter_492_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v_lDecls_493_);
lean_ctor_set(v_reuseFailAlloc_511_, 5, v_decls_494_);
lean_ctor_set(v_reuseFailAlloc_511_, 6, v_userNames_495_);
lean_ctor_set(v_reuseFailAlloc_511_, 7, v_lAssignment_496_);
lean_ctor_set(v_reuseFailAlloc_511_, 8, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_511_, 9, v_dAssignment_498_);
v___x_504_ = v_reuseFailAlloc_511_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_506_; 
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_504_);
v___x_506_ = v___x_487_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_cache_482_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_zetaDeltaFVarIds_483_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v_postponed_484_);
lean_ctor_set(v_reuseFailAlloc_510_, 4, v_diag_485_);
v___x_506_ = v_reuseFailAlloc_510_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_st_ref_set(v___y_478_, v___x_506_);
v___x_508_ = lean_box(0);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg___boxed(lean_object* v_mvarId_514_, lean_object* v_val_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_514_, v_val_515_, v___y_516_);
lean_dec(v___y_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(lean_object* v_mvarId_519_, lean_object* v_fvars_520_, lean_object* v_mvarIdPending_521_, lean_object* v___y_522_){
_start:
{
lean_object* v___x_524_; lean_object* v_mctx_525_; lean_object* v_cache_526_; lean_object* v_zetaDeltaFVarIds_527_; lean_object* v_postponed_528_; lean_object* v_diag_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_558_; 
v___x_524_ = lean_st_ref_take(v___y_522_);
v_mctx_525_ = lean_ctor_get(v___x_524_, 0);
v_cache_526_ = lean_ctor_get(v___x_524_, 1);
v_zetaDeltaFVarIds_527_ = lean_ctor_get(v___x_524_, 2);
v_postponed_528_ = lean_ctor_get(v___x_524_, 3);
v_diag_529_ = lean_ctor_get(v___x_524_, 4);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_558_ == 0)
{
v___x_531_ = v___x_524_;
v_isShared_532_ = v_isSharedCheck_558_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_diag_529_);
lean_inc(v_postponed_528_);
lean_inc(v_zetaDeltaFVarIds_527_);
lean_inc(v_cache_526_);
lean_inc(v_mctx_525_);
lean_dec(v___x_524_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_558_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v_depth_533_; lean_object* v_levelAssignDepth_534_; lean_object* v_lmvarCounter_535_; lean_object* v_mvarCounter_536_; lean_object* v_lDecls_537_; lean_object* v_decls_538_; lean_object* v_userNames_539_; lean_object* v_lAssignment_540_; lean_object* v_eAssignment_541_; lean_object* v_dAssignment_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_557_; 
v_depth_533_ = lean_ctor_get(v_mctx_525_, 0);
v_levelAssignDepth_534_ = lean_ctor_get(v_mctx_525_, 1);
v_lmvarCounter_535_ = lean_ctor_get(v_mctx_525_, 2);
v_mvarCounter_536_ = lean_ctor_get(v_mctx_525_, 3);
v_lDecls_537_ = lean_ctor_get(v_mctx_525_, 4);
v_decls_538_ = lean_ctor_get(v_mctx_525_, 5);
v_userNames_539_ = lean_ctor_get(v_mctx_525_, 6);
v_lAssignment_540_ = lean_ctor_get(v_mctx_525_, 7);
v_eAssignment_541_ = lean_ctor_get(v_mctx_525_, 8);
v_dAssignment_542_ = lean_ctor_get(v_mctx_525_, 9);
v_isSharedCheck_557_ = !lean_is_exclusive(v_mctx_525_);
if (v_isSharedCheck_557_ == 0)
{
v___x_544_ = v_mctx_525_;
v_isShared_545_ = v_isSharedCheck_557_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_dAssignment_542_);
lean_inc(v_eAssignment_541_);
lean_inc(v_lAssignment_540_);
lean_inc(v_userNames_539_);
lean_inc(v_decls_538_);
lean_inc(v_lDecls_537_);
lean_inc(v_mvarCounter_536_);
lean_inc(v_lmvarCounter_535_);
lean_inc(v_levelAssignDepth_534_);
lean_inc(v_depth_533_);
lean_dec(v_mctx_525_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_557_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v_fvars_520_);
lean_ctor_set(v___x_546_, 1, v_mvarIdPending_521_);
v___x_547_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_dAssignment_542_, v_mvarId_519_, v___x_546_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 9, v___x_547_);
v___x_549_ = v___x_544_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_depth_533_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_levelAssignDepth_534_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_lmvarCounter_535_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_mvarCounter_536_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v_lDecls_537_);
lean_ctor_set(v_reuseFailAlloc_556_, 5, v_decls_538_);
lean_ctor_set(v_reuseFailAlloc_556_, 6, v_userNames_539_);
lean_ctor_set(v_reuseFailAlloc_556_, 7, v_lAssignment_540_);
lean_ctor_set(v_reuseFailAlloc_556_, 8, v_eAssignment_541_);
lean_ctor_set(v_reuseFailAlloc_556_, 9, v___x_547_);
v___x_549_ = v_reuseFailAlloc_556_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_551_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_549_);
v___x_551_ = v___x_531_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_cache_526_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_zetaDeltaFVarIds_527_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_postponed_528_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_diag_529_);
v___x_551_ = v_reuseFailAlloc_555_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_552_ = lean_st_ref_set(v___y_522_, v___x_551_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg___boxed(lean_object* v_mvarId_559_, lean_object* v_fvars_560_, lean_object* v_mvarIdPending_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_559_, v_fvars_560_, v_mvarIdPending_561_, v___y_562_);
lean_dec(v___y_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(lean_object* v___x_565_, lean_object* v_userName_566_, lean_object* v_lctx_567_, lean_object* v_localInstances_568_, lean_object* v_type_569_, lean_object* v_max_570_, lean_object* v_mvarId_571_, lean_object* v_lctx_572_, lean_object* v_localInsts_573_, lean_object* v_fvars_574_, lean_object* v_type_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_array_get_size(v_fvars_574_);
v___x_584_ = lean_nat_dec_eq(v___x_583_, v___x_565_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
lean_inc_ref(v_fvars_574_);
lean_inc(v___x_565_);
v___x_585_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_575_, v___x_565_, v___x_583_, v_fvars_574_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; uint8_t v___x_587_; lean_object* v___x_588_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_585_, 1);
v___x_587_ = 2;
lean_inc(v___x_565_);
v___x_588_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_572_, v_localInsts_573_, v_a_586_, v___x_587_, v_userName_566_, v___x_565_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v___x_590_ = lean_box(0);
lean_inc(v___x_565_);
lean_inc_ref(v_type_569_);
v___x_591_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_567_, v_localInstances_568_, v_type_569_, v___x_587_, v___x_590_, v___x_565_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_593_; lean_object* v___y_595_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
v___x_593_ = l_Lean_Expr_mvarId_x21(v_a_589_);
lean_dec(v_a_589_);
v___x_605_ = l_Lean_Expr_mvarId_x21(v_a_592_);
lean_inc(v___x_593_);
lean_inc_ref(v_fvars_574_);
v___x_606_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v___x_605_, v_fvars_574_, v___x_593_, v___y_579_);
lean_dec_ref(v___x_606_);
v___x_607_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkAppBVars(v_a_592_, v___x_583_);
v___x_608_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(v_max_570_, v___x_565_, v_type_569_, v___x_607_);
lean_dec_ref(v___x_607_);
lean_dec(v___x_565_);
v___x_609_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_571_, v___x_608_, v___y_579_);
v___y_595_ = v___x_609_;
goto v___jp_594_;
v___jp_594_:
{
lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_603_; 
v_isSharedCheck_603_ = !lean_is_exclusive(v___y_595_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v___y_595_, 0);
lean_dec(v_unused_604_);
v___x_597_ = v___y_595_;
v_isShared_598_ = v_isSharedCheck_603_;
goto v_resetjp_596_;
}
else
{
lean_dec(v___y_595_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_603_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v_fvars_574_);
lean_ctor_set(v___x_599_, 1, v___x_593_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_599_);
v___x_601_ = v___x_597_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_a_589_);
lean_dec_ref(v_fvars_574_);
lean_dec(v_mvarId_571_);
lean_dec_ref(v_type_569_);
lean_dec(v___x_565_);
v_a_610_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_591_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_591_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec_ref(v_fvars_574_);
lean_dec(v_mvarId_571_);
lean_dec_ref(v_type_569_);
lean_dec_ref(v_localInstances_568_);
lean_dec_ref(v_lctx_567_);
lean_dec(v___x_565_);
v_a_618_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_588_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_588_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec_ref(v_fvars_574_);
lean_dec_ref(v_localInsts_573_);
lean_dec_ref(v_lctx_572_);
lean_dec(v_mvarId_571_);
lean_dec_ref(v_type_569_);
lean_dec_ref(v_localInstances_568_);
lean_dec_ref(v_lctx_567_);
lean_dec(v_userName_566_);
lean_dec(v___x_565_);
v_a_626_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_585_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_585_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec_ref(v_type_575_);
lean_dec_ref(v_fvars_574_);
lean_dec_ref(v_localInsts_573_);
lean_dec_ref(v_lctx_572_);
lean_dec_ref(v_type_569_);
lean_dec_ref(v_localInstances_568_);
lean_dec_ref(v_lctx_567_);
lean_dec(v_userName_566_);
v___x_634_ = lean_mk_empty_array_with_capacity(v___x_565_);
lean_dec(v___x_565_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v_mvarId_571_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed(lean_object** _args){
lean_object* v___x_637_ = _args[0];
lean_object* v_userName_638_ = _args[1];
lean_object* v_lctx_639_ = _args[2];
lean_object* v_localInstances_640_ = _args[3];
lean_object* v_type_641_ = _args[4];
lean_object* v_max_642_ = _args[5];
lean_object* v_mvarId_643_ = _args[6];
lean_object* v_lctx_644_ = _args[7];
lean_object* v_localInsts_645_ = _args[8];
lean_object* v_fvars_646_ = _args[9];
lean_object* v_type_647_ = _args[10];
lean_object* v___y_648_ = _args[11];
lean_object* v___y_649_ = _args[12];
lean_object* v___y_650_ = _args[13];
lean_object* v___y_651_ = _args[14];
lean_object* v___y_652_ = _args[15];
lean_object* v___y_653_ = _args[16];
lean_object* v___y_654_ = _args[17];
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(v___x_637_, v_userName_638_, v_lctx_639_, v_localInstances_640_, v_type_641_, v_max_642_, v_mvarId_643_, v_lctx_644_, v_localInsts_645_, v_fvars_646_, v_type_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v_max_642_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(lean_object* v_env_656_, lean_object* v_localInsts_657_, lean_object* v_fvar_658_, lean_object* v_type_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_Meta_Sym_isClass_x3f(v_env_656_, v_type_659_);
if (lean_obj_tag(v___x_660_) == 1)
{
lean_object* v_val_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_val_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_val_661_);
lean_dec_ref_known(v___x_660_, 1);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v_val_661_);
lean_ctor_set(v___x_662_, 1, v_fvar_658_);
v___x_663_ = lean_array_push(v_localInsts_657_, v___x_662_);
return v___x_663_;
}
else
{
lean_dec(v___x_660_);
lean_dec_ref(v_fvar_658_);
return v_localInsts_657_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2___boxed(lean_object* v_env_664_, lean_object* v_localInsts_665_, lean_object* v_fvar_666_, lean_object* v_type_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(v_env_664_, v_localInsts_665_, v_fvar_666_, v_type_667_);
lean_dec_ref(v_type_667_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(size_t v_sz_669_, size_t v_i_670_, lean_object* v_bs_671_){
_start:
{
uint8_t v___x_672_; 
v___x_672_ = lean_usize_dec_lt(v_i_670_, v_sz_669_);
if (v___x_672_ == 0)
{
return v_bs_671_;
}
else
{
lean_object* v_v_673_; lean_object* v___x_674_; lean_object* v_bs_x27_675_; lean_object* v___x_676_; size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; 
v_v_673_ = lean_array_uget(v_bs_671_, v_i_670_);
v___x_674_ = lean_unsigned_to_nat(0u);
v_bs_x27_675_ = lean_array_uset(v_bs_671_, v_i_670_, v___x_674_);
v___x_676_ = l_Lean_Expr_fvarId_x21(v_v_673_);
lean_dec(v_v_673_);
v___x_677_ = ((size_t)1ULL);
v___x_678_ = lean_usize_add(v_i_670_, v___x_677_);
v___x_679_ = lean_array_uset(v_bs_x27_675_, v_i_670_, v___x_676_);
v_i_670_ = v___x_678_;
v_bs_671_ = v___x_679_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2___boxed(lean_object* v_sz_681_, lean_object* v_i_682_, lean_object* v_bs_683_){
_start:
{
size_t v_sz_boxed_684_; size_t v_i_boxed_685_; lean_object* v_res_686_; 
v_sz_boxed_684_ = lean_unbox_usize(v_sz_681_);
lean_dec(v_sz_681_);
v_i_boxed_685_ = lean_unbox_usize(v_i_682_);
lean_dec(v_i_682_);
v_res_686_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_boxed_684_, v_i_boxed_685_, v_bs_683_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(lean_object* v_mvarId_691_, lean_object* v_max_692_, lean_object* v_names_693_, uint8_t v_hygienic_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_nat_dec_eq(v_max_692_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_st_ref_get(v_a_700_);
lean_inc(v_mvarId_691_);
v___x_705_ = l_Lean_MVarId_getDecl(v_mvarId_691_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v_env_707_; lean_object* v_userName_708_; lean_object* v_lctx_709_; lean_object* v_type_710_; lean_object* v_localInstances_711_; lean_object* v___x_712_; lean_object* v___f_713_; lean_object* v___f_714_; lean_object* v___f_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
v_env_707_ = lean_ctor_get(v___x_704_, 0);
lean_inc_ref(v_env_707_);
lean_dec(v___x_704_);
v_userName_708_ = lean_ctor_get(v_a_706_, 0);
lean_inc(v_userName_708_);
v_lctx_709_ = lean_ctor_get(v_a_706_, 1);
lean_inc_ref_n(v_lctx_709_, 2);
v_type_710_ = lean_ctor_get(v_a_706_, 2);
lean_inc_ref_n(v_type_710_, 2);
v_localInstances_711_ = lean_ctor_get(v_a_706_, 4);
lean_inc_ref_n(v_localInstances_711_, 2);
lean_dec(v_a_706_);
v___x_712_ = lean_box(v_hygienic_694_);
v___f_713_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed), 10, 2);
lean_closure_set(v___f_713_, 0, v_names_693_);
lean_closure_set(v___f_713_, 1, v___x_712_);
lean_inc(v_max_692_);
v___f_714_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed), 18, 7);
lean_closure_set(v___f_714_, 0, v___x_702_);
lean_closure_set(v___f_714_, 1, v_userName_708_);
lean_closure_set(v___f_714_, 2, v_lctx_709_);
lean_closure_set(v___f_714_, 3, v_localInstances_711_);
lean_closure_set(v___f_714_, 4, v_type_710_);
lean_closure_set(v___f_714_, 5, v_max_692_);
lean_closure_set(v___f_714_, 6, v_mvarId_691_);
v___f_715_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2___boxed), 4, 1);
lean_closure_set(v___f_715_, 0, v_env_707_);
v___x_716_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0));
v___x_717_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(v_max_692_, v___f_714_, v___f_713_, v___f_715_, v___x_702_, v_lctx_709_, v_localInstances_711_, v___x_716_, v_type_710_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_max_692_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_737_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_737_ == 0)
{
v___x_720_ = v___x_717_;
v_isShared_721_ = v_isSharedCheck_737_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_737_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v_fst_722_; lean_object* v_snd_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_736_; 
v_fst_722_ = lean_ctor_get(v_a_718_, 0);
v_snd_723_ = lean_ctor_get(v_a_718_, 1);
v_isSharedCheck_736_ = !lean_is_exclusive(v_a_718_);
if (v_isSharedCheck_736_ == 0)
{
v___x_725_ = v_a_718_;
v_isShared_726_ = v_isSharedCheck_736_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_snd_723_);
lean_inc(v_fst_722_);
lean_dec(v_a_718_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_736_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
size_t v_sz_727_; size_t v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v_sz_727_ = lean_array_size(v_fst_722_);
v___x_728_ = ((size_t)0ULL);
v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_727_, v___x_728_, v_fst_722_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_729_);
v___x_731_ = v___x_725_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_snd_723_);
v___x_731_ = v_reuseFailAlloc_735_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_733_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_731_);
v___x_733_ = v___x_720_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
v_a_738_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_717_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_717_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec(v___x_704_);
lean_dec_ref(v_names_693_);
lean_dec(v_max_692_);
lean_dec(v_mvarId_691_);
v_a_746_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_705_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_705_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec_ref(v_names_693_);
lean_dec(v_max_692_);
v___x_754_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v_mvarId_691_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___boxed(lean_object* v_mvarId_757_, lean_object* v_max_758_, lean_object* v_names_759_, lean_object* v_hygienic_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
uint8_t v_hygienic_boxed_768_; lean_object* v_res_769_; 
v_hygienic_boxed_768_ = lean_unbox(v_hygienic_760_);
v_res_769_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_757_, v_max_758_, v_names_759_, v_hygienic_boxed_768_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(lean_object* v_mvarId_770_, lean_object* v_fvars_771_, lean_object* v_mvarIdPending_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_770_, v_fvars_771_, v_mvarIdPending_772_, v___y_774_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___boxed(lean_object* v_mvarId_779_, lean_object* v_fvars_780_, lean_object* v_mvarIdPending_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(v_mvarId_779_, v_fvars_780_, v_mvarIdPending_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(lean_object* v_mvarId_788_, lean_object* v_val_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_788_, v_val_789_, v___y_791_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___boxed(lean_object* v_mvarId_796_, lean_object* v_val_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(v_mvarId_796_, v_val_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0(lean_object* v_00_u03b2_804_, lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_x_805_, v_x_806_, v_x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_809_, lean_object* v_x_810_, size_t v_x_811_, size_t v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_810_, v_x_811_, v_x_812_, v_x_813_, v_x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_816_, lean_object* v_x_817_, lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_x_821_){
_start:
{
size_t v_x_6419__boxed_822_; size_t v_x_6420__boxed_823_; lean_object* v_res_824_; 
v_x_6419__boxed_822_ = lean_unbox_usize(v_x_818_);
lean_dec(v_x_818_);
v_x_6420__boxed_823_ = lean_unbox_usize(v_x_819_);
lean_dec(v_x_819_);
v_res_824_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(v_00_u03b2_816_, v_x_817_, v_x_6419__boxed_822_, v_x_6420__boxed_823_, v_x_820_, v_x_821_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_825_, lean_object* v_n_826_, lean_object* v_k_827_, lean_object* v_v_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(v_n_826_, v_k_827_, v_v_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_830_, size_t v_depth_831_, lean_object* v_keys_832_, lean_object* v_vals_833_, lean_object* v_heq_834_, lean_object* v_i_835_, lean_object* v_entries_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_831_, v_keys_832_, v_vals_833_, v_i_835_, v_entries_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_838_, lean_object* v_depth_839_, lean_object* v_keys_840_, lean_object* v_vals_841_, lean_object* v_heq_842_, lean_object* v_i_843_, lean_object* v_entries_844_){
_start:
{
size_t v_depth_boxed_845_; lean_object* v_res_846_; 
v_depth_boxed_845_ = lean_unbox_usize(v_depth_839_);
lean_dec(v_depth_839_);
v_res_846_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_838_, v_depth_boxed_845_, v_keys_840_, v_vals_841_, v_heq_842_, v_i_843_, v_entries_844_);
lean_dec_ref(v_vals_841_);
lean_dec_ref(v_keys_840_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_x_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_x_848_, v_x_849_, v_x_850_, v_x_851_);
return v___x_852_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat(void){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = lean_unsigned_to_nat(1000000u);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx(lean_object* v_x_854_){
_start:
{
if (lean_obj_tag(v_x_854_) == 0)
{
lean_object* v___x_855_; 
v___x_855_ = lean_unsigned_to_nat(0u);
return v___x_855_;
}
else
{
lean_object* v___x_856_; 
v___x_856_ = lean_unsigned_to_nat(1u);
return v___x_856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx___boxed(lean_object* v_x_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Meta_Sym_IntrosResult_ctorIdx(v_x_857_);
lean_dec(v_x_857_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(lean_object* v_t_859_, lean_object* v_k_860_){
_start:
{
if (lean_obj_tag(v_t_859_) == 0)
{
return v_k_860_;
}
else
{
lean_object* v_newDecls_861_; lean_object* v_mvarId_862_; lean_object* v___x_863_; 
v_newDecls_861_ = lean_ctor_get(v_t_859_, 0);
lean_inc_ref(v_newDecls_861_);
v_mvarId_862_ = lean_ctor_get(v_t_859_, 1);
lean_inc(v_mvarId_862_);
lean_dec_ref_known(v_t_859_, 2);
v___x_863_ = lean_apply_2(v_k_860_, v_newDecls_861_, v_mvarId_862_);
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim(lean_object* v_motive_864_, lean_object* v_ctorIdx_865_, lean_object* v_t_866_, lean_object* v_h_867_, lean_object* v_k_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_866_, v_k_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___boxed(lean_object* v_motive_870_, lean_object* v_ctorIdx_871_, lean_object* v_t_872_, lean_object* v_h_873_, lean_object* v_k_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_Meta_Sym_IntrosResult_ctorElim(v_motive_870_, v_ctorIdx_871_, v_t_872_, v_h_873_, v_k_874_);
lean_dec(v_ctorIdx_871_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim___redArg(lean_object* v_t_876_, lean_object* v_failed_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_876_, v_failed_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim(lean_object* v_motive_879_, lean_object* v_t_880_, lean_object* v_h_881_, lean_object* v_failed_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_880_, v_failed_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim___redArg(lean_object* v_t_884_, lean_object* v_goal_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_884_, v_goal_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim(lean_object* v_motive_887_, lean_object* v_t_888_, lean_object* v_h_889_, lean_object* v_goal_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_888_, v_goal_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros(lean_object* v_mvarId_892_, lean_object* v_names_893_, uint8_t v_hygienic_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_result_903_; lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_919_ = lean_array_get_size(v_names_893_);
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = lean_nat_dec_eq(v___x_919_, v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; 
v___x_922_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_892_, v___x_919_, v_names_893_, v_hygienic_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_922_, 1);
v_result_903_ = v_a_923_;
goto v___jp_902_;
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
v_a_924_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_922_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_922_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec_ref(v_names_893_);
v___x_932_ = lean_unsigned_to_nat(1000000u);
v___x_933_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
v___x_934_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_892_, v___x_932_, v___x_933_, v_hygienic_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_934_, 1);
v_result_903_ = v_a_935_;
goto v___jp_902_;
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
v_a_936_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_934_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_934_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
v___jp_902_:
{
lean_object* v_fst_904_; lean_object* v_snd_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_918_; 
v_fst_904_ = lean_ctor_get(v_result_903_, 0);
v_snd_905_ = lean_ctor_get(v_result_903_, 1);
v_isSharedCheck_918_ = !lean_is_exclusive(v_result_903_);
if (v_isSharedCheck_918_ == 0)
{
v___x_907_ = v_result_903_;
v_isShared_908_ = v_isSharedCheck_918_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_snd_905_);
lean_inc(v_fst_904_);
lean_dec(v_result_903_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_918_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_909_ = lean_array_get_size(v_fst_904_);
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = lean_nat_dec_eq(v___x_909_, v___x_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_913_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 1);
v___x_913_ = v___x_907_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_fst_904_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_snd_905_);
v___x_913_ = v_reuseFailAlloc_915_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; 
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; 
lean_del_object(v___x_907_);
lean_dec(v_snd_905_);
lean_dec(v_fst_904_);
v___x_916_ = lean_box(0);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros___boxed(lean_object* v_mvarId_944_, lean_object* v_names_945_, lean_object* v_hygienic_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
uint8_t v_hygienic_boxed_954_; lean_object* v_res_955_; 
v_hygienic_boxed_954_ = lean_unbox(v_hygienic_946_);
v_res_955_ = l_Lean_Meta_Sym_intros(v_mvarId_944_, v_names_945_, v_hygienic_boxed_954_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN(lean_object* v_mvarId_956_, lean_object* v_num_957_, uint8_t v_hygienic_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
lean_inc(v_num_957_);
v___x_967_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_956_, v_num_957_, v___x_966_, v_hygienic_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_990_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_990_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_990_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_990_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v_fst_972_; lean_object* v_snd_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_989_; 
v_fst_972_ = lean_ctor_get(v_a_968_, 0);
v_snd_973_ = lean_ctor_get(v_a_968_, 1);
v_isSharedCheck_989_ = !lean_is_exclusive(v_a_968_);
if (v_isSharedCheck_989_ == 0)
{
v___x_975_ = v_a_968_;
v_isShared_976_ = v_isSharedCheck_989_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_snd_973_);
lean_inc(v_fst_972_);
lean_dec(v_a_968_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_989_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_977_ = lean_array_get_size(v_fst_972_);
v___x_978_ = lean_nat_dec_eq(v___x_977_, v_num_957_);
lean_dec(v_num_957_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_981_; 
lean_del_object(v___x_975_);
lean_dec(v_snd_973_);
lean_dec(v_fst_972_);
v___x_979_ = lean_box(0);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_979_);
v___x_981_ = v___x_970_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
else
{
lean_object* v___x_984_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set_tag(v___x_975_, 1);
v___x_984_ = v___x_975_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_fst_972_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_snd_973_);
v___x_984_ = v_reuseFailAlloc_988_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_984_);
v___x_986_ = v___x_970_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec(v_num_957_);
v_a_991_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_967_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_967_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN___boxed(lean_object* v_mvarId_999_, lean_object* v_num_1000_, lean_object* v_hygienic_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
uint8_t v_hygienic_boxed_1009_; lean_object* v_res_1010_; 
v_hygienic_boxed_1009_ = lean_unbox(v_hygienic_1001_);
v_res_1010_ = l_Lean_Meta_Sym_introN(v_mvarId_999_, v_num_1000_, v_hygienic_boxed_1009_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
return v_res_1010_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_IsClass(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Intro(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
