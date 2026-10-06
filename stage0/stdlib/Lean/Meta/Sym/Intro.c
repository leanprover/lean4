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
uint8_t l_Lean_LocalDeclKind_ofBinderName(lean_object*);
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
lean_object* lean_obj_tag_nat(lean_object*);
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
v___x_160_ = l_Lean_LocalDeclKind_ofBinderName(v_a_159_);
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
v___x_215_ = l_Lean_LocalDeclKind_ofBinderName(v_a_214_);
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
size_t v_x_5175__boxed_478_; size_t v_x_5176__boxed_479_; lean_object* v_res_480_; 
v_x_5175__boxed_478_ = lean_unbox_usize(v_x_474_);
lean_dec(v_x_474_);
v_x_5176__boxed_479_ = lean_unbox_usize(v_x_475_);
lean_dec(v_x_475_);
v_res_480_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_473_, v_x_5175__boxed_478_, v_x_5176__boxed_479_, v_x_476_, v_x_477_);
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
lean_object* v___x_492_; lean_object* v_mctx_493_; lean_object* v_cache_494_; lean_object* v_zetaDeltaFVarIds_495_; lean_object* v_postponed_496_; lean_object* v_diag_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_527_; 
v___x_492_ = lean_st_ref_take(v___y_490_);
v_mctx_493_ = lean_ctor_get(v___x_492_, 0);
v_cache_494_ = lean_ctor_get(v___x_492_, 1);
v_zetaDeltaFVarIds_495_ = lean_ctor_get(v___x_492_, 2);
v_postponed_496_ = lean_ctor_get(v___x_492_, 3);
v_diag_497_ = lean_ctor_get(v___x_492_, 4);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_527_ == 0)
{
v___x_499_ = v___x_492_;
v_isShared_500_ = v_isSharedCheck_527_;
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
v_isShared_500_ = v_isSharedCheck_527_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v_depth_501_; lean_object* v_levelAssignDepth_502_; lean_object* v_lmvarCounter_503_; lean_object* v_mvarCounter_504_; lean_object* v_lDecls_505_; lean_object* v_decls_506_; lean_object* v_userNames_507_; lean_object* v_lAssignment_508_; lean_object* v_eAssignment_509_; lean_object* v_dAssignment_510_; lean_object* v_instanceTypedMVars_511_; lean_object* v_synthNormMemo_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_526_; 
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
v_synthNormMemo_512_ = lean_ctor_get(v_mctx_493_, 11);
v_isSharedCheck_526_ = !lean_is_exclusive(v_mctx_493_);
if (v_isSharedCheck_526_ == 0)
{
v___x_514_ = v_mctx_493_;
v_isShared_515_ = v_isSharedCheck_526_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_synthNormMemo_512_);
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
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_526_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_516_ = lean_box(0);
v___x_517_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_eAssignment_509_, v_mvarId_488_, v_val_489_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 8, v___x_517_);
v___x_519_ = v___x_514_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_depth_501_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_levelAssignDepth_502_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v_lmvarCounter_503_);
lean_ctor_set(v_reuseFailAlloc_525_, 3, v_mvarCounter_504_);
lean_ctor_set(v_reuseFailAlloc_525_, 4, v_lDecls_505_);
lean_ctor_set(v_reuseFailAlloc_525_, 5, v_decls_506_);
lean_ctor_set(v_reuseFailAlloc_525_, 6, v_userNames_507_);
lean_ctor_set(v_reuseFailAlloc_525_, 7, v_lAssignment_508_);
lean_ctor_set(v_reuseFailAlloc_525_, 8, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_525_, 9, v_dAssignment_510_);
lean_ctor_set(v_reuseFailAlloc_525_, 10, v_instanceTypedMVars_511_);
lean_ctor_set(v_reuseFailAlloc_525_, 11, v_synthNormMemo_512_);
v___x_519_ = v_reuseFailAlloc_525_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_521_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_519_);
v___x_521_ = v___x_499_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_cache_494_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_zetaDeltaFVarIds_495_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v_postponed_496_);
lean_ctor_set(v_reuseFailAlloc_524_, 4, v_diag_497_);
v___x_521_ = v_reuseFailAlloc_524_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_st_ref_put(v___y_490_, v___x_521_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_516_);
return v___x_523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg___boxed(lean_object* v_mvarId_528_, lean_object* v_val_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_528_, v_val_529_, v___y_530_);
lean_dec(v___y_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(lean_object* v_mvarId_533_, lean_object* v_fvars_534_, lean_object* v_mvarIdPending_535_, lean_object* v___y_536_){
_start:
{
lean_object* v___x_538_; lean_object* v_mctx_539_; lean_object* v_cache_540_; lean_object* v_zetaDeltaFVarIds_541_; lean_object* v_postponed_542_; lean_object* v_diag_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_574_; 
v___x_538_ = lean_st_ref_take(v___y_536_);
v_mctx_539_ = lean_ctor_get(v___x_538_, 0);
v_cache_540_ = lean_ctor_get(v___x_538_, 1);
v_zetaDeltaFVarIds_541_ = lean_ctor_get(v___x_538_, 2);
v_postponed_542_ = lean_ctor_get(v___x_538_, 3);
v_diag_543_ = lean_ctor_get(v___x_538_, 4);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_574_ == 0)
{
v___x_545_ = v___x_538_;
v_isShared_546_ = v_isSharedCheck_574_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_diag_543_);
lean_inc(v_postponed_542_);
lean_inc(v_zetaDeltaFVarIds_541_);
lean_inc(v_cache_540_);
lean_inc(v_mctx_539_);
lean_dec(v___x_538_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_574_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v_depth_547_; lean_object* v_levelAssignDepth_548_; lean_object* v_lmvarCounter_549_; lean_object* v_mvarCounter_550_; lean_object* v_lDecls_551_; lean_object* v_decls_552_; lean_object* v_userNames_553_; lean_object* v_lAssignment_554_; lean_object* v_eAssignment_555_; lean_object* v_dAssignment_556_; lean_object* v_instanceTypedMVars_557_; lean_object* v_synthNormMemo_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_573_; 
v_depth_547_ = lean_ctor_get(v_mctx_539_, 0);
v_levelAssignDepth_548_ = lean_ctor_get(v_mctx_539_, 1);
v_lmvarCounter_549_ = lean_ctor_get(v_mctx_539_, 2);
v_mvarCounter_550_ = lean_ctor_get(v_mctx_539_, 3);
v_lDecls_551_ = lean_ctor_get(v_mctx_539_, 4);
v_decls_552_ = lean_ctor_get(v_mctx_539_, 5);
v_userNames_553_ = lean_ctor_get(v_mctx_539_, 6);
v_lAssignment_554_ = lean_ctor_get(v_mctx_539_, 7);
v_eAssignment_555_ = lean_ctor_get(v_mctx_539_, 8);
v_dAssignment_556_ = lean_ctor_get(v_mctx_539_, 9);
v_instanceTypedMVars_557_ = lean_ctor_get(v_mctx_539_, 10);
v_synthNormMemo_558_ = lean_ctor_get(v_mctx_539_, 11);
v_isSharedCheck_573_ = !lean_is_exclusive(v_mctx_539_);
if (v_isSharedCheck_573_ == 0)
{
v___x_560_ = v_mctx_539_;
v_isShared_561_ = v_isSharedCheck_573_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_synthNormMemo_558_);
lean_inc(v_instanceTypedMVars_557_);
lean_inc(v_dAssignment_556_);
lean_inc(v_eAssignment_555_);
lean_inc(v_lAssignment_554_);
lean_inc(v_userNames_553_);
lean_inc(v_decls_552_);
lean_inc(v_lDecls_551_);
lean_inc(v_mvarCounter_550_);
lean_inc(v_lmvarCounter_549_);
lean_inc(v_levelAssignDepth_548_);
lean_inc(v_depth_547_);
lean_dec(v_mctx_539_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_573_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_562_ = lean_box(0);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v_fvars_534_);
lean_ctor_set(v___x_563_, 1, v_mvarIdPending_535_);
v___x_564_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_dAssignment_556_, v_mvarId_533_, v___x_563_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 9, v___x_564_);
v___x_566_ = v___x_560_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_depth_547_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_levelAssignDepth_548_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_lmvarCounter_549_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_mvarCounter_550_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v_lDecls_551_);
lean_ctor_set(v_reuseFailAlloc_572_, 5, v_decls_552_);
lean_ctor_set(v_reuseFailAlloc_572_, 6, v_userNames_553_);
lean_ctor_set(v_reuseFailAlloc_572_, 7, v_lAssignment_554_);
lean_ctor_set(v_reuseFailAlloc_572_, 8, v_eAssignment_555_);
lean_ctor_set(v_reuseFailAlloc_572_, 9, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_572_, 10, v_instanceTypedMVars_557_);
lean_ctor_set(v_reuseFailAlloc_572_, 11, v_synthNormMemo_558_);
v___x_566_ = v_reuseFailAlloc_572_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_568_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_566_);
v___x_568_ = v___x_545_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_cache_540_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_zetaDeltaFVarIds_541_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v_postponed_542_);
lean_ctor_set(v_reuseFailAlloc_571_, 4, v_diag_543_);
v___x_568_ = v_reuseFailAlloc_571_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_st_ref_put(v___y_536_, v___x_568_);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_562_);
return v___x_570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg___boxed(lean_object* v_mvarId_575_, lean_object* v_fvars_576_, lean_object* v_mvarIdPending_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_575_, v_fvars_576_, v_mvarIdPending_577_, v___y_578_);
lean_dec(v___y_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(lean_object* v___x_581_, lean_object* v_userName_582_, lean_object* v_lctx_583_, lean_object* v_localInstances_584_, lean_object* v_type_585_, lean_object* v_max_586_, lean_object* v_mvarId_587_, lean_object* v_lctx_588_, lean_object* v_localInsts_589_, lean_object* v_fvars_590_, lean_object* v_type_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = lean_array_get_size(v_fvars_590_);
v___x_600_ = lean_nat_dec_eq(v___x_599_, v___x_581_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; 
lean_inc_ref(v_fvars_590_);
lean_inc(v___x_581_);
v___x_601_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_591_, v___x_581_, v___x_599_, v_fvars_590_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; uint8_t v___x_603_; lean_object* v___x_604_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
v___x_603_ = 2;
lean_inc(v___x_581_);
v___x_604_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_588_, v_localInsts_589_, v_a_602_, v___x_603_, v_userName_582_, v___x_581_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_606_; lean_object* v___y_608_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v___x_606_ = l_Lean_Expr_mvarId_x21(v_a_605_);
lean_dec(v_a_605_);
v___x_618_ = lean_box(0);
lean_inc(v___x_581_);
lean_inc_ref(v_type_585_);
v___x_619_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_583_, v_localInstances_584_, v_type_585_, v___x_603_, v___x_618_, v___x_581_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc_n(v_a_620_, 2);
lean_dec_ref_known(v___x_619_, 1);
v___x_621_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkAppBVars(v_a_620_, v___x_599_);
v___x_622_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(v_max_586_, v___x_581_, v_type_585_, v___x_621_);
lean_dec_ref(v___x_621_);
lean_dec(v___x_581_);
v___x_623_ = l_Lean_Expr_mvarId_x21(v_a_620_);
lean_dec(v_a_620_);
lean_inc(v___x_606_);
lean_inc_ref(v_fvars_590_);
v___x_624_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v___x_623_, v_fvars_590_, v___x_606_, v___y_595_);
lean_dec_ref(v___x_624_);
v___x_625_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_587_, v___x_622_, v___y_595_);
v___y_608_ = v___x_625_;
goto v___jp_607_;
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec(v___x_606_);
lean_dec_ref(v_fvars_590_);
lean_dec(v_mvarId_587_);
lean_dec_ref(v_type_585_);
lean_dec(v___x_581_);
v_a_626_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_619_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_619_);
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
v___jp_607_:
{
lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_616_; 
v_isSharedCheck_616_ = !lean_is_exclusive(v___y_608_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v___y_608_, 0);
lean_dec(v_unused_617_);
v___x_610_ = v___y_608_;
v_isShared_611_ = v_isSharedCheck_616_;
goto v_resetjp_609_;
}
else
{
lean_dec(v___y_608_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_616_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v_fvars_590_);
lean_ctor_set(v___x_612_, 1, v___x_606_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_612_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec_ref(v_fvars_590_);
lean_dec(v_mvarId_587_);
lean_dec_ref(v_type_585_);
lean_dec_ref(v_localInstances_584_);
lean_dec_ref(v_lctx_583_);
lean_dec(v___x_581_);
v_a_634_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_604_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_604_);
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
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec_ref(v_fvars_590_);
lean_dec_ref(v_localInsts_589_);
lean_dec_ref(v_lctx_588_);
lean_dec(v_mvarId_587_);
lean_dec_ref(v_type_585_);
lean_dec_ref(v_localInstances_584_);
lean_dec_ref(v_lctx_583_);
lean_dec(v_userName_582_);
lean_dec(v___x_581_);
v_a_642_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_601_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_601_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec_ref(v_type_591_);
lean_dec_ref(v_fvars_590_);
lean_dec_ref(v_localInsts_589_);
lean_dec_ref(v_lctx_588_);
lean_dec_ref(v_type_585_);
lean_dec_ref(v_localInstances_584_);
lean_dec_ref(v_lctx_583_);
lean_dec(v_userName_582_);
v___x_650_ = lean_mk_empty_array_with_capacity(v___x_581_);
lean_dec(v___x_581_);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v_mvarId_587_);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2___boxed(lean_object** _args){
lean_object* v___x_653_ = _args[0];
lean_object* v_userName_654_ = _args[1];
lean_object* v_lctx_655_ = _args[2];
lean_object* v_localInstances_656_ = _args[3];
lean_object* v_type_657_ = _args[4];
lean_object* v_max_658_ = _args[5];
lean_object* v_mvarId_659_ = _args[6];
lean_object* v_lctx_660_ = _args[7];
lean_object* v_localInsts_661_ = _args[8];
lean_object* v_fvars_662_ = _args[9];
lean_object* v_type_663_ = _args[10];
lean_object* v___y_664_ = _args[11];
lean_object* v___y_665_ = _args[12];
lean_object* v___y_666_ = _args[13];
lean_object* v___y_667_ = _args[14];
lean_object* v___y_668_ = _args[15];
lean_object* v___y_669_ = _args[16];
lean_object* v___y_670_ = _args[17];
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(v___x_653_, v_userName_654_, v_lctx_655_, v_localInstances_656_, v_type_657_, v_max_658_, v_mvarId_659_, v_lctx_660_, v_localInsts_661_, v_fvars_662_, v_type_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v_max_658_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(size_t v_sz_672_, size_t v_i_673_, lean_object* v_bs_674_){
_start:
{
uint8_t v___x_675_; 
v___x_675_ = lean_usize_dec_lt(v_i_673_, v_sz_672_);
if (v___x_675_ == 0)
{
return v_bs_674_;
}
else
{
lean_object* v_v_676_; lean_object* v___x_677_; lean_object* v_bs_x27_678_; lean_object* v___x_679_; size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; 
v_v_676_ = lean_array_uget(v_bs_674_, v_i_673_);
v___x_677_ = lean_unsigned_to_nat(0u);
v_bs_x27_678_ = lean_array_uset(v_bs_674_, v_i_673_, v___x_677_);
v___x_679_ = l_Lean_Expr_fvarId_x21(v_v_676_);
lean_dec(v_v_676_);
v___x_680_ = ((size_t)1ULL);
v___x_681_ = lean_usize_add(v_i_673_, v___x_680_);
v___x_682_ = lean_array_uset(v_bs_x27_678_, v_i_673_, v___x_679_);
v_i_673_ = v___x_681_;
v_bs_674_ = v___x_682_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2___boxed(lean_object* v_sz_684_, lean_object* v_i_685_, lean_object* v_bs_686_){
_start:
{
size_t v_sz_boxed_687_; size_t v_i_boxed_688_; lean_object* v_res_689_; 
v_sz_boxed_687_ = lean_unbox_usize(v_sz_684_);
lean_dec(v_sz_684_);
v_i_boxed_688_ = lean_unbox_usize(v_i_685_);
lean_dec(v_i_685_);
v_res_689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_boxed_687_, v_i_boxed_688_, v_bs_686_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(lean_object* v_mvarId_694_, lean_object* v_max_695_, lean_object* v_names_696_, uint8_t v_hygienic_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_nat_dec_eq(v_max_695_, v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___f_708_; lean_object* v___x_709_; lean_object* v_env_710_; lean_object* v___f_711_; lean_object* v___x_712_; 
v___x_707_ = lean_box(v_hygienic_697_);
v___f_708_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed), 10, 2);
lean_closure_set(v___f_708_, 0, v_names_696_);
lean_closure_set(v___f_708_, 1, v___x_707_);
v___x_709_ = lean_st_ref_get(v_a_703_);
v_env_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc_ref(v_env_710_);
lean_dec(v___x_709_);
v___f_711_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed), 4, 1);
lean_closure_set(v___f_711_, 0, v_env_710_);
lean_inc(v_mvarId_694_);
v___x_712_ = l_Lean_MVarId_getDecl(v_mvarId_694_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v_userName_714_; lean_object* v_lctx_715_; lean_object* v_type_716_; lean_object* v_localInstances_717_; lean_object* v___f_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_712_, 1);
v_userName_714_ = lean_ctor_get(v_a_713_, 0);
lean_inc(v_userName_714_);
v_lctx_715_ = lean_ctor_get(v_a_713_, 1);
lean_inc_ref_n(v_lctx_715_, 2);
v_type_716_ = lean_ctor_get(v_a_713_, 2);
lean_inc_ref_n(v_type_716_, 2);
v_localInstances_717_ = lean_ctor_get(v_a_713_, 4);
lean_inc_ref_n(v_localInstances_717_, 2);
lean_dec(v_a_713_);
lean_inc(v_max_695_);
v___f_718_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2___boxed), 18, 7);
lean_closure_set(v___f_718_, 0, v___x_705_);
lean_closure_set(v___f_718_, 1, v_userName_714_);
lean_closure_set(v___f_718_, 2, v_lctx_715_);
lean_closure_set(v___f_718_, 3, v_localInstances_717_);
lean_closure_set(v___f_718_, 4, v_type_716_);
lean_closure_set(v___f_718_, 5, v_max_695_);
lean_closure_set(v___f_718_, 6, v_mvarId_694_);
v___x_719_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0));
v___x_720_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(v_max_695_, v___f_718_, v___f_708_, v___f_711_, v___x_705_, v_lctx_715_, v_localInstances_717_, v___x_719_, v_type_716_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
lean_dec(v_max_695_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_740_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_740_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_740_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_740_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_fst_725_; lean_object* v_snd_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_739_; 
v_fst_725_ = lean_ctor_get(v_a_721_, 0);
v_snd_726_ = lean_ctor_get(v_a_721_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_a_721_);
if (v_isSharedCheck_739_ == 0)
{
v___x_728_ = v_a_721_;
v_isShared_729_ = v_isSharedCheck_739_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_snd_726_);
lean_inc(v_fst_725_);
lean_dec(v_a_721_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_739_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
size_t v_sz_730_; size_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
v_sz_730_ = lean_array_size(v_fst_725_);
v___x_731_ = ((size_t)0ULL);
v___x_732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_730_, v___x_731_, v_fst_725_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_732_);
v___x_734_ = v___x_728_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_snd_726_);
v___x_734_ = v_reuseFailAlloc_738_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_736_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_734_);
v___x_736_ = v___x_723_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
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
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
v_a_741_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_720_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_720_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec_ref(v___f_711_);
lean_dec_ref(v___f_708_);
lean_dec(v_max_695_);
lean_dec(v_mvarId_694_);
v_a_749_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_712_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_712_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec_ref(v_names_696_);
lean_dec(v_max_695_);
v___x_757_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v_mvarId_694_);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___boxed(lean_object* v_mvarId_760_, lean_object* v_max_761_, lean_object* v_names_762_, lean_object* v_hygienic_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
uint8_t v_hygienic_boxed_771_; lean_object* v_res_772_; 
v_hygienic_boxed_771_ = lean_unbox(v_hygienic_763_);
v_res_772_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_760_, v_max_761_, v_names_762_, v_hygienic_boxed_771_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(lean_object* v_mvarId_773_, lean_object* v_fvars_774_, lean_object* v_mvarIdPending_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_773_, v_fvars_774_, v_mvarIdPending_775_, v___y_777_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___boxed(lean_object* v_mvarId_782_, lean_object* v_fvars_783_, lean_object* v_mvarIdPending_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(v_mvarId_782_, v_fvars_783_, v_mvarIdPending_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(lean_object* v_mvarId_791_, lean_object* v_val_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_791_, v_val_792_, v___y_794_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___boxed(lean_object* v_mvarId_799_, lean_object* v_val_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(v_mvarId_799_, v_val_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0(lean_object* v_00_u03b2_807_, lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_x_808_, v_x_809_, v_x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_812_, lean_object* v_x_813_, size_t v_x_814_, size_t v_x_815_, lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_813_, v_x_814_, v_x_815_, v_x_816_, v_x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_819_, lean_object* v_x_820_, lean_object* v_x_821_, lean_object* v_x_822_, lean_object* v_x_823_, lean_object* v_x_824_){
_start:
{
size_t v_x_5736__boxed_825_; size_t v_x_5737__boxed_826_; lean_object* v_res_827_; 
v_x_5736__boxed_825_ = lean_unbox_usize(v_x_821_);
lean_dec(v_x_821_);
v_x_5737__boxed_826_ = lean_unbox_usize(v_x_822_);
lean_dec(v_x_822_);
v_res_827_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(v_00_u03b2_819_, v_x_820_, v_x_5736__boxed_825_, v_x_5737__boxed_826_, v_x_823_, v_x_824_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_828_, lean_object* v_n_829_, lean_object* v_k_830_, lean_object* v_v_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(v_n_829_, v_k_830_, v_v_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_833_, size_t v_depth_834_, lean_object* v_keys_835_, lean_object* v_vals_836_, lean_object* v_heq_837_, lean_object* v_i_838_, lean_object* v_entries_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_834_, v_keys_835_, v_vals_836_, v_i_838_, v_entries_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_841_, lean_object* v_depth_842_, lean_object* v_keys_843_, lean_object* v_vals_844_, lean_object* v_heq_845_, lean_object* v_i_846_, lean_object* v_entries_847_){
_start:
{
size_t v_depth_boxed_848_; lean_object* v_res_849_; 
v_depth_boxed_848_ = lean_unbox_usize(v_depth_842_);
lean_dec(v_depth_842_);
v_res_849_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_841_, v_depth_boxed_848_, v_keys_843_, v_vals_844_, v_heq_845_, v_i_846_, v_entries_847_);
lean_dec_ref(v_vals_844_);
lean_dec_ref(v_keys_843_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_850_, lean_object* v_x_851_, lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_x_851_, v_x_852_, v_x_853_, v_x_854_);
return v___x_855_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat(void){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = lean_unsigned_to_nat(1000000u);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx___impl(lean_object* v_x_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = lean_obj_tag_nat(v_x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx___impl___boxed(lean_object* v_x_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Meta_Sym_IntrosResult_ctorIdx___impl(v_x_859_);
lean_dec(v_x_859_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(lean_object* v_t_861_, lean_object* v_k_862_){
_start:
{
if (lean_obj_tag(v_t_861_) == 0)
{
return v_k_862_;
}
else
{
lean_object* v_newDecls_863_; lean_object* v_mvarId_864_; lean_object* v___x_865_; 
v_newDecls_863_ = lean_ctor_get(v_t_861_, 0);
lean_inc_ref(v_newDecls_863_);
v_mvarId_864_ = lean_ctor_get(v_t_861_, 1);
lean_inc(v_mvarId_864_);
lean_dec_ref_known(v_t_861_, 2);
v___x_865_ = lean_apply_2(v_k_862_, v_newDecls_863_, v_mvarId_864_);
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim(lean_object* v_motive_866_, lean_object* v_ctorIdx_867_, lean_object* v_t_868_, lean_object* v_h_869_, lean_object* v_k_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_868_, v_k_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___boxed(lean_object* v_motive_872_, lean_object* v_ctorIdx_873_, lean_object* v_t_874_, lean_object* v_h_875_, lean_object* v_k_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_Meta_Sym_IntrosResult_ctorElim(v_motive_872_, v_ctorIdx_873_, v_t_874_, v_h_875_, v_k_876_);
lean_dec(v_ctorIdx_873_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim___redArg(lean_object* v_t_878_, lean_object* v_failed_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_878_, v_failed_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim(lean_object* v_motive_881_, lean_object* v_t_882_, lean_object* v_h_883_, lean_object* v_failed_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_882_, v_failed_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim___redArg(lean_object* v_t_886_, lean_object* v_goal_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_886_, v_goal_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim(lean_object* v_motive_889_, lean_object* v_t_890_, lean_object* v_h_891_, lean_object* v_goal_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_890_, v_goal_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros(lean_object* v_mvarId_894_, lean_object* v_names_895_, uint8_t v_hygienic_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_result_905_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_921_ = lean_array_get_size(v_names_895_);
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = lean_nat_dec_eq(v___x_921_, v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; 
v___x_924_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_894_, v___x_921_, v_names_895_, v_hygienic_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_924_, 1);
v_result_905_ = v_a_925_;
goto v___jp_904_;
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
v_a_926_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_924_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_924_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec_ref(v_names_895_);
v___x_934_ = lean_unsigned_to_nat(1000000u);
v___x_935_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
v___x_936_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_894_, v___x_934_, v___x_935_, v_hygienic_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref_known(v___x_936_, 1);
v_result_905_ = v_a_937_;
goto v___jp_904_;
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
v_a_938_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_936_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_936_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
v___jp_904_:
{
lean_object* v_fst_906_; lean_object* v_snd_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_920_; 
v_fst_906_ = lean_ctor_get(v_result_905_, 0);
v_snd_907_ = lean_ctor_get(v_result_905_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_result_905_);
if (v_isSharedCheck_920_ == 0)
{
v___x_909_ = v_result_905_;
v_isShared_910_ = v_isSharedCheck_920_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_snd_907_);
lean_inc(v_fst_906_);
lean_dec(v_result_905_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_920_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_911_ = lean_array_get_size(v_fst_906_);
v___x_912_ = lean_unsigned_to_nat(0u);
v___x_913_ = lean_nat_dec_eq(v___x_911_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_915_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set_tag(v___x_909_, 1);
v___x_915_ = v___x_909_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_fst_906_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_snd_907_);
v___x_915_ = v_reuseFailAlloc_917_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; 
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; 
lean_del_object(v___x_909_);
lean_dec(v_snd_907_);
lean_dec(v_fst_906_);
v___x_918_ = lean_box(0);
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros___boxed(lean_object* v_mvarId_946_, lean_object* v_names_947_, lean_object* v_hygienic_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
uint8_t v_hygienic_boxed_956_; lean_object* v_res_957_; 
v_hygienic_boxed_956_ = lean_unbox(v_hygienic_948_);
v_res_957_ = l_Lean_Meta_Sym_intros(v_mvarId_946_, v_names_947_, v_hygienic_boxed_956_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN(lean_object* v_mvarId_958_, lean_object* v_num_959_, uint8_t v_hygienic_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
lean_inc(v_num_959_);
v___x_969_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_958_, v_num_959_, v___x_968_, v_hygienic_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_992_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_992_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_992_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_992_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v_fst_974_; lean_object* v_snd_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_991_; 
v_fst_974_ = lean_ctor_get(v_a_970_, 0);
v_snd_975_ = lean_ctor_get(v_a_970_, 1);
v_isSharedCheck_991_ = !lean_is_exclusive(v_a_970_);
if (v_isSharedCheck_991_ == 0)
{
v___x_977_ = v_a_970_;
v_isShared_978_ = v_isSharedCheck_991_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_snd_975_);
lean_inc(v_fst_974_);
lean_dec(v_a_970_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_991_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_979_ = lean_array_get_size(v_fst_974_);
v___x_980_ = lean_nat_dec_eq(v___x_979_, v_num_959_);
lean_dec(v_num_959_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_983_; 
lean_del_object(v___x_977_);
lean_dec(v_snd_975_);
lean_dec(v_fst_974_);
v___x_981_ = lean_box(0);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_981_);
v___x_983_ = v___x_972_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
else
{
lean_object* v___x_986_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set_tag(v___x_977_, 1);
v___x_986_ = v___x_977_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_fst_974_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_snd_975_);
v___x_986_ = v_reuseFailAlloc_990_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_988_; 
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_986_);
v___x_988_ = v___x_972_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v_num_959_);
v_a_993_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_969_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_969_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN___boxed(lean_object* v_mvarId_1001_, lean_object* v_num_1002_, lean_object* v_hygienic_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
uint8_t v_hygienic_boxed_1011_; lean_object* v_res_1012_; 
v_hygienic_boxed_1011_ = lean_unbox(v_hygienic_1003_);
v_res_1012_ = l_Lean_Meta_Sym_introN(v_mvarId_1001_, v_num_1002_, v_hygienic_boxed_1011_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
return v_res_1012_;
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
