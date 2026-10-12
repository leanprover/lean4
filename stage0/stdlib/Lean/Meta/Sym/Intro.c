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
lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(lean_object* v_fvarId_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = l_Lean_Expr_fvar___override(v_fvarId_39_);
v___x_43_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_42_, v___y_40_);
return v___x_43_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_39_ = stack[0].m_obj;
lean_object* v___y_40_ = stack[1].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(v_fvarId_39_, v___y_40_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg___boxed(lean_object* v_fvarId_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(v_fvarId_45_, v___y_46_);
lean_dec(v___y_46_);
return v_res_48_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(lean_object* v_fvarId_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(v_fvarId_49_, v___y_51_);
return v___x_57_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_49_ = stack[0].m_obj;
lean_object* v___y_50_ = stack[1].m_obj;
lean_object* v___y_51_ = stack[2].m_obj;
lean_object* v___y_52_ = stack[3].m_obj;
lean_object* v___y_53_ = stack[4].m_obj;
lean_object* v___y_54_ = stack[5].m_obj;
lean_object* v___y_55_ = stack[6].m_obj;
lean_object* v_res_58_;
v_res_58_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(v_fvarId_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___boxed(lean_object* v_fvarId_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(v_fvarId_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
return v_res_67_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; lean_object* v_ngen_71_; lean_object* v_namePrefix_72_; lean_object* v_idx_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_103_; 
v___x_70_ = lean_st_ref_get(v___y_68_);
v_ngen_71_ = lean_ctor_get(v___x_70_, 2);
lean_inc_ref(v_ngen_71_);
lean_dec(v___x_70_);
v_namePrefix_72_ = lean_ctor_get(v_ngen_71_, 0);
v_idx_73_ = lean_ctor_get(v_ngen_71_, 1);
v_isSharedCheck_103_ = !lean_is_exclusive(v_ngen_71_);
if (v_isSharedCheck_103_ == 0)
{
v___x_75_ = v_ngen_71_;
v_isShared_76_ = v_isSharedCheck_103_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_idx_73_);
lean_inc(v_namePrefix_72_);
lean_dec(v_ngen_71_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_103_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v_r_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_81_; 
lean_inc(v_idx_73_);
lean_inc(v_namePrefix_72_);
v_r_77_ = l_Lean_Name_num___override(v_namePrefix_72_, v_idx_73_);
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_add(v_idx_73_, v___x_78_);
lean_dec(v_idx_73_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_79_);
v___x_81_ = v___x_75_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_namePrefix_72_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v___x_79_);
v___x_81_ = v_reuseFailAlloc_102_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_object* v___x_82_; lean_object* v_env_83_; lean_object* v_nextMacroScope_84_; lean_object* v_auxDeclNGen_85_; lean_object* v_traceState_86_; lean_object* v_cache_87_; lean_object* v_recordedDeps_88_; lean_object* v_messages_89_; lean_object* v_infoState_90_; lean_object* v_snapshotTasks_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_100_; 
v___x_82_ = lean_st_ref_take(v___y_68_);
v_env_83_ = lean_ctor_get(v___x_82_, 0);
v_nextMacroScope_84_ = lean_ctor_get(v___x_82_, 1);
v_auxDeclNGen_85_ = lean_ctor_get(v___x_82_, 3);
v_traceState_86_ = lean_ctor_get(v___x_82_, 4);
v_cache_87_ = lean_ctor_get(v___x_82_, 5);
v_recordedDeps_88_ = lean_ctor_get(v___x_82_, 6);
v_messages_89_ = lean_ctor_get(v___x_82_, 7);
v_infoState_90_ = lean_ctor_get(v___x_82_, 8);
v_snapshotTasks_91_ = lean_ctor_get(v___x_82_, 9);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v___x_82_, 2);
lean_dec(v_unused_101_);
v___x_93_ = v___x_82_;
v_isShared_94_ = v_isSharedCheck_100_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_snapshotTasks_91_);
lean_inc(v_infoState_90_);
lean_inc(v_messages_89_);
lean_inc(v_recordedDeps_88_);
lean_inc(v_cache_87_);
lean_inc(v_traceState_86_);
lean_inc(v_auxDeclNGen_85_);
lean_inc(v_nextMacroScope_84_);
lean_inc(v_env_83_);
lean_dec(v___x_82_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_100_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 2, v___x_81_);
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_env_83_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_nextMacroScope_84_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_99_, 3, v_auxDeclNGen_85_);
lean_ctor_set(v_reuseFailAlloc_99_, 4, v_traceState_86_);
lean_ctor_set(v_reuseFailAlloc_99_, 5, v_cache_87_);
lean_ctor_set(v_reuseFailAlloc_99_, 6, v_recordedDeps_88_);
lean_ctor_set(v_reuseFailAlloc_99_, 7, v_messages_89_);
lean_ctor_set(v_reuseFailAlloc_99_, 8, v_infoState_90_);
lean_ctor_set(v_reuseFailAlloc_99_, 9, v_snapshotTasks_91_);
v___x_96_ = v_reuseFailAlloc_99_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_st_ref_put(v___y_68_, v___x_96_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v_r_77_);
return v___x_98_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_68_ = stack[0].m_obj;
lean_object* v_res_104_;
v_res_104_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(v___y_68_);
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg___boxed(lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(v___y_105_);
lean_dec(v___y_105_);
return v_res_107_;
}
}
lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___x_115_; lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
v___x_115_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(v___y_113_);
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_108_ = stack[0].m_obj;
lean_object* v___y_109_ = stack[1].m_obj;
lean_object* v___y_110_ = stack[2].m_obj;
lean_object* v___y_111_ = stack[3].m_obj;
lean_object* v___y_112_ = stack[4].m_obj;
lean_object* v___y_113_ = stack[5].m_obj;
lean_object* v_res_124_;
v_res_124_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
stack->m_obj
 = v_res_124_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0___boxed(lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
return v_res_132_;
}
}
lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(lean_object* v_max_133_, lean_object* v_finalize_134_, lean_object* v_mkName_135_, lean_object* v_updateLocalInsts_136_, lean_object* v_i_137_, lean_object* v_lctx_138_, lean_object* v_localInsts_139_, lean_object* v_fvars_140_, lean_object* v_type_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
uint8_t v___x_149_; 
v___x_149_ = lean_nat_dec_le(v_max_133_, v_i_137_);
if (v___x_149_ == 0)
{
switch(lean_obj_tag(v_type_141_))
{
case 10:
{
lean_object* v_expr_150_; 
v_expr_150_ = lean_ctor_get(v_type_141_, 1);
lean_inc_ref(v_expr_150_);
lean_dec_ref_known(v_type_141_, 2);
v_type_141_ = v_expr_150_;
goto _start;
}
case 7:
{
lean_object* v_binderName_152_; lean_object* v_binderType_153_; lean_object* v_body_154_; uint8_t v_binderInfo_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_binderName_152_ = lean_ctor_get(v_type_141_, 0);
lean_inc(v_binderName_152_);
v_binderType_153_ = lean_ctor_get(v_type_141_, 1);
lean_inc_ref(v_binderType_153_);
v_body_154_ = lean_ctor_get(v_type_141_, 2);
lean_inc_ref(v_body_154_);
v_binderInfo_155_ = lean_ctor_get_uint8(v_type_141_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_141_, 3);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_array_get_size(v_fvars_140_);
lean_inc_ref(v_fvars_140_);
v___x_158_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_binderType_153_, v___x_156_, v___x_157_, v_fvars_140_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_160_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_158_, 1);
v___x_160_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_162_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v___x_160_, 1);
lean_inc_ref(v_mkName_135_);
lean_inc(v_a_147_);
lean_inc_ref(v_a_146_);
lean_inc(v_a_145_);
lean_inc_ref(v_a_144_);
lean_inc(v_i_137_);
lean_inc_ref(v_lctx_138_);
v___x_162_ = lean_apply_8(v_mkName_135_, v_lctx_138_, v_binderName_152_, v_i_137_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, lean_box(0));
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_a_163_);
lean_dec_ref_known(v___x_162_, 1);
v___x_164_ = l_Lean_LocalDeclKind_ofBinderName(v_a_163_);
lean_inc(v_a_159_);
lean_inc(v_a_161_);
v___x_165_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_138_, v_a_161_, v_a_163_, v_a_159_, v_binderInfo_155_, v___x_164_);
v___x_166_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(v_a_161_, v_a_143_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc_n(v_a_167_, 2);
lean_dec_ref_known(v___x_166_, 1);
v___x_168_ = lean_array_push(v_fvars_140_, v_a_167_);
lean_inc_ref(v_updateLocalInsts_136_);
v___x_169_ = lean_apply_3(v_updateLocalInsts_136_, v_localInsts_139_, v_a_167_, v_a_159_);
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = lean_nat_add(v_i_137_, v___x_170_);
lean_dec(v_i_137_);
v_i_137_ = v___x_171_;
v_lctx_138_ = v___x_165_;
v_localInsts_139_ = v___x_169_;
v_fvars_140_ = v___x_168_;
v_type_141_ = v_body_154_;
goto _start;
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec_ref(v___x_165_);
lean_dec(v_a_159_);
lean_dec_ref(v_body_154_);
lean_dec_ref(v_fvars_140_);
lean_dec_ref(v_localInsts_139_);
lean_dec(v_i_137_);
lean_dec_ref(v_updateLocalInsts_136_);
lean_dec_ref(v_mkName_135_);
lean_dec_ref(v_finalize_134_);
v_a_173_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_166_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_166_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
lean_dec(v_a_161_);
lean_dec(v_a_159_);
lean_dec_ref(v_body_154_);
lean_dec_ref(v_fvars_140_);
lean_dec_ref(v_localInsts_139_);
lean_dec_ref(v_lctx_138_);
lean_dec(v_i_137_);
lean_dec_ref(v_updateLocalInsts_136_);
lean_dec_ref(v_mkName_135_);
lean_dec_ref(v_finalize_134_);
v_a_181_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_162_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_162_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
else
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
lean_dec(v_a_159_);
lean_dec_ref(v_body_154_);
lean_dec(v_binderName_152_);
lean_dec_ref(v_fvars_140_);
lean_dec_ref(v_localInsts_139_);
lean_dec_ref(v_lctx_138_);
lean_dec(v_i_137_);
lean_dec_ref(v_updateLocalInsts_136_);
lean_dec_ref(v_mkName_135_);
lean_dec_ref(v_finalize_134_);
v_a_189_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_160_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_160_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec_ref(v_body_154_);
lean_dec(v_binderName_152_);
lean_dec_ref(v_fvars_140_);
lean_dec_ref(v_localInsts_139_);
lean_dec_ref(v_lctx_138_);
lean_dec(v_i_137_);
lean_dec_ref(v_updateLocalInsts_136_);
lean_dec_ref(v_mkName_135_);
lean_dec_ref(v_finalize_134_);
v_a_197_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_158_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_158_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
case 8:
{
lean_object* v_declName_205_; lean_object* v_type_206_; lean_object* v_value_207_; lean_object* v_body_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_declName_205_ = lean_ctor_get(v_type_141_, 0);
lean_inc(v_declName_205_);
v_type_206_ = lean_ctor_get(v_type_141_, 1);
lean_inc_ref(v_type_206_);
v_value_207_ = lean_ctor_get(v_type_141_, 2);
lean_inc_ref(v_value_207_);
v_body_208_ = lean_ctor_get(v_type_141_, 3);
lean_inc_ref(v_body_208_);
lean_dec_ref_known(v_type_141_, 4);
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_array_get_size(v_fvars_140_);
lean_inc_ref(v_fvars_140_);
v___x_211_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_206_, v___x_209_, v___x_210_, v_fvars_140_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_213_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
lean_inc_ref(v_fvars_140_);
v___x_213_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_value_207_, v___x_209_, v___x_210_, v_fvars_140_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_215_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_213_, 1);
v___x_215_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_217_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_a_216_);
lean_dec_ref_known(v___x_215_, 1);
lean_inc_ref(v_mkName_135_);
lean_inc(v_a_147_);
lean_inc_ref(v_a_146_);
lean_inc(v_a_145_);
lean_inc_ref(v_a_144_);
lean_inc(v_i_137_);
lean_inc_ref(v_lctx_138_);
v___x_217_ = lean_apply_8(v_mkName_135_, v_lctx_138_, v_declName_205_, v_i_137_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, lean_box(0));
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; uint8_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
lean_dec_ref_known(v___x_217_, 1);
v___x_219_ = l_Lean_LocalDeclKind_ofBinderName(v_a_218_);
lean_inc(v_a_212_);
lean_inc(v_a_216_);
v___x_220_ = l_Lean_LocalContext_mkLetDecl(v_lctx_138_, v_a_216_, v_a_218_, v_a_212_, v_a_214_, v___x_149_, v___x_219_);
v___x_221_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(v_a_216_, v_a_143_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc_n(v_a_222_, 2);
lean_dec_ref_known(v___x_221_, 1);
v___x_223_ = lean_array_push(v_fvars_140_, v_a_222_);
lean_inc_ref(v_updateLocalInsts_136_);
v___x_224_ = lean_apply_3(v_updateLocalInsts_136_, v_localInsts_139_, v_a_222_, v_a_212_);
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = lean_nat_add(v_i_137_, v___x_225_);
lean_dec(v_i_137_);
v_i_137_ = v___x_226_;
v_lctx_138_ = v___x_220_;
v_localInsts_139_ = v___x_224_;
v_fvars_140_ = v___x_223_;
v_type_141_ = v_body_208_;
goto _start;
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec_ref(v___x_220_);
lean_dec(v_a_212_);
lean_dec_ref(v_body_208_);
lean_dec_ref(v_fvars_140_);
lean_dec_ref(v_localInsts_139_);
lean_dec(v_i_137_);
lean_dec_ref(v_updateLocalInsts_136_);
lean_dec_ref(v_mkName_135_);
lean_dec_ref(v_finalize_134_);
v_a_228_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_221_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_221_);
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
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
lean_dec(v_a_216_);
lean_dec(v_a_214_);
lean_dec(v_a_212_);
lean_dec_ref(v_body_208_);
lean_dec_ref(v_fvars_140_);
lean_dec_ref(v_localInsts_139_);
lean_dec_ref(v_lctx_138_);
lean_dec(v_i_137_);
lean_dec_ref(v_updateLocalInsts_136_);
lean_dec_ref(v_mkName_135_);
lean_dec_ref(v_finalize_134_);
v_a_236_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_217_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_217_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec(v_a_214_);
lean_dec(v_a_212_);
lean_dec_ref(v_body_208_);
lean_dec(v_declName_205_);
lean_dec_ref(v_fvars_140_);
lean_dec_ref(v_localInsts_139_);
lean_dec_ref(v_lctx_138_);
lean_dec(v_i_137_);
lean_dec_ref(v_updateLocalInsts_136_);
lean_dec_ref(v_mkName_135_);
lean_dec_ref(v_finalize_134_);
v_a_244_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_215_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_215_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
lean_dec(v_a_212_);
lean_dec_ref(v_body_208_);
lean_dec(v_declName_205_);
lean_dec_ref(v_fvars_140_);
lean_dec_ref(v_localInsts_139_);
lean_dec_ref(v_lctx_138_);
lean_dec(v_i_137_);
lean_dec_ref(v_updateLocalInsts_136_);
lean_dec_ref(v_mkName_135_);
lean_dec_ref(v_finalize_134_);
v_a_252_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_213_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_213_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_dec_ref(v_body_208_);
lean_dec_ref(v_value_207_);
lean_dec(v_declName_205_);
lean_dec_ref(v_fvars_140_);
lean_dec_ref(v_localInsts_139_);
lean_dec_ref(v_lctx_138_);
lean_dec(v_i_137_);
lean_dec_ref(v_updateLocalInsts_136_);
lean_dec_ref(v_mkName_135_);
lean_dec_ref(v_finalize_134_);
v_a_260_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_211_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_211_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
default: 
{
lean_object* v___x_268_; 
lean_dec(v_i_137_);
lean_dec_ref(v_updateLocalInsts_136_);
lean_dec_ref(v_mkName_135_);
lean_inc(v_a_147_);
lean_inc_ref(v_a_146_);
lean_inc(v_a_145_);
lean_inc_ref(v_a_144_);
lean_inc(v_a_143_);
lean_inc_ref(v_a_142_);
v___x_268_ = lean_apply_11(v_finalize_134_, v_lctx_138_, v_localInsts_139_, v_fvars_140_, v_type_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, lean_box(0));
return v___x_268_;
}
}
}
else
{
lean_object* v___x_269_; 
lean_dec(v_i_137_);
lean_dec_ref(v_updateLocalInsts_136_);
lean_dec_ref(v_mkName_135_);
lean_inc(v_a_147_);
lean_inc_ref(v_a_146_);
lean_inc(v_a_145_);
lean_inc_ref(v_a_144_);
lean_inc(v_a_143_);
lean_inc_ref(v_a_142_);
v___x_269_ = lean_apply_11(v_finalize_134_, v_lctx_138_, v_localInsts_139_, v_fvars_140_, v_type_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, lean_box(0));
return v___x_269_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_max_133_ = stack[0].m_obj;
lean_object* v_finalize_134_ = stack[1].m_obj;
lean_object* v_mkName_135_ = stack[2].m_obj;
lean_object* v_updateLocalInsts_136_ = stack[3].m_obj;
lean_object* v_i_137_ = stack[4].m_obj;
lean_object* v_lctx_138_ = stack[5].m_obj;
lean_object* v_localInsts_139_ = stack[6].m_obj;
lean_object* v_fvars_140_ = stack[7].m_obj;
lean_object* v_type_141_ = stack[8].m_obj;
lean_object* v_a_142_ = stack[9].m_obj;
lean_object* v_a_143_ = stack[10].m_obj;
lean_object* v_a_144_ = stack[11].m_obj;
lean_object* v_a_145_ = stack[12].m_obj;
lean_object* v_a_146_ = stack[13].m_obj;
lean_object* v_a_147_ = stack[14].m_obj;
lean_object* v_res_270_;
v_res_270_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(v_max_133_, v_finalize_134_, v_mkName_135_, v_updateLocalInsts_136_, v_i_137_, v_lctx_138_, v_localInsts_139_, v_fvars_140_, v_type_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
stack->m_obj
 = v_res_270_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit___boxed(lean_object* v_max_271_, lean_object* v_finalize_272_, lean_object* v_mkName_273_, lean_object* v_updateLocalInsts_274_, lean_object* v_i_275_, lean_object* v_lctx_276_, lean_object* v_localInsts_277_, lean_object* v_fvars_278_, lean_object* v_type_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(v_max_271_, v_finalize_272_, v_mkName_273_, v_updateLocalInsts_274_, v_i_275_, v_lctx_276_, v_localInsts_277_, v_fvars_278_, v_type_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_max_271_);
return v_res_287_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0(lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(v___y_293_);
return v___x_295_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_288_ = stack[0].m_obj;
lean_object* v___y_289_ = stack[1].m_obj;
lean_object* v___y_290_ = stack[2].m_obj;
lean_object* v___y_291_ = stack[3].m_obj;
lean_object* v___y_292_ = stack[4].m_obj;
lean_object* v___y_293_ = stack[5].m_obj;
lean_object* v_res_296_;
v_res_296_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0(v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
stack->m_obj
 = v_res_296_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___boxed(lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0(v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
return v_res_304_;
}
}
lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(lean_object* v_names_305_, uint8_t v_hygienic_306_, lean_object* v_lctx_307_, lean_object* v_binderName_308_, lean_object* v_i_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = lean_array_get_size(v_names_305_);
v___x_316_ = lean_nat_dec_lt(v_i_309_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_307_, v_binderName_308_, v_hygienic_306_, v___y_312_, v___y_313_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v_binderName_308_);
v___x_318_ = lean_array_fget_borrowed(v_names_305_, v_i_309_);
lean_inc(v___x_318_);
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_names_305_ = stack[0].m_obj;
uint8_t v_hygienic_306_ = stack[1].m_num;
lean_object* v_lctx_307_ = stack[2].m_obj;
lean_object* v_binderName_308_ = stack[3].m_obj;
lean_object* v_i_309_ = stack[4].m_obj;
lean_object* v___y_310_ = stack[5].m_obj;
lean_object* v___y_311_ = stack[6].m_obj;
lean_object* v___y_312_ = stack[7].m_obj;
lean_object* v___y_313_ = stack[8].m_obj;
lean_object* v_res_320_;
v_res_320_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(v_names_305_, v_hygienic_306_, v_lctx_307_, v_binderName_308_, v_i_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
stack->m_obj
 = v_res_320_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed(lean_object* v_names_321_, lean_object* v_hygienic_322_, lean_object* v_lctx_323_, lean_object* v_binderName_324_, lean_object* v_i_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
uint8_t v_hygienic_boxed_331_; lean_object* v_res_332_; 
v_hygienic_boxed_331_ = lean_unbox(v_hygienic_322_);
v_res_332_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(v_names_321_, v_hygienic_boxed_331_, v_lctx_323_, v_binderName_324_, v_i_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v_i_325_);
lean_dec_ref(v_lctx_323_);
lean_dec_ref(v_names_321_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(lean_object* v_env_333_, lean_object* v_localInsts_334_, lean_object* v_fvar_335_, lean_object* v_type_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Meta_Sym_isClass_x3f(v_env_333_, v_type_336_);
if (lean_obj_tag(v___x_337_) == 1)
{
lean_object* v_val_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_val_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_val_338_);
lean_dec_ref_known(v___x_337_, 1);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v_val_338_);
lean_ctor_set(v___x_339_, 1, v_fvar_335_);
v___x_340_ = lean_array_push(v_localInsts_334_, v___x_339_);
return v___x_340_;
}
else
{
lean_dec(v___x_337_);
lean_dec_ref(v_fvar_335_);
return v_localInsts_334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed(lean_object* v_env_341_, lean_object* v_localInsts_342_, lean_object* v_fvar_343_, lean_object* v_type_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(v_env_341_, v_localInsts_342_, v_fvar_343_, v_type_344_);
lean_dec_ref(v_type_344_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(lean_object* v_x_346_, lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v_ks_350_; lean_object* v_vs_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_375_; 
v_ks_350_ = lean_ctor_get(v_x_346_, 0);
v_vs_351_ = lean_ctor_get(v_x_346_, 1);
v_isSharedCheck_375_ = !lean_is_exclusive(v_x_346_);
if (v_isSharedCheck_375_ == 0)
{
v___x_353_ = v_x_346_;
v_isShared_354_ = v_isSharedCheck_375_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_vs_351_);
lean_inc(v_ks_350_);
lean_dec(v_x_346_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_375_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = lean_array_get_size(v_ks_350_);
v___x_356_ = lean_nat_dec_lt(v_x_347_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
lean_dec(v_x_347_);
v___x_357_ = lean_array_push(v_ks_350_, v_x_348_);
v___x_358_ = lean_array_push(v_vs_351_, v_x_349_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_358_);
lean_ctor_set(v___x_353_, 0, v___x_357_);
v___x_360_ = v___x_353_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_357_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
else
{
lean_object* v_k_x27_362_; uint8_t v___x_363_; 
v_k_x27_362_ = lean_array_fget_borrowed(v_ks_350_, v_x_347_);
v___x_363_ = l_Lean_instBEqMVarId_beq(v_x_348_, v_k_x27_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_365_; 
if (v_isShared_354_ == 0)
{
v___x_365_ = v___x_353_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_ks_350_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_vs_351_);
v___x_365_ = v_reuseFailAlloc_369_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_unsigned_to_nat(1u);
v___x_367_ = lean_nat_add(v_x_347_, v___x_366_);
lean_dec(v_x_347_);
v_x_346_ = v___x_365_;
v_x_347_ = v___x_367_;
goto _start;
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_370_ = lean_array_fset(v_ks_350_, v_x_347_, v_x_348_);
v___x_371_ = lean_array_fset(v_vs_351_, v_x_347_, v_x_349_);
lean_dec(v_x_347_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_371_);
lean_ctor_set(v___x_353_, 0, v___x_370_);
v___x_373_ = v___x_353_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_n_376_, lean_object* v_k_377_, lean_object* v_v_378_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_n_376_, v___x_379_, v_k_377_, v_v_378_);
return v___x_380_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_381_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_382_, size_t v_x_383_, size_t v_x_384_, lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
if (lean_obj_tag(v_x_382_) == 0)
{
lean_object* v_es_387_; size_t v___x_388_; size_t v___x_389_; lean_object* v_j_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v_es_387_ = lean_ctor_get(v_x_382_, 0);
v___x_388_ = ((size_t)31ULL);
v___x_389_ = lean_usize_land(v_x_383_, v___x_388_);
v_j_390_ = lean_usize_to_nat(v___x_389_);
v___x_391_ = lean_array_get_size(v_es_387_);
v___x_392_ = lean_nat_dec_lt(v_j_390_, v___x_391_);
if (v___x_392_ == 0)
{
lean_dec(v_j_390_);
lean_dec(v_x_386_);
lean_dec(v_x_385_);
return v_x_382_;
}
else
{
lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_431_; 
lean_inc_ref(v_es_387_);
v_isSharedCheck_431_ = !lean_is_exclusive(v_x_382_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; 
v_unused_432_ = lean_ctor_get(v_x_382_, 0);
lean_dec(v_unused_432_);
v___x_394_ = v_x_382_;
v_isShared_395_ = v_isSharedCheck_431_;
goto v_resetjp_393_;
}
else
{
lean_dec(v_x_382_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_431_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_v_396_; lean_object* v___x_397_; lean_object* v_xs_x27_398_; lean_object* v___y_400_; 
v_v_396_ = lean_array_fget(v_es_387_, v_j_390_);
v___x_397_ = lean_box(0);
v_xs_x27_398_ = lean_array_fset(v_es_387_, v_j_390_, v___x_397_);
switch(lean_obj_tag(v_v_396_))
{
case 0:
{
lean_object* v_key_405_; lean_object* v_val_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_416_; 
v_key_405_ = lean_ctor_get(v_v_396_, 0);
v_val_406_ = lean_ctor_get(v_v_396_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v_v_396_);
if (v_isSharedCheck_416_ == 0)
{
v___x_408_ = v_v_396_;
v_isShared_409_ = v_isSharedCheck_416_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_val_406_);
lean_inc(v_key_405_);
lean_dec(v_v_396_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_416_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
uint8_t v___x_410_; 
v___x_410_ = l_Lean_instBEqMVarId_beq(v_x_385_, v_key_405_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_del_object(v___x_408_);
v___x_411_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_405_, v_val_406_, v_x_385_, v_x_386_);
v___x_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
v___y_400_ = v___x_412_;
goto v___jp_399_;
}
else
{
lean_object* v___x_414_; 
lean_dec(v_val_406_);
lean_dec(v_key_405_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 1, v_x_386_);
lean_ctor_set(v___x_408_, 0, v_x_385_);
v___x_414_ = v___x_408_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_x_385_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_x_386_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
v___y_400_ = v___x_414_;
goto v___jp_399_;
}
}
}
}
case 1:
{
lean_object* v_node_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_429_; 
v_node_417_ = lean_ctor_get(v_v_396_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v_v_396_);
if (v_isSharedCheck_429_ == 0)
{
v___x_419_ = v_v_396_;
v_isShared_420_ = v_isSharedCheck_429_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_node_417_);
lean_dec(v_v_396_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_429_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
size_t v___x_421_; size_t v___x_422_; size_t v___x_423_; size_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_421_ = ((size_t)5ULL);
v___x_422_ = lean_usize_shift_right(v_x_383_, v___x_421_);
v___x_423_ = ((size_t)1ULL);
v___x_424_ = lean_usize_add(v_x_384_, v___x_423_);
v___x_425_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_node_417_, v___x_422_, v___x_424_, v_x_385_, v_x_386_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_425_);
v___x_427_ = v___x_419_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
v___y_400_ = v___x_427_;
goto v___jp_399_;
}
}
}
default: 
{
lean_object* v___x_430_; 
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v_x_385_);
lean_ctor_set(v___x_430_, 1, v_x_386_);
v___y_400_ = v___x_430_;
goto v___jp_399_;
}
}
v___jp_399_:
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_array_fset(v_xs_x27_398_, v_j_390_, v___y_400_);
lean_dec(v_j_390_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_401_);
v___x_403_ = v___x_394_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
else
{
lean_object* v_ks_433_; lean_object* v_vs_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_452_; 
v_ks_433_ = lean_ctor_get(v_x_382_, 0);
v_vs_434_ = lean_ctor_get(v_x_382_, 1);
v_isSharedCheck_452_ = !lean_is_exclusive(v_x_382_);
if (v_isSharedCheck_452_ == 0)
{
v___x_436_ = v_x_382_;
v_isShared_437_ = v_isSharedCheck_452_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_vs_434_);
lean_inc(v_ks_433_);
lean_dec(v_x_382_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_452_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_ks_433_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_vs_434_);
v___x_439_ = v_reuseFailAlloc_451_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v_newNode_440_; size_t v___x_441_; uint8_t v___x_442_; 
v_newNode_440_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(v___x_439_, v_x_385_, v_x_386_);
v___x_441_ = ((size_t)7ULL);
v___x_442_ = lean_usize_dec_le(v___x_441_, v_x_384_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_443_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_440_);
v___x_444_ = lean_unsigned_to_nat(4u);
v___x_445_ = lean_nat_dec_lt(v___x_443_, v___x_444_);
lean_dec(v___x_443_);
if (v___x_445_ == 0)
{
lean_object* v_ks_446_; lean_object* v_vs_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_ks_446_ = lean_ctor_get(v_newNode_440_, 0);
lean_inc_ref(v_ks_446_);
v_vs_447_ = lean_ctor_get(v_newNode_440_, 1);
lean_inc_ref(v_vs_447_);
lean_dec_ref(v_newNode_440_);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_450_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_384_, v_ks_446_, v_vs_447_, v___x_448_, v___x_449_);
lean_dec_ref(v_vs_447_);
lean_dec_ref(v_ks_446_);
return v___x_450_;
}
else
{
return v_newNode_440_;
}
}
else
{
return v_newNode_440_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_382_ = stack[0].m_obj;
size_t v_x_383_ = stack[1].m_num;
size_t v_x_384_ = stack[2].m_num;
lean_object* v_x_385_ = stack[3].m_obj;
lean_object* v_x_386_ = stack[4].m_obj;
lean_object* v_res_453_;
v_res_453_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_382_, v_x_383_, v_x_384_, v_x_385_, v_x_386_);
stack->m_obj
 = v_res_453_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(size_t v_depth_454_, lean_object* v_keys_455_, lean_object* v_vals_456_, lean_object* v_i_457_, lean_object* v_entries_458_){
_start:
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_array_get_size(v_keys_455_);
v___x_460_ = lean_nat_dec_lt(v_i_457_, v___x_459_);
if (v___x_460_ == 0)
{
lean_dec(v_i_457_);
return v_entries_458_;
}
else
{
lean_object* v_k_461_; lean_object* v_v_462_; uint64_t v___x_463_; size_t v_h_464_; size_t v___x_465_; lean_object* v___x_466_; size_t v___x_467_; size_t v___x_468_; size_t v___x_469_; size_t v_h_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_k_461_ = lean_array_fget_borrowed(v_keys_455_, v_i_457_);
v_v_462_ = lean_array_fget_borrowed(v_vals_456_, v_i_457_);
v___x_463_ = l_Lean_instHashableMVarId_hash(v_k_461_);
v_h_464_ = lean_uint64_to_usize(v___x_463_);
v___x_465_ = ((size_t)5ULL);
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = ((size_t)1ULL);
v___x_468_ = lean_usize_sub(v_depth_454_, v___x_467_);
v___x_469_ = lean_usize_mul(v___x_465_, v___x_468_);
v_h_470_ = lean_usize_shift_right(v_h_464_, v___x_469_);
v___x_471_ = lean_nat_add(v_i_457_, v___x_466_);
lean_dec(v_i_457_);
lean_inc(v_v_462_);
lean_inc(v_k_461_);
v___x_472_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_entries_458_, v_h_470_, v_depth_454_, v_k_461_, v_v_462_);
v_i_457_ = v___x_471_;
v_entries_458_ = v___x_472_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_454_ = stack[0].m_num;
lean_object* v_keys_455_ = stack[1].m_obj;
lean_object* v_vals_456_ = stack[2].m_obj;
lean_object* v_i_457_ = stack[3].m_obj;
lean_object* v_entries_458_ = stack[4].m_obj;
lean_object* v_res_474_;
v_res_474_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_454_, v_keys_455_, v_vals_456_, v_i_457_, v_entries_458_);
stack->m_obj
 = v_res_474_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_depth_475_, lean_object* v_keys_476_, lean_object* v_vals_477_, lean_object* v_i_478_, lean_object* v_entries_479_){
_start:
{
size_t v_depth_boxed_480_; lean_object* v_res_481_; 
v_depth_boxed_480_ = lean_unbox_usize(v_depth_475_);
lean_dec(v_depth_475_);
v_res_481_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_boxed_480_, v_keys_476_, v_vals_477_, v_i_478_, v_entries_479_);
lean_dec_ref(v_vals_477_);
lean_dec_ref(v_keys_476_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
size_t v_x_5225__boxed_487_; size_t v_x_5226__boxed_488_; lean_object* v_res_489_; 
v_x_5225__boxed_487_ = lean_unbox_usize(v_x_483_);
lean_dec(v_x_483_);
v_x_5226__boxed_488_ = lean_unbox_usize(v_x_484_);
lean_dec(v_x_484_);
v_res_489_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_482_, v_x_5225__boxed_487_, v_x_5226__boxed_488_, v_x_485_, v_x_486_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
uint64_t v___x_493_; size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; 
v___x_493_ = l_Lean_instHashableMVarId_hash(v_x_491_);
v___x_494_ = lean_uint64_to_usize(v___x_493_);
v___x_495_ = ((size_t)1ULL);
v___x_496_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_490_, v___x_494_, v___x_495_, v_x_491_, v_x_492_);
return v___x_496_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(lean_object* v_mvarId_497_, lean_object* v_val_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; lean_object* v_mctx_502_; lean_object* v_cache_503_; lean_object* v_zetaDeltaFVarIds_504_; lean_object* v_postponed_505_; lean_object* v_diag_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_536_; 
v___x_501_ = lean_st_ref_take(v___y_499_);
v_mctx_502_ = lean_ctor_get(v___x_501_, 0);
v_cache_503_ = lean_ctor_get(v___x_501_, 1);
v_zetaDeltaFVarIds_504_ = lean_ctor_get(v___x_501_, 2);
v_postponed_505_ = lean_ctor_get(v___x_501_, 3);
v_diag_506_ = lean_ctor_get(v___x_501_, 4);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_536_ == 0)
{
v___x_508_ = v___x_501_;
v_isShared_509_ = v_isSharedCheck_536_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_diag_506_);
lean_inc(v_postponed_505_);
lean_inc(v_zetaDeltaFVarIds_504_);
lean_inc(v_cache_503_);
lean_inc(v_mctx_502_);
lean_dec(v___x_501_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_536_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v_depth_510_; lean_object* v_levelAssignDepth_511_; lean_object* v_lmvarCounter_512_; lean_object* v_mvarCounter_513_; lean_object* v_lDecls_514_; lean_object* v_decls_515_; lean_object* v_userNames_516_; lean_object* v_lAssignment_517_; lean_object* v_eAssignment_518_; lean_object* v_dAssignment_519_; lean_object* v_instanceTypedMVars_520_; lean_object* v_synthNormMemo_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_535_; 
v_depth_510_ = lean_ctor_get(v_mctx_502_, 0);
v_levelAssignDepth_511_ = lean_ctor_get(v_mctx_502_, 1);
v_lmvarCounter_512_ = lean_ctor_get(v_mctx_502_, 2);
v_mvarCounter_513_ = lean_ctor_get(v_mctx_502_, 3);
v_lDecls_514_ = lean_ctor_get(v_mctx_502_, 4);
v_decls_515_ = lean_ctor_get(v_mctx_502_, 5);
v_userNames_516_ = lean_ctor_get(v_mctx_502_, 6);
v_lAssignment_517_ = lean_ctor_get(v_mctx_502_, 7);
v_eAssignment_518_ = lean_ctor_get(v_mctx_502_, 8);
v_dAssignment_519_ = lean_ctor_get(v_mctx_502_, 9);
v_instanceTypedMVars_520_ = lean_ctor_get(v_mctx_502_, 10);
v_synthNormMemo_521_ = lean_ctor_get(v_mctx_502_, 11);
v_isSharedCheck_535_ = !lean_is_exclusive(v_mctx_502_);
if (v_isSharedCheck_535_ == 0)
{
v___x_523_ = v_mctx_502_;
v_isShared_524_ = v_isSharedCheck_535_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_synthNormMemo_521_);
lean_inc(v_instanceTypedMVars_520_);
lean_inc(v_dAssignment_519_);
lean_inc(v_eAssignment_518_);
lean_inc(v_lAssignment_517_);
lean_inc(v_userNames_516_);
lean_inc(v_decls_515_);
lean_inc(v_lDecls_514_);
lean_inc(v_mvarCounter_513_);
lean_inc(v_lmvarCounter_512_);
lean_inc(v_levelAssignDepth_511_);
lean_inc(v_depth_510_);
lean_dec(v_mctx_502_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_535_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_525_ = lean_box(0);
v___x_526_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_eAssignment_518_, v_mvarId_497_, v_val_498_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 8, v___x_526_);
v___x_528_ = v___x_523_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_depth_510_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_levelAssignDepth_511_);
lean_ctor_set(v_reuseFailAlloc_534_, 2, v_lmvarCounter_512_);
lean_ctor_set(v_reuseFailAlloc_534_, 3, v_mvarCounter_513_);
lean_ctor_set(v_reuseFailAlloc_534_, 4, v_lDecls_514_);
lean_ctor_set(v_reuseFailAlloc_534_, 5, v_decls_515_);
lean_ctor_set(v_reuseFailAlloc_534_, 6, v_userNames_516_);
lean_ctor_set(v_reuseFailAlloc_534_, 7, v_lAssignment_517_);
lean_ctor_set(v_reuseFailAlloc_534_, 8, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_534_, 9, v_dAssignment_519_);
lean_ctor_set(v_reuseFailAlloc_534_, 10, v_instanceTypedMVars_520_);
lean_ctor_set(v_reuseFailAlloc_534_, 11, v_synthNormMemo_521_);
v___x_528_ = v_reuseFailAlloc_534_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_528_);
v___x_530_ = v___x_508_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_cache_503_);
lean_ctor_set(v_reuseFailAlloc_533_, 2, v_zetaDeltaFVarIds_504_);
lean_ctor_set(v_reuseFailAlloc_533_, 3, v_postponed_505_);
lean_ctor_set(v_reuseFailAlloc_533_, 4, v_diag_506_);
v___x_530_ = v_reuseFailAlloc_533_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_st_ref_put(v___y_499_, v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_525_);
return v___x_532_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_497_ = stack[0].m_obj;
lean_object* v_val_498_ = stack[1].m_obj;
lean_object* v___y_499_ = stack[2].m_obj;
lean_object* v_res_537_;
v_res_537_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_497_, v_val_498_, v___y_499_);
stack->m_obj
 = v_res_537_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg___boxed(lean_object* v_mvarId_538_, lean_object* v_val_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_538_, v_val_539_, v___y_540_);
lean_dec(v___y_540_);
return v_res_542_;
}
}
lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(lean_object* v_mvarId_543_, lean_object* v_fvars_544_, lean_object* v_mvarIdPending_545_, lean_object* v___y_546_){
_start:
{
lean_object* v___x_548_; lean_object* v_mctx_549_; lean_object* v_cache_550_; lean_object* v_zetaDeltaFVarIds_551_; lean_object* v_postponed_552_; lean_object* v_diag_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_584_; 
v___x_548_ = lean_st_ref_take(v___y_546_);
v_mctx_549_ = lean_ctor_get(v___x_548_, 0);
v_cache_550_ = lean_ctor_get(v___x_548_, 1);
v_zetaDeltaFVarIds_551_ = lean_ctor_get(v___x_548_, 2);
v_postponed_552_ = lean_ctor_get(v___x_548_, 3);
v_diag_553_ = lean_ctor_get(v___x_548_, 4);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_584_ == 0)
{
v___x_555_ = v___x_548_;
v_isShared_556_ = v_isSharedCheck_584_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_diag_553_);
lean_inc(v_postponed_552_);
lean_inc(v_zetaDeltaFVarIds_551_);
lean_inc(v_cache_550_);
lean_inc(v_mctx_549_);
lean_dec(v___x_548_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_584_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v_depth_557_; lean_object* v_levelAssignDepth_558_; lean_object* v_lmvarCounter_559_; lean_object* v_mvarCounter_560_; lean_object* v_lDecls_561_; lean_object* v_decls_562_; lean_object* v_userNames_563_; lean_object* v_lAssignment_564_; lean_object* v_eAssignment_565_; lean_object* v_dAssignment_566_; lean_object* v_instanceTypedMVars_567_; lean_object* v_synthNormMemo_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_583_; 
v_depth_557_ = lean_ctor_get(v_mctx_549_, 0);
v_levelAssignDepth_558_ = lean_ctor_get(v_mctx_549_, 1);
v_lmvarCounter_559_ = lean_ctor_get(v_mctx_549_, 2);
v_mvarCounter_560_ = lean_ctor_get(v_mctx_549_, 3);
v_lDecls_561_ = lean_ctor_get(v_mctx_549_, 4);
v_decls_562_ = lean_ctor_get(v_mctx_549_, 5);
v_userNames_563_ = lean_ctor_get(v_mctx_549_, 6);
v_lAssignment_564_ = lean_ctor_get(v_mctx_549_, 7);
v_eAssignment_565_ = lean_ctor_get(v_mctx_549_, 8);
v_dAssignment_566_ = lean_ctor_get(v_mctx_549_, 9);
v_instanceTypedMVars_567_ = lean_ctor_get(v_mctx_549_, 10);
v_synthNormMemo_568_ = lean_ctor_get(v_mctx_549_, 11);
v_isSharedCheck_583_ = !lean_is_exclusive(v_mctx_549_);
if (v_isSharedCheck_583_ == 0)
{
v___x_570_ = v_mctx_549_;
v_isShared_571_ = v_isSharedCheck_583_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_synthNormMemo_568_);
lean_inc(v_instanceTypedMVars_567_);
lean_inc(v_dAssignment_566_);
lean_inc(v_eAssignment_565_);
lean_inc(v_lAssignment_564_);
lean_inc(v_userNames_563_);
lean_inc(v_decls_562_);
lean_inc(v_lDecls_561_);
lean_inc(v_mvarCounter_560_);
lean_inc(v_lmvarCounter_559_);
lean_inc(v_levelAssignDepth_558_);
lean_inc(v_depth_557_);
lean_dec(v_mctx_549_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_583_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_572_ = lean_box(0);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v_fvars_544_);
lean_ctor_set(v___x_573_, 1, v_mvarIdPending_545_);
v___x_574_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_dAssignment_566_, v_mvarId_543_, v___x_573_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 9, v___x_574_);
v___x_576_ = v___x_570_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_depth_557_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_levelAssignDepth_558_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v_lmvarCounter_559_);
lean_ctor_set(v_reuseFailAlloc_582_, 3, v_mvarCounter_560_);
lean_ctor_set(v_reuseFailAlloc_582_, 4, v_lDecls_561_);
lean_ctor_set(v_reuseFailAlloc_582_, 5, v_decls_562_);
lean_ctor_set(v_reuseFailAlloc_582_, 6, v_userNames_563_);
lean_ctor_set(v_reuseFailAlloc_582_, 7, v_lAssignment_564_);
lean_ctor_set(v_reuseFailAlloc_582_, 8, v_eAssignment_565_);
lean_ctor_set(v_reuseFailAlloc_582_, 9, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_582_, 10, v_instanceTypedMVars_567_);
lean_ctor_set(v_reuseFailAlloc_582_, 11, v_synthNormMemo_568_);
v___x_576_ = v_reuseFailAlloc_582_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_578_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_576_);
v___x_578_ = v___x_555_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_cache_550_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_zetaDeltaFVarIds_551_);
lean_ctor_set(v_reuseFailAlloc_581_, 3, v_postponed_552_);
lean_ctor_set(v_reuseFailAlloc_581_, 4, v_diag_553_);
v___x_578_ = v_reuseFailAlloc_581_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_st_ref_put(v___y_546_, v___x_578_);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_572_);
return v___x_580_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_543_ = stack[0].m_obj;
lean_object* v_fvars_544_ = stack[1].m_obj;
lean_object* v_mvarIdPending_545_ = stack[2].m_obj;
lean_object* v___y_546_ = stack[3].m_obj;
lean_object* v_res_585_;
v_res_585_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_543_, v_fvars_544_, v_mvarIdPending_545_, v___y_546_);
stack->m_obj
 = v_res_585_;
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg___boxed(lean_object* v_mvarId_586_, lean_object* v_fvars_587_, lean_object* v_mvarIdPending_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_586_, v_fvars_587_, v_mvarIdPending_588_, v___y_589_);
lean_dec(v___y_589_);
return v_res_591_;
}
}
lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(lean_object* v___x_592_, lean_object* v_userName_593_, lean_object* v_lctx_594_, lean_object* v_localInstances_595_, lean_object* v_type_596_, lean_object* v_max_597_, lean_object* v_mvarId_598_, lean_object* v_lctx_599_, lean_object* v_localInsts_600_, lean_object* v_fvars_601_, lean_object* v_type_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_array_get_size(v_fvars_601_);
v___x_611_ = lean_nat_dec_eq(v___x_610_, v___x_592_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
lean_inc_ref(v_fvars_601_);
lean_inc(v___x_592_);
v___x_612_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_602_, v___x_592_, v___x_610_, v_fvars_601_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; uint8_t v___x_614_; lean_object* v___x_615_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 1);
v___x_614_ = 2;
lean_inc(v___x_592_);
v___x_615_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_599_, v_localInsts_600_, v_a_613_, v___x_614_, v_userName_593_, v___x_592_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_617_; lean_object* v___y_619_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
v___x_617_ = l_Lean_Expr_mvarId_x21(v_a_616_);
lean_dec(v_a_616_);
v___x_629_ = lean_box(0);
lean_inc(v___x_592_);
lean_inc_ref(v_type_596_);
v___x_630_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_594_, v_localInstances_595_, v_type_596_, v___x_614_, v___x_629_, v___x_592_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc_n(v_a_631_, 2);
lean_dec_ref_known(v___x_630_, 1);
v___x_632_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkAppBVars(v_a_631_, v___x_610_);
v___x_633_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(v_max_597_, v___x_592_, v_type_596_, v___x_632_);
lean_dec_ref(v___x_632_);
lean_dec(v___x_592_);
v___x_634_ = l_Lean_Expr_mvarId_x21(v_a_631_);
lean_dec(v_a_631_);
lean_inc(v___x_617_);
lean_inc_ref(v_fvars_601_);
v___x_635_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v___x_634_, v_fvars_601_, v___x_617_, v___y_606_);
lean_dec_ref(v___x_635_);
v___x_636_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_598_, v___x_633_, v___y_606_);
v___y_619_ = v___x_636_;
goto v___jp_618_;
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec(v___x_617_);
lean_dec_ref(v_fvars_601_);
lean_dec(v_mvarId_598_);
lean_dec_ref(v_type_596_);
lean_dec(v___x_592_);
v_a_637_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_630_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_630_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
v___jp_618_:
{
lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_627_; 
v_isSharedCheck_627_ = !lean_is_exclusive(v___y_619_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v___y_619_, 0);
lean_dec(v_unused_628_);
v___x_621_ = v___y_619_;
v_isShared_622_ = v_isSharedCheck_627_;
goto v_resetjp_620_;
}
else
{
lean_dec(v___y_619_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_627_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v_fvars_601_);
lean_ctor_set(v___x_623_, 1, v___x_617_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_623_);
v___x_625_ = v___x_621_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec_ref(v_fvars_601_);
lean_dec(v_mvarId_598_);
lean_dec_ref(v_type_596_);
lean_dec_ref(v_localInstances_595_);
lean_dec_ref(v_lctx_594_);
lean_dec(v___x_592_);
v_a_645_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_615_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_615_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec_ref(v_fvars_601_);
lean_dec_ref(v_localInsts_600_);
lean_dec_ref(v_lctx_599_);
lean_dec(v_mvarId_598_);
lean_dec_ref(v_type_596_);
lean_dec_ref(v_localInstances_595_);
lean_dec_ref(v_lctx_594_);
lean_dec(v_userName_593_);
lean_dec(v___x_592_);
v_a_653_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_612_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_612_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec_ref(v_type_602_);
lean_dec_ref(v_fvars_601_);
lean_dec_ref(v_localInsts_600_);
lean_dec_ref(v_lctx_599_);
lean_dec_ref(v_type_596_);
lean_dec_ref(v_localInstances_595_);
lean_dec_ref(v_lctx_594_);
lean_dec(v_userName_593_);
v___x_661_ = lean_mk_empty_array_with_capacity(v___x_592_);
lean_dec(v___x_592_);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v_mvarId_598_);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_592_ = stack[0].m_obj;
lean_object* v_userName_593_ = stack[1].m_obj;
lean_object* v_lctx_594_ = stack[2].m_obj;
lean_object* v_localInstances_595_ = stack[3].m_obj;
lean_object* v_type_596_ = stack[4].m_obj;
lean_object* v_max_597_ = stack[5].m_obj;
lean_object* v_mvarId_598_ = stack[6].m_obj;
lean_object* v_lctx_599_ = stack[7].m_obj;
lean_object* v_localInsts_600_ = stack[8].m_obj;
lean_object* v_fvars_601_ = stack[9].m_obj;
lean_object* v_type_602_ = stack[10].m_obj;
lean_object* v___y_603_ = stack[11].m_obj;
lean_object* v___y_604_ = stack[12].m_obj;
lean_object* v___y_605_ = stack[13].m_obj;
lean_object* v___y_606_ = stack[14].m_obj;
lean_object* v___y_607_ = stack[15].m_obj;
lean_object* v___y_608_ = stack[16].m_obj;
lean_object* v_res_664_;
v_res_664_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(v___x_592_, v_userName_593_, v_lctx_594_, v_localInstances_595_, v_type_596_, v_max_597_, v_mvarId_598_, v_lctx_599_, v_localInsts_600_, v_fvars_601_, v_type_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
stack->m_obj
 = v_res_664_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2___boxed(lean_object** _args){
lean_object* v___x_665_ = _args[0];
lean_object* v_userName_666_ = _args[1];
lean_object* v_lctx_667_ = _args[2];
lean_object* v_localInstances_668_ = _args[3];
lean_object* v_type_669_ = _args[4];
lean_object* v_max_670_ = _args[5];
lean_object* v_mvarId_671_ = _args[6];
lean_object* v_lctx_672_ = _args[7];
lean_object* v_localInsts_673_ = _args[8];
lean_object* v_fvars_674_ = _args[9];
lean_object* v_type_675_ = _args[10];
lean_object* v___y_676_ = _args[11];
lean_object* v___y_677_ = _args[12];
lean_object* v___y_678_ = _args[13];
lean_object* v___y_679_ = _args[14];
lean_object* v___y_680_ = _args[15];
lean_object* v___y_681_ = _args[16];
lean_object* v___y_682_ = _args[17];
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(v___x_665_, v_userName_666_, v_lctx_667_, v_localInstances_668_, v_type_669_, v_max_670_, v_mvarId_671_, v_lctx_672_, v_localInsts_673_, v_fvars_674_, v_type_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v_max_670_);
return v_res_683_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(size_t v_sz_684_, size_t v_i_685_, lean_object* v_bs_686_){
_start:
{
uint8_t v___x_687_; 
v___x_687_ = lean_usize_dec_lt(v_i_685_, v_sz_684_);
if (v___x_687_ == 0)
{
return v_bs_686_;
}
else
{
lean_object* v_v_688_; lean_object* v___x_689_; lean_object* v_bs_x27_690_; lean_object* v___x_691_; size_t v___x_692_; size_t v___x_693_; lean_object* v___x_694_; 
v_v_688_ = lean_array_uget(v_bs_686_, v_i_685_);
v___x_689_ = lean_unsigned_to_nat(0u);
v_bs_x27_690_ = lean_array_uset(v_bs_686_, v_i_685_, v___x_689_);
v___x_691_ = l_Lean_Expr_fvarId_x21(v_v_688_);
lean_dec(v_v_688_);
v___x_692_ = ((size_t)1ULL);
v___x_693_ = lean_usize_add(v_i_685_, v___x_692_);
v___x_694_ = lean_array_uset(v_bs_x27_690_, v_i_685_, v___x_691_);
v_i_685_ = v___x_693_;
v_bs_686_ = v___x_694_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_684_ = stack[0].m_num;
size_t v_i_685_ = stack[1].m_num;
lean_object* v_bs_686_ = stack[2].m_obj;
lean_object* v_res_696_;
v_res_696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_684_, v_i_685_, v_bs_686_);
stack->m_obj
 = v_res_696_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2___boxed(lean_object* v_sz_697_, lean_object* v_i_698_, lean_object* v_bs_699_){
_start:
{
size_t v_sz_boxed_700_; size_t v_i_boxed_701_; lean_object* v_res_702_; 
v_sz_boxed_700_ = lean_unbox_usize(v_sz_697_);
lean_dec(v_sz_697_);
v_i_boxed_701_ = lean_unbox_usize(v_i_698_);
lean_dec(v_i_698_);
v_res_702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_boxed_700_, v_i_boxed_701_, v_bs_699_);
return v_res_702_;
}
}
lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(lean_object* v_mvarId_707_, lean_object* v_max_708_, lean_object* v_names_709_, uint8_t v_hygienic_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = lean_nat_dec_eq(v_max_708_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___f_721_; lean_object* v___x_722_; lean_object* v_env_723_; lean_object* v___f_724_; lean_object* v___x_725_; 
v___x_720_ = lean_box(v_hygienic_710_);
v___f_721_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed), 10, 2);
lean_closure_set(v___f_721_, 0, v_names_709_);
lean_closure_set(v___f_721_, 1, v___x_720_);
v___x_722_ = lean_st_ref_get(v_a_716_);
v_env_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc_ref(v_env_723_);
lean_dec(v___x_722_);
v___f_724_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed), 4, 1);
lean_closure_set(v___f_724_, 0, v_env_723_);
lean_inc(v_mvarId_707_);
v___x_725_ = l_Lean_MVarId_getDecl(v_mvarId_707_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v_userName_727_; lean_object* v_lctx_728_; lean_object* v_type_729_; lean_object* v_localInstances_730_; lean_object* v___f_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v_userName_727_ = lean_ctor_get(v_a_726_, 0);
lean_inc(v_userName_727_);
v_lctx_728_ = lean_ctor_get(v_a_726_, 1);
lean_inc_ref_n(v_lctx_728_, 2);
v_type_729_ = lean_ctor_get(v_a_726_, 2);
lean_inc_ref_n(v_type_729_, 2);
v_localInstances_730_ = lean_ctor_get(v_a_726_, 4);
lean_inc_ref_n(v_localInstances_730_, 2);
lean_dec(v_a_726_);
lean_inc(v_max_708_);
v___f_731_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2___boxed), 18, 7);
lean_closure_set(v___f_731_, 0, v___x_718_);
lean_closure_set(v___f_731_, 1, v_userName_727_);
lean_closure_set(v___f_731_, 2, v_lctx_728_);
lean_closure_set(v___f_731_, 3, v_localInstances_730_);
lean_closure_set(v___f_731_, 4, v_type_729_);
lean_closure_set(v___f_731_, 5, v_max_708_);
lean_closure_set(v___f_731_, 6, v_mvarId_707_);
v___x_732_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0));
v___x_733_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(v_max_708_, v___f_731_, v___f_721_, v___f_724_, v___x_718_, v_lctx_728_, v_localInstances_730_, v___x_732_, v_type_729_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
lean_dec(v_max_708_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_753_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_753_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_753_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_753_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v_fst_738_; lean_object* v_snd_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_752_; 
v_fst_738_ = lean_ctor_get(v_a_734_, 0);
v_snd_739_ = lean_ctor_get(v_a_734_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v_a_734_);
if (v_isSharedCheck_752_ == 0)
{
v___x_741_ = v_a_734_;
v_isShared_742_ = v_isSharedCheck_752_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_snd_739_);
lean_inc(v_fst_738_);
lean_dec(v_a_734_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_752_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
size_t v_sz_743_; size_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
v_sz_743_ = lean_array_size(v_fst_738_);
v___x_744_ = ((size_t)0ULL);
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_743_, v___x_744_, v_fst_738_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_745_);
v___x_747_ = v___x_741_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_snd_739_);
v___x_747_ = v_reuseFailAlloc_751_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_749_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_747_);
v___x_749_ = v___x_736_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
v_a_754_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_733_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_733_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec_ref(v___f_724_);
lean_dec_ref(v___f_721_);
lean_dec(v_max_708_);
lean_dec(v_mvarId_707_);
v_a_762_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_725_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_725_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec_ref(v_names_709_);
lean_dec(v_max_708_);
v___x_770_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v_mvarId_707_);
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
return v___x_772_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_707_ = stack[0].m_obj;
lean_object* v_max_708_ = stack[1].m_obj;
lean_object* v_names_709_ = stack[2].m_obj;
uint8_t v_hygienic_710_ = stack[3].m_num;
lean_object* v_a_711_ = stack[4].m_obj;
lean_object* v_a_712_ = stack[5].m_obj;
lean_object* v_a_713_ = stack[6].m_obj;
lean_object* v_a_714_ = stack[7].m_obj;
lean_object* v_a_715_ = stack[8].m_obj;
lean_object* v_a_716_ = stack[9].m_obj;
lean_object* v_res_773_;
v_res_773_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_707_, v_max_708_, v_names_709_, v_hygienic_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
stack->m_obj
 = v_res_773_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___boxed(lean_object* v_mvarId_774_, lean_object* v_max_775_, lean_object* v_names_776_, lean_object* v_hygienic_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
uint8_t v_hygienic_boxed_785_; lean_object* v_res_786_; 
v_hygienic_boxed_785_ = lean_unbox(v_hygienic_777_);
v_res_786_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_774_, v_max_775_, v_names_776_, v_hygienic_boxed_785_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
return v_res_786_;
}
}
lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(lean_object* v_mvarId_787_, lean_object* v_fvars_788_, lean_object* v_mvarIdPending_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_787_, v_fvars_788_, v_mvarIdPending_789_, v___y_791_);
return v___x_795_;
}
}
LEAN_EXPORT void l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_787_ = stack[0].m_obj;
lean_object* v_fvars_788_ = stack[1].m_obj;
lean_object* v_mvarIdPending_789_ = stack[2].m_obj;
lean_object* v___y_790_ = stack[3].m_obj;
lean_object* v___y_791_ = stack[4].m_obj;
lean_object* v___y_792_ = stack[5].m_obj;
lean_object* v___y_793_ = stack[6].m_obj;
lean_object* v_res_796_;
v_res_796_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(v_mvarId_787_, v_fvars_788_, v_mvarIdPending_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
stack->m_obj
 = v_res_796_;
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___boxed(lean_object* v_mvarId_797_, lean_object* v_fvars_798_, lean_object* v_mvarIdPending_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(v_mvarId_797_, v_fvars_798_, v_mvarIdPending_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
return v_res_805_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(lean_object* v_mvarId_806_, lean_object* v_val_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_806_, v_val_807_, v___y_809_);
return v___x_813_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_806_ = stack[0].m_obj;
lean_object* v_val_807_ = stack[1].m_obj;
lean_object* v___y_808_ = stack[2].m_obj;
lean_object* v___y_809_ = stack[3].m_obj;
lean_object* v___y_810_ = stack[4].m_obj;
lean_object* v___y_811_ = stack[5].m_obj;
lean_object* v_res_814_;
v_res_814_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(v_mvarId_806_, v_val_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
stack->m_obj
 = v_res_814_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___boxed(lean_object* v_mvarId_815_, lean_object* v_val_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(v_mvarId_815_, v_val_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0(lean_object* v_00_u03b2_823_, lean_object* v_x_824_, lean_object* v_x_825_, lean_object* v_x_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_x_824_, v_x_825_, v_x_826_);
return v___x_827_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_828_, lean_object* v_x_829_, size_t v_x_830_, size_t v_x_831_, lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_829_, v_x_830_, v_x_831_, v_x_832_, v_x_833_);
return v___x_834_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_829_ = stack[1].m_obj;
size_t v_x_830_ = stack[2].m_num;
size_t v_x_831_ = stack[3].m_num;
lean_object* v_x_832_ = stack[4].m_obj;
lean_object* v_x_833_ = stack[5].m_obj;
lean_object* v_res_835_;
v_res_835_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(lean_box(0), v_x_829_, v_x_830_, v_x_831_, v_x_832_, v_x_833_);
stack->m_obj
 = v_res_835_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
size_t v_x_6082__boxed_842_; size_t v_x_6083__boxed_843_; lean_object* v_res_844_; 
v_x_6082__boxed_842_ = lean_unbox_usize(v_x_838_);
lean_dec(v_x_838_);
v_x_6083__boxed_843_ = lean_unbox_usize(v_x_839_);
lean_dec(v_x_839_);
v_res_844_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(v_00_u03b2_836_, v_x_837_, v_x_6082__boxed_842_, v_x_6083__boxed_843_, v_x_840_, v_x_841_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_845_, lean_object* v_n_846_, lean_object* v_k_847_, lean_object* v_v_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(v_n_846_, v_k_847_, v_v_848_);
return v___x_849_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_850_, size_t v_depth_851_, lean_object* v_keys_852_, lean_object* v_vals_853_, lean_object* v_heq_854_, lean_object* v_i_855_, lean_object* v_entries_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_851_, v_keys_852_, v_vals_853_, v_i_855_, v_entries_856_);
return v___x_857_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_851_ = stack[1].m_num;
lean_object* v_keys_852_ = stack[2].m_obj;
lean_object* v_vals_853_ = stack[3].m_obj;
lean_object* v_i_855_ = stack[5].m_obj;
lean_object* v_entries_856_ = stack[6].m_obj;
lean_object* v_res_858_;
v_res_858_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(lean_box(0), v_depth_851_, v_keys_852_, v_vals_853_, lean_box(0), v_i_855_, v_entries_856_);
stack->m_obj
 = v_res_858_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_859_, lean_object* v_depth_860_, lean_object* v_keys_861_, lean_object* v_vals_862_, lean_object* v_heq_863_, lean_object* v_i_864_, lean_object* v_entries_865_){
_start:
{
size_t v_depth_boxed_866_; lean_object* v_res_867_; 
v_depth_boxed_866_ = lean_unbox_usize(v_depth_860_);
lean_dec(v_depth_860_);
v_res_867_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_859_, v_depth_boxed_866_, v_keys_861_, v_vals_862_, v_heq_863_, v_i_864_, v_entries_865_);
lean_dec_ref(v_vals_862_);
lean_dec_ref(v_keys_861_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_868_, lean_object* v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_x_869_, v_x_870_, v_x_871_, v_x_872_);
return v___x_873_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat(void){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = lean_unsigned_to_nat(1000000u);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx___impl(lean_object* v_x_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = lean_obj_tag_nat(v_x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx___impl___boxed(lean_object* v_x_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_Meta_Sym_IntrosResult_ctorIdx___impl(v_x_877_);
lean_dec(v_x_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(lean_object* v_t_879_, lean_object* v_k_880_){
_start:
{
if (lean_obj_tag(v_t_879_) == 0)
{
return v_k_880_;
}
else
{
lean_object* v_newDecls_881_; lean_object* v_mvarId_882_; lean_object* v___x_883_; 
v_newDecls_881_ = lean_ctor_get(v_t_879_, 0);
lean_inc_ref(v_newDecls_881_);
v_mvarId_882_ = lean_ctor_get(v_t_879_, 1);
lean_inc(v_mvarId_882_);
lean_dec_ref_known(v_t_879_, 2);
v___x_883_ = lean_apply_2(v_k_880_, v_newDecls_881_, v_mvarId_882_);
return v___x_883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim(lean_object* v_motive_884_, lean_object* v_ctorIdx_885_, lean_object* v_t_886_, lean_object* v_h_887_, lean_object* v_k_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_886_, v_k_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___boxed(lean_object* v_motive_890_, lean_object* v_ctorIdx_891_, lean_object* v_t_892_, lean_object* v_h_893_, lean_object* v_k_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Meta_Sym_IntrosResult_ctorElim(v_motive_890_, v_ctorIdx_891_, v_t_892_, v_h_893_, v_k_894_);
lean_dec(v_ctorIdx_891_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim___redArg(lean_object* v_t_896_, lean_object* v_failed_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_896_, v_failed_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim(lean_object* v_motive_899_, lean_object* v_t_900_, lean_object* v_h_901_, lean_object* v_failed_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_900_, v_failed_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim___redArg(lean_object* v_t_904_, lean_object* v_goal_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_904_, v_goal_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim(lean_object* v_motive_907_, lean_object* v_t_908_, lean_object* v_h_909_, lean_object* v_goal_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_908_, v_goal_910_);
return v___x_911_;
}
}
lean_object* l_Lean_Meta_Sym_intros(lean_object* v_mvarId_912_, lean_object* v_names_913_, uint8_t v_hygienic_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_result_923_; lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_939_ = lean_array_get_size(v_names_913_);
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = lean_nat_dec_eq(v___x_939_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
v___x_942_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_912_, v___x_939_, v_names_913_, v_hygienic_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_942_, 1);
v_result_923_ = v_a_943_;
goto v___jp_922_;
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v_a_944_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_942_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_942_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
lean_dec_ref(v_names_913_);
v___x_952_ = lean_unsigned_to_nat(1000000u);
v___x_953_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
v___x_954_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_912_, v___x_952_, v___x_953_, v_hygienic_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_954_, 1);
v_result_923_ = v_a_955_;
goto v___jp_922_;
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
v_a_956_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_954_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_954_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
v___jp_922_:
{
lean_object* v_fst_924_; lean_object* v_snd_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_938_; 
v_fst_924_ = lean_ctor_get(v_result_923_, 0);
v_snd_925_ = lean_ctor_get(v_result_923_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v_result_923_);
if (v_isSharedCheck_938_ == 0)
{
v___x_927_ = v_result_923_;
v_isShared_928_ = v_isSharedCheck_938_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_snd_925_);
lean_inc(v_fst_924_);
lean_dec(v_result_923_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_938_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_929_ = lean_array_get_size(v_fst_924_);
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = lean_nat_dec_eq(v___x_929_, v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_933_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set_tag(v___x_927_, 1);
v___x_933_ = v___x_927_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_fst_924_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_snd_925_);
v___x_933_ = v_reuseFailAlloc_935_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; 
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_del_object(v___x_927_);
lean_dec(v_snd_925_);
lean_dec(v_fst_924_);
v___x_936_ = lean_box(0);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_intros_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_912_ = stack[0].m_obj;
lean_object* v_names_913_ = stack[1].m_obj;
uint8_t v_hygienic_914_ = stack[2].m_num;
lean_object* v_a_915_ = stack[3].m_obj;
lean_object* v_a_916_ = stack[4].m_obj;
lean_object* v_a_917_ = stack[5].m_obj;
lean_object* v_a_918_ = stack[6].m_obj;
lean_object* v_a_919_ = stack[7].m_obj;
lean_object* v_a_920_ = stack[8].m_obj;
lean_object* v_res_964_;
v_res_964_ = l_Lean_Meta_Sym_intros(v_mvarId_912_, v_names_913_, v_hygienic_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
stack->m_obj
 = v_res_964_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros___boxed(lean_object* v_mvarId_965_, lean_object* v_names_966_, lean_object* v_hygienic_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
uint8_t v_hygienic_boxed_975_; lean_object* v_res_976_; 
v_hygienic_boxed_975_ = lean_unbox(v_hygienic_967_);
v_res_976_ = l_Lean_Meta_Sym_intros(v_mvarId_965_, v_names_966_, v_hygienic_boxed_975_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
return v_res_976_;
}
}
lean_object* l_Lean_Meta_Sym_introN(lean_object* v_mvarId_977_, lean_object* v_num_978_, uint8_t v_hygienic_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
lean_inc(v_num_978_);
v___x_988_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_977_, v_num_978_, v___x_987_, v_hygienic_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1011_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_1011_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1011_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v_fst_993_; lean_object* v_snd_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1010_; 
v_fst_993_ = lean_ctor_get(v_a_989_, 0);
v_snd_994_ = lean_ctor_get(v_a_989_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_a_989_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_996_ = v_a_989_;
v_isShared_997_ = v_isSharedCheck_1010_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_snd_994_);
lean_inc(v_fst_993_);
lean_dec(v_a_989_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1010_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_998_ = lean_array_get_size(v_fst_993_);
v___x_999_ = lean_nat_dec_eq(v___x_998_, v_num_978_);
lean_dec(v_num_978_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
lean_del_object(v___x_996_);
lean_dec(v_snd_994_);
lean_dec(v_fst_993_);
v___x_1000_ = lean_box(0);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_1000_);
v___x_1002_ = v___x_991_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
else
{
lean_object* v___x_1005_; 
if (v_isShared_997_ == 0)
{
lean_ctor_set_tag(v___x_996_, 1);
v___x_1005_ = v___x_996_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_fst_993_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_snd_994_);
v___x_1005_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_1005_);
v___x_1007_ = v___x_991_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec(v_num_978_);
v_a_1012_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_988_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_988_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_introN_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_977_ = stack[0].m_obj;
lean_object* v_num_978_ = stack[1].m_obj;
uint8_t v_hygienic_979_ = stack[2].m_num;
lean_object* v_a_980_ = stack[3].m_obj;
lean_object* v_a_981_ = stack[4].m_obj;
lean_object* v_a_982_ = stack[5].m_obj;
lean_object* v_a_983_ = stack[6].m_obj;
lean_object* v_a_984_ = stack[7].m_obj;
lean_object* v_a_985_ = stack[8].m_obj;
lean_object* v_res_1020_;
v_res_1020_ = l_Lean_Meta_Sym_introN(v_mvarId_977_, v_num_978_, v_hygienic_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
stack->m_obj
 = v_res_1020_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN___boxed(lean_object* v_mvarId_1021_, lean_object* v_num_1022_, lean_object* v_hygienic_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
uint8_t v_hygienic_boxed_1031_; lean_object* v_res_1032_; 
v_hygienic_boxed_1031_ = lean_unbox(v_hygienic_1023_);
v_res_1032_ = l_Lean_Meta_Sym_introN(v_mvarId_1021_, v_num_1022_, v_hygienic_boxed_1031_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
return v_res_1032_;
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
