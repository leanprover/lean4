// Lean compiler output
// Module: Lean.Meta.Sym.Intro
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.IsClass import Lean.Meta.Sym.AlphaShareBuilder
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
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isClass_x3f(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__2;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_type_3_);
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
lean_dec_ref(v_type_3_);
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
lean_dec_ref(v_type_3_);
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
lean_dec_ref(v_type_136_);
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
lean_dec_ref(v_type_136_);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_array_get_size(v_fvars_135_);
v___x_153_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_binderType_148_, v___x_151_, v___x_152_, v_fvars_135_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_155_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_a_154_);
lean_dec_ref(v___x_153_);
v___x_155_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_157_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref(v___x_155_);
lean_inc_ref(v_mkName_130_);
lean_inc(v_a_142_);
lean_inc_ref(v_a_141_);
lean_inc(v_a_140_);
lean_inc_ref(v_a_139_);
lean_inc(v_i_132_);
v___x_157_ = lean_apply_7(v_mkName_130_, v_binderName_147_, v_i_132_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, lean_box(0));
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref(v___x_157_);
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
lean_dec_ref(v___x_161_);
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
lean_dec_ref(v_type_136_);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_array_get_size(v_fvars_135_);
v___x_206_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_201_, v___x_204_, v___x_205_, v_fvars_135_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_208_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref(v___x_206_);
v___x_208_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_value_202_, v___x_204_, v___x_205_, v_fvars_135_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_210_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref(v___x_208_);
v___x_210_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_212_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
lean_dec_ref(v___x_210_);
lean_inc_ref(v_mkName_130_);
lean_inc(v_a_142_);
lean_inc_ref(v_a_141_);
lean_inc(v_a_140_);
lean_inc_ref(v_a_139_);
lean_inc(v_i_132_);
v___x_212_ = lean_apply_7(v_mkName_130_, v_declName_200_, v_i_132_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, lean_box(0));
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; uint8_t v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref(v___x_212_);
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
lean_dec_ref(v___x_216_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(lean_object* v_names_298_, lean_object* v_binderName_299_, lean_object* v_i_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = lean_array_get_size(v_names_298_);
v___x_307_ = lean_nat_dec_lt(v_i_300_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Core_mkFreshUserName(v_binderName_299_, v___y_303_, v___y_304_);
return v___x_308_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec(v_binderName_299_);
v___x_309_ = lean_array_fget_borrowed(v_names_298_, v_i_300_);
lean_inc(v___x_309_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed(lean_object* v_names_311_, lean_object* v_binderName_312_, lean_object* v_i_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(v_names_311_, v_binderName_312_, v_i_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v_i_313_);
lean_dec_ref(v_names_311_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_){
_start:
{
lean_object* v_ks_324_; lean_object* v_vs_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_349_; 
v_ks_324_ = lean_ctor_get(v_x_320_, 0);
v_vs_325_ = lean_ctor_get(v_x_320_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v_x_320_);
if (v_isSharedCheck_349_ == 0)
{
v___x_327_ = v_x_320_;
v_isShared_328_ = v_isSharedCheck_349_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_vs_325_);
lean_inc(v_ks_324_);
lean_dec(v_x_320_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_349_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_array_get_size(v_ks_324_);
v___x_330_ = lean_nat_dec_lt(v_x_321_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
lean_dec(v_x_321_);
v___x_331_ = lean_array_push(v_ks_324_, v_x_322_);
v___x_332_ = lean_array_push(v_vs_325_, v_x_323_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v___x_332_);
lean_ctor_set(v___x_327_, 0, v___x_331_);
v___x_334_ = v___x_327_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
else
{
lean_object* v_k_x27_336_; uint8_t v___x_337_; 
v_k_x27_336_ = lean_array_fget_borrowed(v_ks_324_, v_x_321_);
v___x_337_ = l_Lean_instBEqMVarId_beq(v_x_322_, v_k_x27_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_339_; 
if (v_isShared_328_ == 0)
{
v___x_339_ = v___x_327_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_ks_324_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_vs_325_);
v___x_339_ = v_reuseFailAlloc_343_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_unsigned_to_nat(1u);
v___x_341_ = lean_nat_add(v_x_321_, v___x_340_);
lean_dec(v_x_321_);
v_x_320_ = v___x_339_;
v_x_321_ = v___x_341_;
goto _start;
}
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_344_ = lean_array_fset(v_ks_324_, v_x_321_, v_x_322_);
v___x_345_ = lean_array_fset(v_vs_325_, v_x_321_, v_x_323_);
lean_dec(v_x_321_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v___x_345_);
lean_ctor_set(v___x_327_, 0, v___x_344_);
v___x_347_ = v___x_327_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_n_350_, lean_object* v_k_351_, lean_object* v_v_352_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_n_350_, v___x_353_, v_k_351_, v_v_352_);
return v___x_354_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_355_; size_t v___x_356_; size_t v___x_357_; 
v___x_355_ = ((size_t)5ULL);
v___x_356_ = ((size_t)1ULL);
v___x_357_ = lean_usize_shift_left(v___x_356_, v___x_355_);
return v___x_357_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_358_; size_t v___x_359_; size_t v___x_360_; 
v___x_358_ = ((size_t)1ULL);
v___x_359_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_360_ = lean_usize_sub(v___x_359_, v___x_358_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_362_, size_t v_x_363_, size_t v_x_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
if (lean_obj_tag(v_x_362_) == 0)
{
lean_object* v_es_367_; size_t v___x_368_; size_t v___x_369_; size_t v___x_370_; size_t v___x_371_; lean_object* v_j_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v_es_367_ = lean_ctor_get(v_x_362_, 0);
v___x_368_ = ((size_t)5ULL);
v___x_369_ = ((size_t)1ULL);
v___x_370_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_371_ = lean_usize_land(v_x_363_, v___x_370_);
v_j_372_ = lean_usize_to_nat(v___x_371_);
v___x_373_ = lean_array_get_size(v_es_367_);
v___x_374_ = lean_nat_dec_lt(v_j_372_, v___x_373_);
if (v___x_374_ == 0)
{
lean_dec(v_j_372_);
lean_dec(v_x_366_);
lean_dec(v_x_365_);
return v_x_362_;
}
else
{
lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_411_; 
lean_inc_ref(v_es_367_);
v_isSharedCheck_411_ = !lean_is_exclusive(v_x_362_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v_x_362_, 0);
lean_dec(v_unused_412_);
v___x_376_ = v_x_362_;
v_isShared_377_ = v_isSharedCheck_411_;
goto v_resetjp_375_;
}
else
{
lean_dec(v_x_362_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_411_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v_v_378_; lean_object* v___x_379_; lean_object* v_xs_x27_380_; lean_object* v___y_382_; 
v_v_378_ = lean_array_fget(v_es_367_, v_j_372_);
v___x_379_ = lean_box(0);
v_xs_x27_380_ = lean_array_fset(v_es_367_, v_j_372_, v___x_379_);
switch(lean_obj_tag(v_v_378_))
{
case 0:
{
lean_object* v_key_387_; lean_object* v_val_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_398_; 
v_key_387_ = lean_ctor_get(v_v_378_, 0);
v_val_388_ = lean_ctor_get(v_v_378_, 1);
v_isSharedCheck_398_ = !lean_is_exclusive(v_v_378_);
if (v_isSharedCheck_398_ == 0)
{
v___x_390_ = v_v_378_;
v_isShared_391_ = v_isSharedCheck_398_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_val_388_);
lean_inc(v_key_387_);
lean_dec(v_v_378_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_398_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
uint8_t v___x_392_; 
v___x_392_ = l_Lean_instBEqMVarId_beq(v_x_365_, v_key_387_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_del_object(v___x_390_);
v___x_393_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_387_, v_val_388_, v_x_365_, v_x_366_);
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
v___y_382_ = v___x_394_;
goto v___jp_381_;
}
else
{
lean_object* v___x_396_; 
lean_dec(v_val_388_);
lean_dec(v_key_387_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 1, v_x_366_);
lean_ctor_set(v___x_390_, 0, v_x_365_);
v___x_396_ = v___x_390_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_x_365_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_x_366_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
v___y_382_ = v___x_396_;
goto v___jp_381_;
}
}
}
}
case 1:
{
lean_object* v_node_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_409_; 
v_node_399_ = lean_ctor_get(v_v_378_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v_v_378_);
if (v_isSharedCheck_409_ == 0)
{
v___x_401_ = v_v_378_;
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_node_399_);
lean_dec(v_v_378_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
size_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_403_ = lean_usize_shift_right(v_x_363_, v___x_368_);
v___x_404_ = lean_usize_add(v_x_364_, v___x_369_);
v___x_405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_node_399_, v___x_403_, v___x_404_, v_x_365_, v_x_366_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_405_);
v___x_407_ = v___x_401_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
v___y_382_ = v___x_407_;
goto v___jp_381_;
}
}
}
default: 
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v_x_365_);
lean_ctor_set(v___x_410_, 1, v_x_366_);
v___y_382_ = v___x_410_;
goto v___jp_381_;
}
}
v___jp_381_:
{
lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_383_ = lean_array_fset(v_xs_x27_380_, v_j_372_, v___y_382_);
lean_dec(v_j_372_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_383_);
v___x_385_ = v___x_376_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
else
{
lean_object* v_ks_413_; lean_object* v_vs_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_434_; 
v_ks_413_ = lean_ctor_get(v_x_362_, 0);
v_vs_414_ = lean_ctor_get(v_x_362_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_x_362_);
if (v_isSharedCheck_434_ == 0)
{
v___x_416_ = v_x_362_;
v_isShared_417_ = v_isSharedCheck_434_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_vs_414_);
lean_inc(v_ks_413_);
lean_dec(v_x_362_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_434_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_ks_413_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_vs_414_);
v___x_419_ = v_reuseFailAlloc_433_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v_newNode_420_; uint8_t v___y_422_; size_t v___x_428_; uint8_t v___x_429_; 
v_newNode_420_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(v___x_419_, v_x_365_, v_x_366_);
v___x_428_ = ((size_t)7ULL);
v___x_429_ = lean_usize_dec_le(v___x_428_, v_x_364_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_430_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_420_);
v___x_431_ = lean_unsigned_to_nat(4u);
v___x_432_ = lean_nat_dec_lt(v___x_430_, v___x_431_);
lean_dec(v___x_430_);
v___y_422_ = v___x_432_;
goto v___jp_421_;
}
else
{
v___y_422_ = v___x_429_;
goto v___jp_421_;
}
v___jp_421_:
{
if (v___y_422_ == 0)
{
lean_object* v_ks_423_; lean_object* v_vs_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_ks_423_ = lean_ctor_get(v_newNode_420_, 0);
lean_inc_ref(v_ks_423_);
v_vs_424_ = lean_ctor_get(v_newNode_420_, 1);
lean_inc_ref(v_vs_424_);
lean_dec_ref(v_newNode_420_);
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_427_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_364_, v_ks_423_, v_vs_424_, v___x_425_, v___x_426_);
lean_dec_ref(v_vs_424_);
lean_dec_ref(v_ks_423_);
return v___x_427_;
}
else
{
return v_newNode_420_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(size_t v_depth_435_, lean_object* v_keys_436_, lean_object* v_vals_437_, lean_object* v_i_438_, lean_object* v_entries_439_){
_start:
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_array_get_size(v_keys_436_);
v___x_441_ = lean_nat_dec_lt(v_i_438_, v___x_440_);
if (v___x_441_ == 0)
{
lean_dec(v_i_438_);
return v_entries_439_;
}
else
{
lean_object* v_k_442_; lean_object* v_v_443_; uint64_t v___x_444_; size_t v_h_445_; size_t v___x_446_; lean_object* v___x_447_; size_t v___x_448_; size_t v___x_449_; size_t v___x_450_; size_t v_h_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_k_442_ = lean_array_fget_borrowed(v_keys_436_, v_i_438_);
v_v_443_ = lean_array_fget_borrowed(v_vals_437_, v_i_438_);
v___x_444_ = l_Lean_instHashableMVarId_hash(v_k_442_);
v_h_445_ = lean_uint64_to_usize(v___x_444_);
v___x_446_ = ((size_t)5ULL);
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_sub(v_depth_435_, v___x_448_);
v___x_450_ = lean_usize_mul(v___x_446_, v___x_449_);
v_h_451_ = lean_usize_shift_right(v_h_445_, v___x_450_);
v___x_452_ = lean_nat_add(v_i_438_, v___x_447_);
lean_dec(v_i_438_);
lean_inc(v_v_443_);
lean_inc(v_k_442_);
v___x_453_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_entries_439_, v_h_451_, v_depth_435_, v_k_442_, v_v_443_);
v_i_438_ = v___x_452_;
v_entries_439_ = v___x_453_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_depth_455_, lean_object* v_keys_456_, lean_object* v_vals_457_, lean_object* v_i_458_, lean_object* v_entries_459_){
_start:
{
size_t v_depth_boxed_460_; lean_object* v_res_461_; 
v_depth_boxed_460_ = lean_unbox_usize(v_depth_455_);
lean_dec(v_depth_455_);
v_res_461_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_boxed_460_, v_keys_456_, v_vals_457_, v_i_458_, v_entries_459_);
lean_dec_ref(v_vals_457_);
lean_dec_ref(v_keys_456_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_, lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
size_t v_x_5324__boxed_467_; size_t v_x_5325__boxed_468_; lean_object* v_res_469_; 
v_x_5324__boxed_467_ = lean_unbox_usize(v_x_463_);
lean_dec(v_x_463_);
v_x_5325__boxed_468_ = lean_unbox_usize(v_x_464_);
lean_dec(v_x_464_);
v_res_469_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_462_, v_x_5324__boxed_467_, v_x_5325__boxed_468_, v_x_465_, v_x_466_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(lean_object* v_x_470_, lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
uint64_t v___x_473_; size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
v___x_473_ = l_Lean_instHashableMVarId_hash(v_x_471_);
v___x_474_ = lean_uint64_to_usize(v___x_473_);
v___x_475_ = ((size_t)1ULL);
v___x_476_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_470_, v___x_474_, v___x_475_, v_x_471_, v_x_472_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(lean_object* v_mvarId_477_, lean_object* v_val_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; lean_object* v_mctx_482_; lean_object* v_cache_483_; lean_object* v_zetaDeltaFVarIds_484_; lean_object* v_postponed_485_; lean_object* v_diag_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_513_; 
v___x_481_ = lean_st_ref_take(v___y_479_);
v_mctx_482_ = lean_ctor_get(v___x_481_, 0);
v_cache_483_ = lean_ctor_get(v___x_481_, 1);
v_zetaDeltaFVarIds_484_ = lean_ctor_get(v___x_481_, 2);
v_postponed_485_ = lean_ctor_get(v___x_481_, 3);
v_diag_486_ = lean_ctor_get(v___x_481_, 4);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_513_ == 0)
{
v___x_488_ = v___x_481_;
v_isShared_489_ = v_isSharedCheck_513_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_diag_486_);
lean_inc(v_postponed_485_);
lean_inc(v_zetaDeltaFVarIds_484_);
lean_inc(v_cache_483_);
lean_inc(v_mctx_482_);
lean_dec(v___x_481_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_513_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v_depth_490_; lean_object* v_levelAssignDepth_491_; lean_object* v_mvarCounter_492_; lean_object* v_lDepth_493_; lean_object* v_decls_494_; lean_object* v_userNames_495_; lean_object* v_lAssignment_496_; lean_object* v_eAssignment_497_; lean_object* v_dAssignment_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_512_; 
v_depth_490_ = lean_ctor_get(v_mctx_482_, 0);
v_levelAssignDepth_491_ = lean_ctor_get(v_mctx_482_, 1);
v_mvarCounter_492_ = lean_ctor_get(v_mctx_482_, 2);
v_lDepth_493_ = lean_ctor_get(v_mctx_482_, 3);
v_decls_494_ = lean_ctor_get(v_mctx_482_, 4);
v_userNames_495_ = lean_ctor_get(v_mctx_482_, 5);
v_lAssignment_496_ = lean_ctor_get(v_mctx_482_, 6);
v_eAssignment_497_ = lean_ctor_get(v_mctx_482_, 7);
v_dAssignment_498_ = lean_ctor_get(v_mctx_482_, 8);
v_isSharedCheck_512_ = !lean_is_exclusive(v_mctx_482_);
if (v_isSharedCheck_512_ == 0)
{
v___x_500_ = v_mctx_482_;
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
lean_inc(v_lDepth_493_);
lean_inc(v_mvarCounter_492_);
lean_inc(v_levelAssignDepth_491_);
lean_inc(v_depth_490_);
lean_dec(v_mctx_482_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_512_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_eAssignment_497_, v_mvarId_477_, v_val_478_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 7, v___x_502_);
v___x_504_ = v___x_500_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_depth_490_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_levelAssignDepth_491_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_mvarCounter_492_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_lDepth_493_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v_decls_494_);
lean_ctor_set(v_reuseFailAlloc_511_, 5, v_userNames_495_);
lean_ctor_set(v_reuseFailAlloc_511_, 6, v_lAssignment_496_);
lean_ctor_set(v_reuseFailAlloc_511_, 7, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_511_, 8, v_dAssignment_498_);
v___x_504_ = v_reuseFailAlloc_511_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_506_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_504_);
v___x_506_ = v___x_488_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_cache_483_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_zetaDeltaFVarIds_484_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v_postponed_485_);
lean_ctor_set(v_reuseFailAlloc_510_, 4, v_diag_486_);
v___x_506_ = v_reuseFailAlloc_510_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_st_ref_set(v___y_479_, v___x_506_);
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
lean_object* v___x_524_; lean_object* v_mctx_525_; lean_object* v_cache_526_; lean_object* v_zetaDeltaFVarIds_527_; lean_object* v_postponed_528_; lean_object* v_diag_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_557_; 
v___x_524_ = lean_st_ref_take(v___y_522_);
v_mctx_525_ = lean_ctor_get(v___x_524_, 0);
v_cache_526_ = lean_ctor_get(v___x_524_, 1);
v_zetaDeltaFVarIds_527_ = lean_ctor_get(v___x_524_, 2);
v_postponed_528_ = lean_ctor_get(v___x_524_, 3);
v_diag_529_ = lean_ctor_get(v___x_524_, 4);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_557_ == 0)
{
v___x_531_ = v___x_524_;
v_isShared_532_ = v_isSharedCheck_557_;
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
v_isShared_532_ = v_isSharedCheck_557_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v_depth_533_; lean_object* v_levelAssignDepth_534_; lean_object* v_mvarCounter_535_; lean_object* v_lDepth_536_; lean_object* v_decls_537_; lean_object* v_userNames_538_; lean_object* v_lAssignment_539_; lean_object* v_eAssignment_540_; lean_object* v_dAssignment_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_556_; 
v_depth_533_ = lean_ctor_get(v_mctx_525_, 0);
v_levelAssignDepth_534_ = lean_ctor_get(v_mctx_525_, 1);
v_mvarCounter_535_ = lean_ctor_get(v_mctx_525_, 2);
v_lDepth_536_ = lean_ctor_get(v_mctx_525_, 3);
v_decls_537_ = lean_ctor_get(v_mctx_525_, 4);
v_userNames_538_ = lean_ctor_get(v_mctx_525_, 5);
v_lAssignment_539_ = lean_ctor_get(v_mctx_525_, 6);
v_eAssignment_540_ = lean_ctor_get(v_mctx_525_, 7);
v_dAssignment_541_ = lean_ctor_get(v_mctx_525_, 8);
v_isSharedCheck_556_ = !lean_is_exclusive(v_mctx_525_);
if (v_isSharedCheck_556_ == 0)
{
v___x_543_ = v_mctx_525_;
v_isShared_544_ = v_isSharedCheck_556_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_dAssignment_541_);
lean_inc(v_eAssignment_540_);
lean_inc(v_lAssignment_539_);
lean_inc(v_userNames_538_);
lean_inc(v_decls_537_);
lean_inc(v_lDepth_536_);
lean_inc(v_mvarCounter_535_);
lean_inc(v_levelAssignDepth_534_);
lean_inc(v_depth_533_);
lean_dec(v_mctx_525_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_556_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v_fvars_520_);
lean_ctor_set(v___x_545_, 1, v_mvarIdPending_521_);
v___x_546_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_dAssignment_541_, v_mvarId_519_, v___x_545_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 8, v___x_546_);
v___x_548_ = v___x_543_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_depth_533_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_levelAssignDepth_534_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_mvarCounter_535_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_lDepth_536_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_decls_537_);
lean_ctor_set(v_reuseFailAlloc_555_, 5, v_userNames_538_);
lean_ctor_set(v_reuseFailAlloc_555_, 6, v_lAssignment_539_);
lean_ctor_set(v_reuseFailAlloc_555_, 7, v_eAssignment_540_);
lean_ctor_set(v_reuseFailAlloc_555_, 8, v___x_546_);
v___x_548_ = v_reuseFailAlloc_555_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_550_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_548_);
v___x_550_ = v___x_531_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_cache_526_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_zetaDeltaFVarIds_527_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v_postponed_528_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v_diag_529_);
v___x_550_ = v_reuseFailAlloc_554_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = lean_st_ref_set(v___y_522_, v___x_550_);
v___x_552_ = lean_box(0);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg___boxed(lean_object* v_mvarId_558_, lean_object* v_fvars_559_, lean_object* v_mvarIdPending_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_558_, v_fvars_559_, v_mvarIdPending_560_, v___y_561_);
lean_dec(v___y_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(lean_object* v___x_564_, lean_object* v_userName_565_, lean_object* v_lctx_566_, lean_object* v_localInstances_567_, lean_object* v_type_568_, lean_object* v_max_569_, lean_object* v_mvarId_570_, lean_object* v_lctx_571_, lean_object* v_localInsts_572_, lean_object* v_fvars_573_, lean_object* v_type_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_array_get_size(v_fvars_573_);
v___x_583_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_574_, v___x_564_, v___x_582_, v_fvars_573_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; uint8_t v___x_585_; lean_object* v___x_586_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref(v___x_583_);
v___x_585_ = 2;
lean_inc(v___x_564_);
v___x_586_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_571_, v_localInsts_572_, v_a_584_, v___x_585_, v_userName_565_, v___x_564_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref(v___x_586_);
v___x_588_ = lean_box(0);
lean_inc(v___x_564_);
lean_inc_ref(v_type_568_);
v___x_589_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_566_, v_localInstances_567_, v_type_568_, v___x_585_, v___x_588_, v___x_564_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_591_; lean_object* v___y_593_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref(v___x_589_);
v___x_591_ = l_Lean_Expr_mvarId_x21(v_a_587_);
lean_dec(v_a_587_);
v___x_603_ = l_Lean_Expr_mvarId_x21(v_a_590_);
lean_inc(v___x_591_);
lean_inc_ref(v_fvars_573_);
v___x_604_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v___x_603_, v_fvars_573_, v___x_591_, v___y_578_);
lean_dec_ref(v___x_604_);
v___x_605_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkAppBVars(v_a_590_, v___x_582_);
v___x_606_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(v_max_569_, v___x_564_, v_type_568_, v___x_605_);
lean_dec_ref(v___x_605_);
lean_dec(v___x_564_);
v___x_607_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_570_, v___x_606_, v___y_578_);
v___y_593_ = v___x_607_;
goto v___jp_592_;
v___jp_592_:
{
lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_601_; 
v_isSharedCheck_601_ = !lean_is_exclusive(v___y_593_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v___y_593_, 0);
lean_dec(v_unused_602_);
v___x_595_ = v___y_593_;
v_isShared_596_ = v_isSharedCheck_601_;
goto v_resetjp_594_;
}
else
{
lean_dec(v___y_593_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_601_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v_fvars_573_);
lean_ctor_set(v___x_597_, 1, v___x_591_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_597_);
v___x_599_ = v___x_595_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec(v_a_587_);
lean_dec_ref(v_fvars_573_);
lean_dec(v_mvarId_570_);
lean_dec_ref(v_type_568_);
lean_dec(v___x_564_);
v_a_608_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_589_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_589_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref(v_fvars_573_);
lean_dec(v_mvarId_570_);
lean_dec_ref(v_type_568_);
lean_dec_ref(v_localInstances_567_);
lean_dec_ref(v_lctx_566_);
lean_dec(v___x_564_);
v_a_616_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_586_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_586_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v_fvars_573_);
lean_dec_ref(v_localInsts_572_);
lean_dec_ref(v_lctx_571_);
lean_dec(v_mvarId_570_);
lean_dec_ref(v_type_568_);
lean_dec_ref(v_localInstances_567_);
lean_dec_ref(v_lctx_566_);
lean_dec(v_userName_565_);
lean_dec(v___x_564_);
v_a_624_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_583_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_583_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed(lean_object** _args){
lean_object* v___x_632_ = _args[0];
lean_object* v_userName_633_ = _args[1];
lean_object* v_lctx_634_ = _args[2];
lean_object* v_localInstances_635_ = _args[3];
lean_object* v_type_636_ = _args[4];
lean_object* v_max_637_ = _args[5];
lean_object* v_mvarId_638_ = _args[6];
lean_object* v_lctx_639_ = _args[7];
lean_object* v_localInsts_640_ = _args[8];
lean_object* v_fvars_641_ = _args[9];
lean_object* v_type_642_ = _args[10];
lean_object* v___y_643_ = _args[11];
lean_object* v___y_644_ = _args[12];
lean_object* v___y_645_ = _args[13];
lean_object* v___y_646_ = _args[14];
lean_object* v___y_647_ = _args[15];
lean_object* v___y_648_ = _args[16];
lean_object* v___y_649_ = _args[17];
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(v___x_632_, v_userName_633_, v_lctx_634_, v_localInstances_635_, v_type_636_, v_max_637_, v_mvarId_638_, v_lctx_639_, v_localInsts_640_, v_fvars_641_, v_type_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v_max_637_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(lean_object* v_env_651_, lean_object* v_localInsts_652_, lean_object* v_fvar_653_, lean_object* v_type_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Meta_Sym_isClass_x3f(v_env_651_, v_type_654_);
if (lean_obj_tag(v___x_655_) == 1)
{
lean_object* v_val_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_val_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_val_656_);
lean_dec_ref(v___x_655_);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v_val_656_);
lean_ctor_set(v___x_657_, 1, v_fvar_653_);
v___x_658_ = lean_array_push(v_localInsts_652_, v___x_657_);
return v___x_658_;
}
else
{
lean_dec(v___x_655_);
lean_dec_ref(v_fvar_653_);
return v_localInsts_652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(size_t v_sz_659_, size_t v_i_660_, lean_object* v_bs_661_){
_start:
{
uint8_t v___x_662_; 
v___x_662_ = lean_usize_dec_lt(v_i_660_, v_sz_659_);
if (v___x_662_ == 0)
{
return v_bs_661_;
}
else
{
lean_object* v_v_663_; lean_object* v___x_664_; lean_object* v_bs_x27_665_; lean_object* v___x_666_; size_t v___x_667_; size_t v___x_668_; lean_object* v___x_669_; 
v_v_663_ = lean_array_uget(v_bs_661_, v_i_660_);
v___x_664_ = lean_unsigned_to_nat(0u);
v_bs_x27_665_ = lean_array_uset(v_bs_661_, v_i_660_, v___x_664_);
v___x_666_ = l_Lean_Expr_fvarId_x21(v_v_663_);
lean_dec(v_v_663_);
v___x_667_ = ((size_t)1ULL);
v___x_668_ = lean_usize_add(v_i_660_, v___x_667_);
v___x_669_ = lean_array_uset(v_bs_x27_665_, v_i_660_, v___x_666_);
v_i_660_ = v___x_668_;
v_bs_661_ = v___x_669_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2___boxed(lean_object* v_sz_671_, lean_object* v_i_672_, lean_object* v_bs_673_){
_start:
{
size_t v_sz_boxed_674_; size_t v_i_boxed_675_; lean_object* v_res_676_; 
v_sz_boxed_674_ = lean_unbox_usize(v_sz_671_);
lean_dec(v_sz_671_);
v_i_boxed_675_ = lean_unbox_usize(v_i_672_);
lean_dec(v_i_672_);
v_res_676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_boxed_674_, v_i_boxed_675_, v_bs_673_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(lean_object* v_mvarId_681_, lean_object* v_max_682_, lean_object* v_names_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = lean_nat_dec_eq(v_max_682_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_st_ref_get(v_a_689_);
lean_inc(v_mvarId_681_);
v___x_694_ = l_Lean_MVarId_getDecl(v_mvarId_681_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v_env_696_; lean_object* v_userName_697_; lean_object* v_lctx_698_; lean_object* v_type_699_; lean_object* v_localInstances_700_; lean_object* v___f_701_; lean_object* v___f_702_; lean_object* v___f_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref(v___x_694_);
v_env_696_ = lean_ctor_get(v___x_693_, 0);
lean_inc_ref(v_env_696_);
lean_dec(v___x_693_);
v_userName_697_ = lean_ctor_get(v_a_695_, 0);
lean_inc(v_userName_697_);
v_lctx_698_ = lean_ctor_get(v_a_695_, 1);
lean_inc_ref_n(v_lctx_698_, 2);
v_type_699_ = lean_ctor_get(v_a_695_, 2);
lean_inc_ref_n(v_type_699_, 2);
v_localInstances_700_ = lean_ctor_get(v_a_695_, 4);
lean_inc_ref_n(v_localInstances_700_, 2);
lean_dec(v_a_695_);
v___f_701_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed), 8, 1);
lean_closure_set(v___f_701_, 0, v_names_683_);
lean_inc(v_max_682_);
v___f_702_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed), 18, 7);
lean_closure_set(v___f_702_, 0, v___x_691_);
lean_closure_set(v___f_702_, 1, v_userName_697_);
lean_closure_set(v___f_702_, 2, v_lctx_698_);
lean_closure_set(v___f_702_, 3, v_localInstances_700_);
lean_closure_set(v___f_702_, 4, v_type_699_);
lean_closure_set(v___f_702_, 5, v_max_682_);
lean_closure_set(v___f_702_, 6, v_mvarId_681_);
v___f_703_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2), 4, 1);
lean_closure_set(v___f_703_, 0, v_env_696_);
v___x_704_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0));
v___x_705_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(v_max_682_, v___f_702_, v___f_701_, v___f_703_, v___x_691_, v_lctx_698_, v_localInstances_700_, v___x_704_, v_type_699_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec(v_max_682_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_725_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_725_ == 0)
{
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_725_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_725_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v_fst_710_; lean_object* v_snd_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_724_; 
v_fst_710_ = lean_ctor_get(v_a_706_, 0);
v_snd_711_ = lean_ctor_get(v_a_706_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_a_706_);
if (v_isSharedCheck_724_ == 0)
{
v___x_713_ = v_a_706_;
v_isShared_714_ = v_isSharedCheck_724_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_snd_711_);
lean_inc(v_fst_710_);
lean_dec(v_a_706_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_724_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
size_t v_sz_715_; size_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
v_sz_715_ = lean_array_size(v_fst_710_);
v___x_716_ = ((size_t)0ULL);
v___x_717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_715_, v___x_716_, v_fst_710_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_717_);
v___x_719_ = v___x_713_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_snd_711_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_719_);
v___x_721_ = v___x_708_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
v_a_726_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_705_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_705_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v___x_693_);
lean_dec_ref(v_names_683_);
lean_dec(v_max_682_);
lean_dec(v_mvarId_681_);
v_a_734_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_694_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_694_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
lean_dec_ref(v_names_683_);
lean_dec(v_max_682_);
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v_mvarId_681_);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___boxed(lean_object* v_mvarId_745_, lean_object* v_max_746_, lean_object* v_names_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_745_, v_max_746_, v_names_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(lean_object* v_mvarId_756_, lean_object* v_fvars_757_, lean_object* v_mvarIdPending_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_756_, v_fvars_757_, v_mvarIdPending_758_, v___y_760_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___boxed(lean_object* v_mvarId_765_, lean_object* v_fvars_766_, lean_object* v_mvarIdPending_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(v_mvarId_765_, v_fvars_766_, v_mvarIdPending_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(lean_object* v_mvarId_774_, lean_object* v_val_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_774_, v_val_775_, v___y_777_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___boxed(lean_object* v_mvarId_782_, lean_object* v_val_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(v_mvarId_782_, v_val_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0(lean_object* v_00_u03b2_790_, lean_object* v_x_791_, lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_x_791_, v_x_792_, v_x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_795_, lean_object* v_x_796_, size_t v_x_797_, size_t v_x_798_, lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_796_, v_x_797_, v_x_798_, v_x_799_, v_x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
size_t v_x_5893__boxed_808_; size_t v_x_5894__boxed_809_; lean_object* v_res_810_; 
v_x_5893__boxed_808_ = lean_unbox_usize(v_x_804_);
lean_dec(v_x_804_);
v_x_5894__boxed_809_ = lean_unbox_usize(v_x_805_);
lean_dec(v_x_805_);
v_res_810_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(v_00_u03b2_802_, v_x_803_, v_x_5893__boxed_808_, v_x_5894__boxed_809_, v_x_806_, v_x_807_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_811_, lean_object* v_n_812_, lean_object* v_k_813_, lean_object* v_v_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(v_n_812_, v_k_813_, v_v_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_816_, size_t v_depth_817_, lean_object* v_keys_818_, lean_object* v_vals_819_, lean_object* v_heq_820_, lean_object* v_i_821_, lean_object* v_entries_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_817_, v_keys_818_, v_vals_819_, v_i_821_, v_entries_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_824_, lean_object* v_depth_825_, lean_object* v_keys_826_, lean_object* v_vals_827_, lean_object* v_heq_828_, lean_object* v_i_829_, lean_object* v_entries_830_){
_start:
{
size_t v_depth_boxed_831_; lean_object* v_res_832_; 
v_depth_boxed_831_ = lean_unbox_usize(v_depth_825_);
lean_dec(v_depth_825_);
v_res_832_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_824_, v_depth_boxed_831_, v_keys_826_, v_vals_827_, v_heq_828_, v_i_829_, v_entries_830_);
lean_dec_ref(v_vals_827_);
lean_dec_ref(v_keys_826_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_833_, lean_object* v_x_834_, lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_x_834_, v_x_835_, v_x_836_, v_x_837_);
return v___x_838_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat(void){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = lean_unsigned_to_nat(1000000u);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx(lean_object* v_x_840_){
_start:
{
if (lean_obj_tag(v_x_840_) == 0)
{
lean_object* v___x_841_; 
v___x_841_ = lean_unsigned_to_nat(0u);
return v___x_841_;
}
else
{
lean_object* v___x_842_; 
v___x_842_ = lean_unsigned_to_nat(1u);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx___boxed(lean_object* v_x_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_Meta_Sym_IntrosResult_ctorIdx(v_x_843_);
lean_dec(v_x_843_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(lean_object* v_t_845_, lean_object* v_k_846_){
_start:
{
if (lean_obj_tag(v_t_845_) == 0)
{
return v_k_846_;
}
else
{
lean_object* v_newDecls_847_; lean_object* v_mvarId_848_; lean_object* v___x_849_; 
v_newDecls_847_ = lean_ctor_get(v_t_845_, 0);
lean_inc_ref(v_newDecls_847_);
v_mvarId_848_ = lean_ctor_get(v_t_845_, 1);
lean_inc(v_mvarId_848_);
lean_dec_ref(v_t_845_);
v___x_849_ = lean_apply_2(v_k_846_, v_newDecls_847_, v_mvarId_848_);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim(lean_object* v_motive_850_, lean_object* v_ctorIdx_851_, lean_object* v_t_852_, lean_object* v_h_853_, lean_object* v_k_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_852_, v_k_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___boxed(lean_object* v_motive_856_, lean_object* v_ctorIdx_857_, lean_object* v_t_858_, lean_object* v_h_859_, lean_object* v_k_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Meta_Sym_IntrosResult_ctorElim(v_motive_856_, v_ctorIdx_857_, v_t_858_, v_h_859_, v_k_860_);
lean_dec(v_ctorIdx_857_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim___redArg(lean_object* v_t_862_, lean_object* v_failed_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_862_, v_failed_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim(lean_object* v_motive_865_, lean_object* v_t_866_, lean_object* v_h_867_, lean_object* v_failed_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_866_, v_failed_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim___redArg(lean_object* v_t_870_, lean_object* v_goal_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_870_, v_goal_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim(lean_object* v_motive_873_, lean_object* v_t_874_, lean_object* v_h_875_, lean_object* v_goal_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_874_, v_goal_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros(lean_object* v_mvarId_878_, lean_object* v_names_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_result_888_; lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_904_ = lean_array_get_size(v_names_879_);
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = lean_nat_dec_eq(v___x_904_, v___x_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
v___x_907_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_878_, v___x_904_, v_names_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref(v___x_907_);
v_result_888_ = v_a_908_;
goto v___jp_887_;
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
v_a_909_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_907_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_907_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec_ref(v_names_879_);
v___x_917_ = lean_unsigned_to_nat(1000000u);
v___x_918_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
v___x_919_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_878_, v___x_917_, v___x_918_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref(v___x_919_);
v_result_888_ = v_a_920_;
goto v___jp_887_;
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
v_a_921_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_919_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_919_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
v___jp_887_:
{
lean_object* v_fst_889_; lean_object* v_snd_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_903_; 
v_fst_889_ = lean_ctor_get(v_result_888_, 0);
v_snd_890_ = lean_ctor_get(v_result_888_, 1);
v_isSharedCheck_903_ = !lean_is_exclusive(v_result_888_);
if (v_isSharedCheck_903_ == 0)
{
v___x_892_ = v_result_888_;
v_isShared_893_ = v_isSharedCheck_903_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_snd_890_);
lean_inc(v_fst_889_);
lean_dec(v_result_888_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_903_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_894_ = lean_array_get_size(v_fst_889_);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_nat_dec_eq(v___x_894_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_898_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 1);
v___x_898_ = v___x_892_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_fst_889_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_snd_890_);
v___x_898_ = v_reuseFailAlloc_900_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; 
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
else
{
lean_object* v___x_901_; lean_object* v___x_902_; 
lean_del_object(v___x_892_);
lean_dec(v_snd_890_);
lean_dec(v_fst_889_);
v___x_901_ = lean_box(0);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros___boxed(lean_object* v_mvarId_929_, lean_object* v_names_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Meta_Sym_intros(v_mvarId_929_, v_names_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN(lean_object* v_mvarId_939_, lean_object* v_num_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
lean_inc(v_num_940_);
v___x_949_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_939_, v_num_940_, v___x_948_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_972_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_972_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_972_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_972_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_fst_954_; lean_object* v_snd_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_971_; 
v_fst_954_ = lean_ctor_get(v_a_950_, 0);
v_snd_955_ = lean_ctor_get(v_a_950_, 1);
v_isSharedCheck_971_ = !lean_is_exclusive(v_a_950_);
if (v_isSharedCheck_971_ == 0)
{
v___x_957_ = v_a_950_;
v_isShared_958_ = v_isSharedCheck_971_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_snd_955_);
lean_inc(v_fst_954_);
lean_dec(v_a_950_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_971_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_959_ = lean_array_get_size(v_fst_954_);
v___x_960_ = lean_nat_dec_eq(v___x_959_, v_num_940_);
lean_dec(v_num_940_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_963_; 
lean_del_object(v___x_957_);
lean_dec(v_snd_955_);
lean_dec(v_fst_954_);
v___x_961_ = lean_box(0);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_961_);
v___x_963_ = v___x_952_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
else
{
lean_object* v___x_966_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set_tag(v___x_957_, 1);
v___x_966_ = v___x_957_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_fst_954_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_snd_955_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_966_);
v___x_968_ = v___x_952_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec(v_num_940_);
v_a_973_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_949_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_949_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN___boxed(lean_object* v_mvarId_981_, lean_object* v_num_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_Meta_Sym_introN(v_mvarId_981_, v_num_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
return v_res_990_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
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
