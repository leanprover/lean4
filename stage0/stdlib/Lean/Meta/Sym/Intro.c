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
size_t v_x_5332__boxed_467_; size_t v_x_5333__boxed_468_; lean_object* v_res_469_; 
v_x_5332__boxed_467_ = lean_unbox_usize(v_x_463_);
lean_dec(v_x_463_);
v_x_5333__boxed_468_ = lean_unbox_usize(v_x_464_);
lean_dec(v_x_464_);
v_res_469_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_462_, v_x_5332__boxed_467_, v_x_5333__boxed_468_, v_x_465_, v_x_466_);
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
lean_object* v___x_481_; lean_object* v_mctx_482_; lean_object* v_cache_483_; lean_object* v_zetaDeltaFVarIds_484_; lean_object* v_postponed_485_; lean_object* v_diag_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_514_; 
v___x_481_ = lean_st_ref_take(v___y_479_);
v_mctx_482_ = lean_ctor_get(v___x_481_, 0);
v_cache_483_ = lean_ctor_get(v___x_481_, 1);
v_zetaDeltaFVarIds_484_ = lean_ctor_get(v___x_481_, 2);
v_postponed_485_ = lean_ctor_get(v___x_481_, 3);
v_diag_486_ = lean_ctor_get(v___x_481_, 4);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_514_ == 0)
{
v___x_488_ = v___x_481_;
v_isShared_489_ = v_isSharedCheck_514_;
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
v_isShared_489_ = v_isSharedCheck_514_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v_depth_490_; lean_object* v_levelAssignDepth_491_; lean_object* v_lmvarCounter_492_; lean_object* v_mvarCounter_493_; lean_object* v_lDecls_494_; lean_object* v_decls_495_; lean_object* v_userNames_496_; lean_object* v_lAssignment_497_; lean_object* v_eAssignment_498_; lean_object* v_dAssignment_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_513_; 
v_depth_490_ = lean_ctor_get(v_mctx_482_, 0);
v_levelAssignDepth_491_ = lean_ctor_get(v_mctx_482_, 1);
v_lmvarCounter_492_ = lean_ctor_get(v_mctx_482_, 2);
v_mvarCounter_493_ = lean_ctor_get(v_mctx_482_, 3);
v_lDecls_494_ = lean_ctor_get(v_mctx_482_, 4);
v_decls_495_ = lean_ctor_get(v_mctx_482_, 5);
v_userNames_496_ = lean_ctor_get(v_mctx_482_, 6);
v_lAssignment_497_ = lean_ctor_get(v_mctx_482_, 7);
v_eAssignment_498_ = lean_ctor_get(v_mctx_482_, 8);
v_dAssignment_499_ = lean_ctor_get(v_mctx_482_, 9);
v_isSharedCheck_513_ = !lean_is_exclusive(v_mctx_482_);
if (v_isSharedCheck_513_ == 0)
{
v___x_501_ = v_mctx_482_;
v_isShared_502_ = v_isSharedCheck_513_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_dAssignment_499_);
lean_inc(v_eAssignment_498_);
lean_inc(v_lAssignment_497_);
lean_inc(v_userNames_496_);
lean_inc(v_decls_495_);
lean_inc(v_lDecls_494_);
lean_inc(v_mvarCounter_493_);
lean_inc(v_lmvarCounter_492_);
lean_inc(v_levelAssignDepth_491_);
lean_inc(v_depth_490_);
lean_dec(v_mctx_482_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_513_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_eAssignment_498_, v_mvarId_477_, v_val_478_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 8, v___x_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_depth_490_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_levelAssignDepth_491_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_lmvarCounter_492_);
lean_ctor_set(v_reuseFailAlloc_512_, 3, v_mvarCounter_493_);
lean_ctor_set(v_reuseFailAlloc_512_, 4, v_lDecls_494_);
lean_ctor_set(v_reuseFailAlloc_512_, 5, v_decls_495_);
lean_ctor_set(v_reuseFailAlloc_512_, 6, v_userNames_496_);
lean_ctor_set(v_reuseFailAlloc_512_, 7, v_lAssignment_497_);
lean_ctor_set(v_reuseFailAlloc_512_, 8, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_512_, 9, v_dAssignment_499_);
v___x_505_ = v_reuseFailAlloc_512_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_507_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_505_);
v___x_507_ = v___x_488_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_cache_483_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_zetaDeltaFVarIds_484_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_postponed_485_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v_diag_486_);
v___x_507_ = v_reuseFailAlloc_511_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = lean_st_ref_set(v___y_479_, v___x_507_);
v___x_509_ = lean_box(0);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg___boxed(lean_object* v_mvarId_515_, lean_object* v_val_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_515_, v_val_516_, v___y_517_);
lean_dec(v___y_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(lean_object* v_mvarId_520_, lean_object* v_fvars_521_, lean_object* v_mvarIdPending_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; lean_object* v_mctx_526_; lean_object* v_cache_527_; lean_object* v_zetaDeltaFVarIds_528_; lean_object* v_postponed_529_; lean_object* v_diag_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_559_; 
v___x_525_ = lean_st_ref_take(v___y_523_);
v_mctx_526_ = lean_ctor_get(v___x_525_, 0);
v_cache_527_ = lean_ctor_get(v___x_525_, 1);
v_zetaDeltaFVarIds_528_ = lean_ctor_get(v___x_525_, 2);
v_postponed_529_ = lean_ctor_get(v___x_525_, 3);
v_diag_530_ = lean_ctor_get(v___x_525_, 4);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_559_ == 0)
{
v___x_532_ = v___x_525_;
v_isShared_533_ = v_isSharedCheck_559_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_diag_530_);
lean_inc(v_postponed_529_);
lean_inc(v_zetaDeltaFVarIds_528_);
lean_inc(v_cache_527_);
lean_inc(v_mctx_526_);
lean_dec(v___x_525_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_559_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_depth_534_; lean_object* v_levelAssignDepth_535_; lean_object* v_lmvarCounter_536_; lean_object* v_mvarCounter_537_; lean_object* v_lDecls_538_; lean_object* v_decls_539_; lean_object* v_userNames_540_; lean_object* v_lAssignment_541_; lean_object* v_eAssignment_542_; lean_object* v_dAssignment_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_558_; 
v_depth_534_ = lean_ctor_get(v_mctx_526_, 0);
v_levelAssignDepth_535_ = lean_ctor_get(v_mctx_526_, 1);
v_lmvarCounter_536_ = lean_ctor_get(v_mctx_526_, 2);
v_mvarCounter_537_ = lean_ctor_get(v_mctx_526_, 3);
v_lDecls_538_ = lean_ctor_get(v_mctx_526_, 4);
v_decls_539_ = lean_ctor_get(v_mctx_526_, 5);
v_userNames_540_ = lean_ctor_get(v_mctx_526_, 6);
v_lAssignment_541_ = lean_ctor_get(v_mctx_526_, 7);
v_eAssignment_542_ = lean_ctor_get(v_mctx_526_, 8);
v_dAssignment_543_ = lean_ctor_get(v_mctx_526_, 9);
v_isSharedCheck_558_ = !lean_is_exclusive(v_mctx_526_);
if (v_isSharedCheck_558_ == 0)
{
v___x_545_ = v_mctx_526_;
v_isShared_546_ = v_isSharedCheck_558_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_dAssignment_543_);
lean_inc(v_eAssignment_542_);
lean_inc(v_lAssignment_541_);
lean_inc(v_userNames_540_);
lean_inc(v_decls_539_);
lean_inc(v_lDecls_538_);
lean_inc(v_mvarCounter_537_);
lean_inc(v_lmvarCounter_536_);
lean_inc(v_levelAssignDepth_535_);
lean_inc(v_depth_534_);
lean_dec(v_mctx_526_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_558_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v_fvars_521_);
lean_ctor_set(v___x_547_, 1, v_mvarIdPending_522_);
v___x_548_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_dAssignment_543_, v_mvarId_520_, v___x_547_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 9, v___x_548_);
v___x_550_ = v___x_545_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_depth_534_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_levelAssignDepth_535_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_lmvarCounter_536_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v_mvarCounter_537_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v_lDecls_538_);
lean_ctor_set(v_reuseFailAlloc_557_, 5, v_decls_539_);
lean_ctor_set(v_reuseFailAlloc_557_, 6, v_userNames_540_);
lean_ctor_set(v_reuseFailAlloc_557_, 7, v_lAssignment_541_);
lean_ctor_set(v_reuseFailAlloc_557_, 8, v_eAssignment_542_);
lean_ctor_set(v_reuseFailAlloc_557_, 9, v___x_548_);
v___x_550_ = v_reuseFailAlloc_557_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_552_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_550_);
v___x_552_ = v___x_532_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_cache_527_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_zetaDeltaFVarIds_528_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_postponed_529_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v_diag_530_);
v___x_552_ = v_reuseFailAlloc_556_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = lean_st_ref_set(v___y_523_, v___x_552_);
v___x_554_ = lean_box(0);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg___boxed(lean_object* v_mvarId_560_, lean_object* v_fvars_561_, lean_object* v_mvarIdPending_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_560_, v_fvars_561_, v_mvarIdPending_562_, v___y_563_);
lean_dec(v___y_563_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(lean_object* v___x_566_, lean_object* v_userName_567_, lean_object* v_lctx_568_, lean_object* v_localInstances_569_, lean_object* v_type_570_, lean_object* v_max_571_, lean_object* v_mvarId_572_, lean_object* v_lctx_573_, lean_object* v_localInsts_574_, lean_object* v_fvars_575_, lean_object* v_type_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_array_get_size(v_fvars_575_);
v___x_585_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_576_, v___x_566_, v___x_584_, v_fvars_575_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; uint8_t v___x_587_; lean_object* v___x_588_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref(v___x_585_);
v___x_587_ = 2;
lean_inc(v___x_566_);
v___x_588_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_573_, v_localInsts_574_, v_a_586_, v___x_587_, v_userName_567_, v___x_566_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref(v___x_588_);
v___x_590_ = lean_box(0);
lean_inc(v___x_566_);
lean_inc_ref(v_type_570_);
v___x_591_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_568_, v_localInstances_569_, v_type_570_, v___x_587_, v___x_590_, v___x_566_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_593_; lean_object* v___y_595_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref(v___x_591_);
v___x_593_ = l_Lean_Expr_mvarId_x21(v_a_589_);
lean_dec(v_a_589_);
v___x_605_ = l_Lean_Expr_mvarId_x21(v_a_592_);
lean_inc(v___x_593_);
lean_inc_ref(v_fvars_575_);
v___x_606_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v___x_605_, v_fvars_575_, v___x_593_, v___y_580_);
lean_dec_ref(v___x_606_);
v___x_607_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkAppBVars(v_a_592_, v___x_584_);
v___x_608_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(v_max_571_, v___x_566_, v_type_570_, v___x_607_);
lean_dec_ref(v___x_607_);
lean_dec(v___x_566_);
v___x_609_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_572_, v___x_608_, v___y_580_);
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
lean_ctor_set(v___x_599_, 0, v_fvars_575_);
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
lean_dec_ref(v_fvars_575_);
lean_dec(v_mvarId_572_);
lean_dec_ref(v_type_570_);
lean_dec(v___x_566_);
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
lean_dec_ref(v_fvars_575_);
lean_dec(v_mvarId_572_);
lean_dec_ref(v_type_570_);
lean_dec_ref(v_localInstances_569_);
lean_dec_ref(v_lctx_568_);
lean_dec(v___x_566_);
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
lean_dec_ref(v_fvars_575_);
lean_dec_ref(v_localInsts_574_);
lean_dec_ref(v_lctx_573_);
lean_dec(v_mvarId_572_);
lean_dec_ref(v_type_570_);
lean_dec_ref(v_localInstances_569_);
lean_dec_ref(v_lctx_568_);
lean_dec(v_userName_567_);
lean_dec(v___x_566_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed(lean_object** _args){
lean_object* v___x_634_ = _args[0];
lean_object* v_userName_635_ = _args[1];
lean_object* v_lctx_636_ = _args[2];
lean_object* v_localInstances_637_ = _args[3];
lean_object* v_type_638_ = _args[4];
lean_object* v_max_639_ = _args[5];
lean_object* v_mvarId_640_ = _args[6];
lean_object* v_lctx_641_ = _args[7];
lean_object* v_localInsts_642_ = _args[8];
lean_object* v_fvars_643_ = _args[9];
lean_object* v_type_644_ = _args[10];
lean_object* v___y_645_ = _args[11];
lean_object* v___y_646_ = _args[12];
lean_object* v___y_647_ = _args[13];
lean_object* v___y_648_ = _args[14];
lean_object* v___y_649_ = _args[15];
lean_object* v___y_650_ = _args[16];
lean_object* v___y_651_ = _args[17];
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(v___x_634_, v_userName_635_, v_lctx_636_, v_localInstances_637_, v_type_638_, v_max_639_, v_mvarId_640_, v_lctx_641_, v_localInsts_642_, v_fvars_643_, v_type_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v_max_639_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(lean_object* v_env_653_, lean_object* v_localInsts_654_, lean_object* v_fvar_655_, lean_object* v_type_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Meta_Sym_isClass_x3f(v_env_653_, v_type_656_);
if (lean_obj_tag(v___x_657_) == 1)
{
lean_object* v_val_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_val_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_val_658_);
lean_dec_ref(v___x_657_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v_val_658_);
lean_ctor_set(v___x_659_, 1, v_fvar_655_);
v___x_660_ = lean_array_push(v_localInsts_654_, v___x_659_);
return v___x_660_;
}
else
{
lean_dec(v___x_657_);
lean_dec_ref(v_fvar_655_);
return v_localInsts_654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(size_t v_sz_661_, size_t v_i_662_, lean_object* v_bs_663_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = lean_usize_dec_lt(v_i_662_, v_sz_661_);
if (v___x_664_ == 0)
{
return v_bs_663_;
}
else
{
lean_object* v_v_665_; lean_object* v___x_666_; lean_object* v_bs_x27_667_; lean_object* v___x_668_; size_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; 
v_v_665_ = lean_array_uget(v_bs_663_, v_i_662_);
v___x_666_ = lean_unsigned_to_nat(0u);
v_bs_x27_667_ = lean_array_uset(v_bs_663_, v_i_662_, v___x_666_);
v___x_668_ = l_Lean_Expr_fvarId_x21(v_v_665_);
lean_dec(v_v_665_);
v___x_669_ = ((size_t)1ULL);
v___x_670_ = lean_usize_add(v_i_662_, v___x_669_);
v___x_671_ = lean_array_uset(v_bs_x27_667_, v_i_662_, v___x_668_);
v_i_662_ = v___x_670_;
v_bs_663_ = v___x_671_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2___boxed(lean_object* v_sz_673_, lean_object* v_i_674_, lean_object* v_bs_675_){
_start:
{
size_t v_sz_boxed_676_; size_t v_i_boxed_677_; lean_object* v_res_678_; 
v_sz_boxed_676_ = lean_unbox_usize(v_sz_673_);
lean_dec(v_sz_673_);
v_i_boxed_677_ = lean_unbox_usize(v_i_674_);
lean_dec(v_i_674_);
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_boxed_676_, v_i_boxed_677_, v_bs_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(lean_object* v_mvarId_683_, lean_object* v_max_684_, lean_object* v_names_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_nat_dec_eq(v_max_684_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_st_ref_get(v_a_691_);
lean_inc(v_mvarId_683_);
v___x_696_ = l_Lean_MVarId_getDecl(v_mvarId_683_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v_env_698_; lean_object* v_userName_699_; lean_object* v_lctx_700_; lean_object* v_type_701_; lean_object* v_localInstances_702_; lean_object* v___f_703_; lean_object* v___f_704_; lean_object* v___f_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref(v___x_696_);
v_env_698_ = lean_ctor_get(v___x_695_, 0);
lean_inc_ref(v_env_698_);
lean_dec(v___x_695_);
v_userName_699_ = lean_ctor_get(v_a_697_, 0);
lean_inc(v_userName_699_);
v_lctx_700_ = lean_ctor_get(v_a_697_, 1);
lean_inc_ref_n(v_lctx_700_, 2);
v_type_701_ = lean_ctor_get(v_a_697_, 2);
lean_inc_ref_n(v_type_701_, 2);
v_localInstances_702_ = lean_ctor_get(v_a_697_, 4);
lean_inc_ref_n(v_localInstances_702_, 2);
lean_dec(v_a_697_);
v___f_703_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed), 8, 1);
lean_closure_set(v___f_703_, 0, v_names_685_);
lean_inc(v_max_684_);
v___f_704_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed), 18, 7);
lean_closure_set(v___f_704_, 0, v___x_693_);
lean_closure_set(v___f_704_, 1, v_userName_699_);
lean_closure_set(v___f_704_, 2, v_lctx_700_);
lean_closure_set(v___f_704_, 3, v_localInstances_702_);
lean_closure_set(v___f_704_, 4, v_type_701_);
lean_closure_set(v___f_704_, 5, v_max_684_);
lean_closure_set(v___f_704_, 6, v_mvarId_683_);
v___f_705_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2), 4, 1);
lean_closure_set(v___f_705_, 0, v_env_698_);
v___x_706_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0));
v___x_707_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(v_max_684_, v___f_704_, v___f_703_, v___f_705_, v___x_693_, v_lctx_700_, v_localInstances_702_, v___x_706_, v_type_701_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
lean_dec(v_max_684_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_727_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_727_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_727_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_727_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v_fst_712_; lean_object* v_snd_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_726_; 
v_fst_712_ = lean_ctor_get(v_a_708_, 0);
v_snd_713_ = lean_ctor_get(v_a_708_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_a_708_);
if (v_isSharedCheck_726_ == 0)
{
v___x_715_ = v_a_708_;
v_isShared_716_ = v_isSharedCheck_726_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_snd_713_);
lean_inc(v_fst_712_);
lean_dec(v_a_708_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_726_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
size_t v_sz_717_; size_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v_sz_717_ = lean_array_size(v_fst_712_);
v___x_718_ = ((size_t)0ULL);
v___x_719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_717_, v___x_718_, v_fst_712_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_719_);
v___x_721_ = v___x_715_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_snd_713_);
v___x_721_ = v_reuseFailAlloc_725_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_723_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_721_);
v___x_723_ = v___x_710_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
v_a_728_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_707_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_707_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
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
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v___x_695_);
lean_dec_ref(v_names_685_);
lean_dec(v_max_684_);
lean_dec(v_mvarId_683_);
v_a_736_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_696_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_696_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec_ref(v_names_685_);
lean_dec(v_max_684_);
v___x_744_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
lean_ctor_set(v___x_745_, 1, v_mvarId_683_);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___boxed(lean_object* v_mvarId_747_, lean_object* v_max_748_, lean_object* v_names_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_747_, v_max_748_, v_names_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(lean_object* v_mvarId_758_, lean_object* v_fvars_759_, lean_object* v_mvarIdPending_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_758_, v_fvars_759_, v_mvarIdPending_760_, v___y_762_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___boxed(lean_object* v_mvarId_767_, lean_object* v_fvars_768_, lean_object* v_mvarIdPending_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(v_mvarId_767_, v_fvars_768_, v_mvarIdPending_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(lean_object* v_mvarId_776_, lean_object* v_val_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_776_, v_val_777_, v___y_779_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___boxed(lean_object* v_mvarId_784_, lean_object* v_val_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(v_mvarId_784_, v_val_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0(lean_object* v_00_u03b2_792_, lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_x_793_, v_x_794_, v_x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_797_, lean_object* v_x_798_, size_t v_x_799_, size_t v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_798_, v_x_799_, v_x_800_, v_x_801_, v_x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_804_, lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
size_t v_x_5901__boxed_810_; size_t v_x_5902__boxed_811_; lean_object* v_res_812_; 
v_x_5901__boxed_810_ = lean_unbox_usize(v_x_806_);
lean_dec(v_x_806_);
v_x_5902__boxed_811_ = lean_unbox_usize(v_x_807_);
lean_dec(v_x_807_);
v_res_812_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(v_00_u03b2_804_, v_x_805_, v_x_5901__boxed_810_, v_x_5902__boxed_811_, v_x_808_, v_x_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_813_, lean_object* v_n_814_, lean_object* v_k_815_, lean_object* v_v_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(v_n_814_, v_k_815_, v_v_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_818_, size_t v_depth_819_, lean_object* v_keys_820_, lean_object* v_vals_821_, lean_object* v_heq_822_, lean_object* v_i_823_, lean_object* v_entries_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_819_, v_keys_820_, v_vals_821_, v_i_823_, v_entries_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_826_, lean_object* v_depth_827_, lean_object* v_keys_828_, lean_object* v_vals_829_, lean_object* v_heq_830_, lean_object* v_i_831_, lean_object* v_entries_832_){
_start:
{
size_t v_depth_boxed_833_; lean_object* v_res_834_; 
v_depth_boxed_833_ = lean_unbox_usize(v_depth_827_);
lean_dec(v_depth_827_);
v_res_834_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_826_, v_depth_boxed_833_, v_keys_828_, v_vals_829_, v_heq_830_, v_i_831_, v_entries_832_);
lean_dec_ref(v_vals_829_);
lean_dec_ref(v_keys_828_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_x_836_, v_x_837_, v_x_838_, v_x_839_);
return v___x_840_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat(void){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = lean_unsigned_to_nat(1000000u);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx(lean_object* v_x_842_){
_start:
{
if (lean_obj_tag(v_x_842_) == 0)
{
lean_object* v___x_843_; 
v___x_843_ = lean_unsigned_to_nat(0u);
return v___x_843_;
}
else
{
lean_object* v___x_844_; 
v___x_844_ = lean_unsigned_to_nat(1u);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx___boxed(lean_object* v_x_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Meta_Sym_IntrosResult_ctorIdx(v_x_845_);
lean_dec(v_x_845_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(lean_object* v_t_847_, lean_object* v_k_848_){
_start:
{
if (lean_obj_tag(v_t_847_) == 0)
{
return v_k_848_;
}
else
{
lean_object* v_newDecls_849_; lean_object* v_mvarId_850_; lean_object* v___x_851_; 
v_newDecls_849_ = lean_ctor_get(v_t_847_, 0);
lean_inc_ref(v_newDecls_849_);
v_mvarId_850_ = lean_ctor_get(v_t_847_, 1);
lean_inc(v_mvarId_850_);
lean_dec_ref(v_t_847_);
v___x_851_ = lean_apply_2(v_k_848_, v_newDecls_849_, v_mvarId_850_);
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim(lean_object* v_motive_852_, lean_object* v_ctorIdx_853_, lean_object* v_t_854_, lean_object* v_h_855_, lean_object* v_k_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_854_, v_k_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___boxed(lean_object* v_motive_858_, lean_object* v_ctorIdx_859_, lean_object* v_t_860_, lean_object* v_h_861_, lean_object* v_k_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_Meta_Sym_IntrosResult_ctorElim(v_motive_858_, v_ctorIdx_859_, v_t_860_, v_h_861_, v_k_862_);
lean_dec(v_ctorIdx_859_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim___redArg(lean_object* v_t_864_, lean_object* v_failed_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_864_, v_failed_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim(lean_object* v_motive_867_, lean_object* v_t_868_, lean_object* v_h_869_, lean_object* v_failed_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_868_, v_failed_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim___redArg(lean_object* v_t_872_, lean_object* v_goal_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_872_, v_goal_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim(lean_object* v_motive_875_, lean_object* v_t_876_, lean_object* v_h_877_, lean_object* v_goal_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_876_, v_goal_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros(lean_object* v_mvarId_880_, lean_object* v_names_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_result_890_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_906_ = lean_array_get_size(v_names_881_);
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = lean_nat_dec_eq(v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_880_, v___x_906_, v_names_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref(v___x_909_);
v_result_890_ = v_a_910_;
goto v___jp_889_;
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
v_a_911_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_909_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_909_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
lean_dec_ref(v_names_881_);
v___x_919_ = lean_unsigned_to_nat(1000000u);
v___x_920_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
v___x_921_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_880_, v___x_919_, v___x_920_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref(v___x_921_);
v_result_890_ = v_a_922_;
goto v___jp_889_;
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
v_a_923_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_921_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_921_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
v___jp_889_:
{
lean_object* v_fst_891_; lean_object* v_snd_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_905_; 
v_fst_891_ = lean_ctor_get(v_result_890_, 0);
v_snd_892_ = lean_ctor_get(v_result_890_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v_result_890_);
if (v_isSharedCheck_905_ == 0)
{
v___x_894_ = v_result_890_;
v_isShared_895_ = v_isSharedCheck_905_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_snd_892_);
lean_inc(v_fst_891_);
lean_dec(v_result_890_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_905_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_896_ = lean_array_get_size(v_fst_891_);
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = lean_nat_dec_eq(v___x_896_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_900_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set_tag(v___x_894_, 1);
v___x_900_ = v___x_894_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_fst_891_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_snd_892_);
v___x_900_ = v_reuseFailAlloc_902_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; 
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
else
{
lean_object* v___x_903_; lean_object* v___x_904_; 
lean_del_object(v___x_894_);
lean_dec(v_snd_892_);
lean_dec(v_fst_891_);
v___x_903_ = lean_box(0);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros___boxed(lean_object* v_mvarId_931_, lean_object* v_names_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_Meta_Sym_intros(v_mvarId_931_, v_names_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN(lean_object* v_mvarId_941_, lean_object* v_num_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
lean_inc(v_num_942_);
v___x_951_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_941_, v_num_942_, v___x_950_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_974_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_974_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_974_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_974_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v_fst_956_; lean_object* v_snd_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_973_; 
v_fst_956_ = lean_ctor_get(v_a_952_, 0);
v_snd_957_ = lean_ctor_get(v_a_952_, 1);
v_isSharedCheck_973_ = !lean_is_exclusive(v_a_952_);
if (v_isSharedCheck_973_ == 0)
{
v___x_959_ = v_a_952_;
v_isShared_960_ = v_isSharedCheck_973_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_snd_957_);
lean_inc(v_fst_956_);
lean_dec(v_a_952_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_973_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_961_ = lean_array_get_size(v_fst_956_);
v___x_962_ = lean_nat_dec_eq(v___x_961_, v_num_942_);
lean_dec(v_num_942_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_965_; 
lean_del_object(v___x_959_);
lean_dec(v_snd_957_);
lean_dec(v_fst_956_);
v___x_963_ = lean_box(0);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_963_);
v___x_965_ = v___x_954_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
else
{
lean_object* v___x_968_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 1);
v___x_968_ = v___x_959_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_fst_956_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_snd_957_);
v___x_968_ = v_reuseFailAlloc_972_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_970_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_968_);
v___x_970_ = v___x_954_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_num_942_);
v_a_975_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_951_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_951_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN___boxed(lean_object* v_mvarId_983_, lean_object* v_num_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_Meta_Sym_introN(v_mvarId_983_, v_num_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
return v_res_992_;
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
