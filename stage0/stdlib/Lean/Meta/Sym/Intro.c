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
lean_object* v___x_75_; lean_object* v_env_76_; lean_object* v_nextMacroScope_77_; lean_object* v_auxDeclNGen_78_; lean_object* v_traceState_79_; lean_object* v_cache_80_; lean_object* v_messages_81_; lean_object* v_infoState_82_; lean_object* v_snapshotTasks_83_; lean_object* v_newDecls_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_99_; 
v___x_75_ = lean_st_ref_take(v___y_66_);
v_env_76_ = lean_ctor_get(v___x_75_, 0);
v_nextMacroScope_77_ = lean_ctor_get(v___x_75_, 1);
v_auxDeclNGen_78_ = lean_ctor_get(v___x_75_, 3);
v_traceState_79_ = lean_ctor_get(v___x_75_, 4);
v_cache_80_ = lean_ctor_get(v___x_75_, 5);
v_messages_81_ = lean_ctor_get(v___x_75_, 6);
v_infoState_82_ = lean_ctor_get(v___x_75_, 7);
v_snapshotTasks_83_ = lean_ctor_get(v___x_75_, 8);
v_newDecls_84_ = lean_ctor_get(v___x_75_, 9);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_99_ == 0)
{
lean_object* v_unused_100_; 
v_unused_100_ = lean_ctor_get(v___x_75_, 2);
lean_dec(v_unused_100_);
v___x_86_ = v___x_75_;
v_isShared_87_ = v_isSharedCheck_99_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_newDecls_84_);
lean_inc(v_snapshotTasks_83_);
lean_inc(v_infoState_82_);
lean_inc(v_messages_81_);
lean_inc(v_cache_80_);
lean_inc(v_traceState_79_);
lean_inc(v_auxDeclNGen_78_);
lean_inc(v_nextMacroScope_77_);
lean_inc(v_env_76_);
lean_dec(v___x_75_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_99_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v_r_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_92_; 
lean_inc(v_idx_71_);
lean_inc(v_namePrefix_70_);
v_r_88_ = l_Lean_Name_num___override(v_namePrefix_70_, v_idx_71_);
v___x_89_ = lean_unsigned_to_nat(1u);
v___x_90_ = lean_nat_add(v_idx_71_, v___x_89_);
lean_dec(v_idx_71_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___x_90_);
v___x_92_ = v___x_73_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_namePrefix_70_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v___x_90_);
v___x_92_ = v_reuseFailAlloc_98_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_94_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 2, v___x_92_);
v___x_94_ = v___x_86_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_env_76_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_nextMacroScope_77_);
lean_ctor_set(v_reuseFailAlloc_97_, 2, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_97_, 3, v_auxDeclNGen_78_);
lean_ctor_set(v_reuseFailAlloc_97_, 4, v_traceState_79_);
lean_ctor_set(v_reuseFailAlloc_97_, 5, v_cache_80_);
lean_ctor_set(v_reuseFailAlloc_97_, 6, v_messages_81_);
lean_ctor_set(v_reuseFailAlloc_97_, 7, v_infoState_82_);
lean_ctor_set(v_reuseFailAlloc_97_, 8, v_snapshotTasks_83_);
lean_ctor_set(v_reuseFailAlloc_97_, 9, v_newDecls_84_);
v___x_94_ = v_reuseFailAlloc_97_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_st_ref_set(v___y_66_, v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v_r_88_);
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
lean_dec_ref(v_type_137_);
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
lean_dec_ref(v_type_137_);
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_array_get_size(v_fvars_136_);
v___x_154_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_binderType_149_, v___x_152_, v___x_153_, v_fvars_136_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_156_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref(v___x_154_);
v___x_156_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v___x_158_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_a_157_);
lean_dec_ref(v___x_156_);
lean_inc_ref(v_mkName_131_);
lean_inc(v_a_143_);
lean_inc_ref(v_a_142_);
lean_inc(v_a_141_);
lean_inc_ref(v_a_140_);
lean_inc(v_i_133_);
v___x_158_ = lean_apply_7(v_mkName_131_, v_binderName_148_, v_i_133_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, lean_box(0));
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref(v___x_158_);
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
lean_dec_ref(v___x_162_);
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
lean_dec_ref(v_type_137_);
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_array_get_size(v_fvars_136_);
v___x_207_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_202_, v___x_205_, v___x_206_, v_fvars_136_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_209_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref(v___x_207_);
v___x_209_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_value_203_, v___x_205_, v___x_206_, v_fvars_136_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_211_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
lean_dec_ref(v___x_209_);
v___x_211_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_213_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref(v___x_211_);
lean_inc_ref(v_mkName_131_);
lean_inc(v_a_143_);
lean_inc_ref(v_a_142_);
lean_inc(v_a_141_);
lean_inc_ref(v_a_140_);
lean_inc(v_i_133_);
v___x_213_ = lean_apply_7(v_mkName_131_, v_declName_201_, v_i_133_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, lean_box(0));
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref(v___x_213_);
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
lean_dec_ref(v___x_217_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(lean_object* v_names_299_, lean_object* v_binderName_300_, lean_object* v_i_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_array_get_size(v_names_299_);
v___x_308_ = lean_nat_dec_lt(v_i_301_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Core_mkFreshUserName(v_binderName_300_, v___y_304_, v___y_305_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v_binderName_300_);
v___x_310_ = lean_array_fget_borrowed(v_names_299_, v_i_301_);
lean_inc(v___x_310_);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed(lean_object* v_names_312_, lean_object* v_binderName_313_, lean_object* v_i_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(v_names_312_, v_binderName_313_, v_i_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v_i_314_);
lean_dec_ref(v_names_312_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
lean_object* v_ks_325_; lean_object* v_vs_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_350_; 
v_ks_325_ = lean_ctor_get(v_x_321_, 0);
v_vs_326_ = lean_ctor_get(v_x_321_, 1);
v_isSharedCheck_350_ = !lean_is_exclusive(v_x_321_);
if (v_isSharedCheck_350_ == 0)
{
v___x_328_ = v_x_321_;
v_isShared_329_ = v_isSharedCheck_350_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_vs_326_);
lean_inc(v_ks_325_);
lean_dec(v_x_321_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_350_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_array_get_size(v_ks_325_);
v___x_331_ = lean_nat_dec_lt(v_x_322_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
lean_dec(v_x_322_);
v___x_332_ = lean_array_push(v_ks_325_, v_x_323_);
v___x_333_ = lean_array_push(v_vs_326_, v_x_324_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_333_);
lean_ctor_set(v___x_328_, 0, v___x_332_);
v___x_335_ = v___x_328_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
else
{
lean_object* v_k_x27_337_; uint8_t v___x_338_; 
v_k_x27_337_ = lean_array_fget_borrowed(v_ks_325_, v_x_322_);
v___x_338_ = l_Lean_instBEqMVarId_beq(v_x_323_, v_k_x27_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_340_; 
if (v_isShared_329_ == 0)
{
v___x_340_ = v___x_328_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_ks_325_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_vs_326_);
v___x_340_ = v_reuseFailAlloc_344_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = lean_nat_add(v_x_322_, v___x_341_);
lean_dec(v_x_322_);
v_x_321_ = v___x_340_;
v_x_322_ = v___x_342_;
goto _start;
}
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_345_ = lean_array_fset(v_ks_325_, v_x_322_, v_x_323_);
v___x_346_ = lean_array_fset(v_vs_326_, v_x_322_, v_x_324_);
lean_dec(v_x_322_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_346_);
lean_ctor_set(v___x_328_, 0, v___x_345_);
v___x_348_ = v___x_328_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_n_351_, lean_object* v_k_352_, lean_object* v_v_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_n_351_, v___x_354_, v_k_352_, v_v_353_);
return v___x_355_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_356_; size_t v___x_357_; size_t v___x_358_; 
v___x_356_ = ((size_t)5ULL);
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_shift_left(v___x_357_, v___x_356_);
return v___x_358_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_359_; size_t v___x_360_; size_t v___x_361_; 
v___x_359_ = ((size_t)1ULL);
v___x_360_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_361_ = lean_usize_sub(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_363_, size_t v_x_364_, size_t v_x_365_, lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
if (lean_obj_tag(v_x_363_) == 0)
{
lean_object* v_es_368_; size_t v___x_369_; size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; lean_object* v_j_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v_es_368_ = lean_ctor_get(v_x_363_, 0);
v___x_369_ = ((size_t)5ULL);
v___x_370_ = ((size_t)1ULL);
v___x_371_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_372_ = lean_usize_land(v_x_364_, v___x_371_);
v_j_373_ = lean_usize_to_nat(v___x_372_);
v___x_374_ = lean_array_get_size(v_es_368_);
v___x_375_ = lean_nat_dec_lt(v_j_373_, v___x_374_);
if (v___x_375_ == 0)
{
lean_dec(v_j_373_);
lean_dec(v_x_367_);
lean_dec(v_x_366_);
return v_x_363_;
}
else
{
lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_412_; 
lean_inc_ref(v_es_368_);
v_isSharedCheck_412_ = !lean_is_exclusive(v_x_363_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v_x_363_, 0);
lean_dec(v_unused_413_);
v___x_377_ = v_x_363_;
v_isShared_378_ = v_isSharedCheck_412_;
goto v_resetjp_376_;
}
else
{
lean_dec(v_x_363_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_412_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v_v_379_; lean_object* v___x_380_; lean_object* v_xs_x27_381_; lean_object* v___y_383_; 
v_v_379_ = lean_array_fget(v_es_368_, v_j_373_);
v___x_380_ = lean_box(0);
v_xs_x27_381_ = lean_array_fset(v_es_368_, v_j_373_, v___x_380_);
switch(lean_obj_tag(v_v_379_))
{
case 0:
{
lean_object* v_key_388_; lean_object* v_val_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_399_; 
v_key_388_ = lean_ctor_get(v_v_379_, 0);
v_val_389_ = lean_ctor_get(v_v_379_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v_v_379_);
if (v_isSharedCheck_399_ == 0)
{
v___x_391_ = v_v_379_;
v_isShared_392_ = v_isSharedCheck_399_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_val_389_);
lean_inc(v_key_388_);
lean_dec(v_v_379_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_399_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
uint8_t v___x_393_; 
v___x_393_ = l_Lean_instBEqMVarId_beq(v_x_366_, v_key_388_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_del_object(v___x_391_);
v___x_394_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_388_, v_val_389_, v_x_366_, v_x_367_);
v___x_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
v___y_383_ = v___x_395_;
goto v___jp_382_;
}
else
{
lean_object* v___x_397_; 
lean_dec(v_val_389_);
lean_dec(v_key_388_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 1, v_x_367_);
lean_ctor_set(v___x_391_, 0, v_x_366_);
v___x_397_ = v___x_391_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_x_366_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_x_367_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
v___y_383_ = v___x_397_;
goto v___jp_382_;
}
}
}
}
case 1:
{
lean_object* v_node_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_410_; 
v_node_400_ = lean_ctor_get(v_v_379_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v_v_379_);
if (v_isSharedCheck_410_ == 0)
{
v___x_402_ = v_v_379_;
v_isShared_403_ = v_isSharedCheck_410_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_node_400_);
lean_dec(v_v_379_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_410_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
size_t v___x_404_; size_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_404_ = lean_usize_shift_right(v_x_364_, v___x_369_);
v___x_405_ = lean_usize_add(v_x_365_, v___x_370_);
v___x_406_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_node_400_, v___x_404_, v___x_405_, v_x_366_, v_x_367_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_406_);
v___x_408_ = v___x_402_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
v___y_383_ = v___x_408_;
goto v___jp_382_;
}
}
}
default: 
{
lean_object* v___x_411_; 
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v_x_366_);
lean_ctor_set(v___x_411_, 1, v_x_367_);
v___y_383_ = v___x_411_;
goto v___jp_382_;
}
}
v___jp_382_:
{
lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_384_ = lean_array_fset(v_xs_x27_381_, v_j_373_, v___y_383_);
lean_dec(v_j_373_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_384_);
v___x_386_ = v___x_377_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
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
}
else
{
lean_object* v_ks_414_; lean_object* v_vs_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_435_; 
v_ks_414_ = lean_ctor_get(v_x_363_, 0);
v_vs_415_ = lean_ctor_get(v_x_363_, 1);
v_isSharedCheck_435_ = !lean_is_exclusive(v_x_363_);
if (v_isSharedCheck_435_ == 0)
{
v___x_417_ = v_x_363_;
v_isShared_418_ = v_isSharedCheck_435_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_vs_415_);
lean_inc(v_ks_414_);
lean_dec(v_x_363_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_435_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_ks_414_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_vs_415_);
v___x_420_ = v_reuseFailAlloc_434_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v_newNode_421_; uint8_t v___y_423_; size_t v___x_429_; uint8_t v___x_430_; 
v_newNode_421_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(v___x_420_, v_x_366_, v_x_367_);
v___x_429_ = ((size_t)7ULL);
v___x_430_ = lean_usize_dec_le(v___x_429_, v_x_365_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_431_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_421_);
v___x_432_ = lean_unsigned_to_nat(4u);
v___x_433_ = lean_nat_dec_lt(v___x_431_, v___x_432_);
lean_dec(v___x_431_);
v___y_423_ = v___x_433_;
goto v___jp_422_;
}
else
{
v___y_423_ = v___x_430_;
goto v___jp_422_;
}
v___jp_422_:
{
if (v___y_423_ == 0)
{
lean_object* v_ks_424_; lean_object* v_vs_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_ks_424_ = lean_ctor_get(v_newNode_421_, 0);
lean_inc_ref(v_ks_424_);
v_vs_425_ = lean_ctor_get(v_newNode_421_, 1);
lean_inc_ref(v_vs_425_);
lean_dec_ref(v_newNode_421_);
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_428_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_365_, v_ks_424_, v_vs_425_, v___x_426_, v___x_427_);
lean_dec_ref(v_vs_425_);
lean_dec_ref(v_ks_424_);
return v___x_428_;
}
else
{
return v_newNode_421_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(size_t v_depth_436_, lean_object* v_keys_437_, lean_object* v_vals_438_, lean_object* v_i_439_, lean_object* v_entries_440_){
_start:
{
lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_441_ = lean_array_get_size(v_keys_437_);
v___x_442_ = lean_nat_dec_lt(v_i_439_, v___x_441_);
if (v___x_442_ == 0)
{
lean_dec(v_i_439_);
return v_entries_440_;
}
else
{
lean_object* v_k_443_; lean_object* v_v_444_; uint64_t v___x_445_; size_t v_h_446_; size_t v___x_447_; lean_object* v___x_448_; size_t v___x_449_; size_t v___x_450_; size_t v___x_451_; size_t v_h_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v_k_443_ = lean_array_fget_borrowed(v_keys_437_, v_i_439_);
v_v_444_ = lean_array_fget_borrowed(v_vals_438_, v_i_439_);
v___x_445_ = l_Lean_instHashableMVarId_hash(v_k_443_);
v_h_446_ = lean_uint64_to_usize(v___x_445_);
v___x_447_ = ((size_t)5ULL);
v___x_448_ = lean_unsigned_to_nat(1u);
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_sub(v_depth_436_, v___x_449_);
v___x_451_ = lean_usize_mul(v___x_447_, v___x_450_);
v_h_452_ = lean_usize_shift_right(v_h_446_, v___x_451_);
v___x_453_ = lean_nat_add(v_i_439_, v___x_448_);
lean_dec(v_i_439_);
lean_inc(v_v_444_);
lean_inc(v_k_443_);
v___x_454_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_entries_440_, v_h_452_, v_depth_436_, v_k_443_, v_v_444_);
v_i_439_ = v___x_453_;
v_entries_440_ = v___x_454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_depth_456_, lean_object* v_keys_457_, lean_object* v_vals_458_, lean_object* v_i_459_, lean_object* v_entries_460_){
_start:
{
size_t v_depth_boxed_461_; lean_object* v_res_462_; 
v_depth_boxed_461_ = lean_unbox_usize(v_depth_456_);
lean_dec(v_depth_456_);
v_res_462_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_boxed_461_, v_keys_457_, v_vals_458_, v_i_459_, v_entries_460_);
lean_dec_ref(v_vals_458_);
lean_dec_ref(v_keys_457_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_463_, lean_object* v_x_464_, lean_object* v_x_465_, lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
size_t v_x_5924__boxed_468_; size_t v_x_5925__boxed_469_; lean_object* v_res_470_; 
v_x_5924__boxed_468_ = lean_unbox_usize(v_x_464_);
lean_dec(v_x_464_);
v_x_5925__boxed_469_ = lean_unbox_usize(v_x_465_);
lean_dec(v_x_465_);
v_res_470_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_463_, v_x_5924__boxed_468_, v_x_5925__boxed_469_, v_x_466_, v_x_467_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(lean_object* v_x_471_, lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
uint64_t v___x_474_; size_t v___x_475_; size_t v___x_476_; lean_object* v___x_477_; 
v___x_474_ = l_Lean_instHashableMVarId_hash(v_x_472_);
v___x_475_ = lean_uint64_to_usize(v___x_474_);
v___x_476_ = ((size_t)1ULL);
v___x_477_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_471_, v___x_475_, v___x_476_, v_x_472_, v_x_473_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(lean_object* v_mvarId_478_, lean_object* v_val_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___x_482_; lean_object* v_mctx_483_; lean_object* v_cache_484_; lean_object* v_zetaDeltaFVarIds_485_; lean_object* v_postponed_486_; lean_object* v_diag_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_515_; 
v___x_482_ = lean_st_ref_take(v___y_480_);
v_mctx_483_ = lean_ctor_get(v___x_482_, 0);
v_cache_484_ = lean_ctor_get(v___x_482_, 1);
v_zetaDeltaFVarIds_485_ = lean_ctor_get(v___x_482_, 2);
v_postponed_486_ = lean_ctor_get(v___x_482_, 3);
v_diag_487_ = lean_ctor_get(v___x_482_, 4);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_515_ == 0)
{
v___x_489_ = v___x_482_;
v_isShared_490_ = v_isSharedCheck_515_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_diag_487_);
lean_inc(v_postponed_486_);
lean_inc(v_zetaDeltaFVarIds_485_);
lean_inc(v_cache_484_);
lean_inc(v_mctx_483_);
lean_dec(v___x_482_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_515_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v_depth_491_; lean_object* v_levelAssignDepth_492_; lean_object* v_lmvarCounter_493_; lean_object* v_mvarCounter_494_; lean_object* v_lDecls_495_; lean_object* v_decls_496_; lean_object* v_userNames_497_; lean_object* v_lAssignment_498_; lean_object* v_eAssignment_499_; lean_object* v_dAssignment_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_514_; 
v_depth_491_ = lean_ctor_get(v_mctx_483_, 0);
v_levelAssignDepth_492_ = lean_ctor_get(v_mctx_483_, 1);
v_lmvarCounter_493_ = lean_ctor_get(v_mctx_483_, 2);
v_mvarCounter_494_ = lean_ctor_get(v_mctx_483_, 3);
v_lDecls_495_ = lean_ctor_get(v_mctx_483_, 4);
v_decls_496_ = lean_ctor_get(v_mctx_483_, 5);
v_userNames_497_ = lean_ctor_get(v_mctx_483_, 6);
v_lAssignment_498_ = lean_ctor_get(v_mctx_483_, 7);
v_eAssignment_499_ = lean_ctor_get(v_mctx_483_, 8);
v_dAssignment_500_ = lean_ctor_get(v_mctx_483_, 9);
v_isSharedCheck_514_ = !lean_is_exclusive(v_mctx_483_);
if (v_isSharedCheck_514_ == 0)
{
v___x_502_ = v_mctx_483_;
v_isShared_503_ = v_isSharedCheck_514_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_dAssignment_500_);
lean_inc(v_eAssignment_499_);
lean_inc(v_lAssignment_498_);
lean_inc(v_userNames_497_);
lean_inc(v_decls_496_);
lean_inc(v_lDecls_495_);
lean_inc(v_mvarCounter_494_);
lean_inc(v_lmvarCounter_493_);
lean_inc(v_levelAssignDepth_492_);
lean_inc(v_depth_491_);
lean_dec(v_mctx_483_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_514_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_eAssignment_499_, v_mvarId_478_, v_val_479_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 8, v___x_504_);
v___x_506_ = v___x_502_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_depth_491_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_levelAssignDepth_492_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_lmvarCounter_493_);
lean_ctor_set(v_reuseFailAlloc_513_, 3, v_mvarCounter_494_);
lean_ctor_set(v_reuseFailAlloc_513_, 4, v_lDecls_495_);
lean_ctor_set(v_reuseFailAlloc_513_, 5, v_decls_496_);
lean_ctor_set(v_reuseFailAlloc_513_, 6, v_userNames_497_);
lean_ctor_set(v_reuseFailAlloc_513_, 7, v_lAssignment_498_);
lean_ctor_set(v_reuseFailAlloc_513_, 8, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_513_, 9, v_dAssignment_500_);
v___x_506_ = v_reuseFailAlloc_513_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_508_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_506_);
v___x_508_ = v___x_489_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_cache_484_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_zetaDeltaFVarIds_485_);
lean_ctor_set(v_reuseFailAlloc_512_, 3, v_postponed_486_);
lean_ctor_set(v_reuseFailAlloc_512_, 4, v_diag_487_);
v___x_508_ = v_reuseFailAlloc_512_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_st_ref_set(v___y_480_, v___x_508_);
v___x_510_ = lean_box(0);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg___boxed(lean_object* v_mvarId_516_, lean_object* v_val_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_516_, v_val_517_, v___y_518_);
lean_dec(v___y_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(lean_object* v_mvarId_521_, lean_object* v_fvars_522_, lean_object* v_mvarIdPending_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___x_526_; lean_object* v_mctx_527_; lean_object* v_cache_528_; lean_object* v_zetaDeltaFVarIds_529_; lean_object* v_postponed_530_; lean_object* v_diag_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_560_; 
v___x_526_ = lean_st_ref_take(v___y_524_);
v_mctx_527_ = lean_ctor_get(v___x_526_, 0);
v_cache_528_ = lean_ctor_get(v___x_526_, 1);
v_zetaDeltaFVarIds_529_ = lean_ctor_get(v___x_526_, 2);
v_postponed_530_ = lean_ctor_get(v___x_526_, 3);
v_diag_531_ = lean_ctor_get(v___x_526_, 4);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_560_ == 0)
{
v___x_533_ = v___x_526_;
v_isShared_534_ = v_isSharedCheck_560_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_diag_531_);
lean_inc(v_postponed_530_);
lean_inc(v_zetaDeltaFVarIds_529_);
lean_inc(v_cache_528_);
lean_inc(v_mctx_527_);
lean_dec(v___x_526_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_560_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v_depth_535_; lean_object* v_levelAssignDepth_536_; lean_object* v_lmvarCounter_537_; lean_object* v_mvarCounter_538_; lean_object* v_lDecls_539_; lean_object* v_decls_540_; lean_object* v_userNames_541_; lean_object* v_lAssignment_542_; lean_object* v_eAssignment_543_; lean_object* v_dAssignment_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_559_; 
v_depth_535_ = lean_ctor_get(v_mctx_527_, 0);
v_levelAssignDepth_536_ = lean_ctor_get(v_mctx_527_, 1);
v_lmvarCounter_537_ = lean_ctor_get(v_mctx_527_, 2);
v_mvarCounter_538_ = lean_ctor_get(v_mctx_527_, 3);
v_lDecls_539_ = lean_ctor_get(v_mctx_527_, 4);
v_decls_540_ = lean_ctor_get(v_mctx_527_, 5);
v_userNames_541_ = lean_ctor_get(v_mctx_527_, 6);
v_lAssignment_542_ = lean_ctor_get(v_mctx_527_, 7);
v_eAssignment_543_ = lean_ctor_get(v_mctx_527_, 8);
v_dAssignment_544_ = lean_ctor_get(v_mctx_527_, 9);
v_isSharedCheck_559_ = !lean_is_exclusive(v_mctx_527_);
if (v_isSharedCheck_559_ == 0)
{
v___x_546_ = v_mctx_527_;
v_isShared_547_ = v_isSharedCheck_559_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_dAssignment_544_);
lean_inc(v_eAssignment_543_);
lean_inc(v_lAssignment_542_);
lean_inc(v_userNames_541_);
lean_inc(v_decls_540_);
lean_inc(v_lDecls_539_);
lean_inc(v_mvarCounter_538_);
lean_inc(v_lmvarCounter_537_);
lean_inc(v_levelAssignDepth_536_);
lean_inc(v_depth_535_);
lean_dec(v_mctx_527_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_559_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v_fvars_522_);
lean_ctor_set(v___x_548_, 1, v_mvarIdPending_523_);
v___x_549_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_dAssignment_544_, v_mvarId_521_, v___x_548_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 9, v___x_549_);
v___x_551_ = v___x_546_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_depth_535_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_levelAssignDepth_536_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_lmvarCounter_537_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_mvarCounter_538_);
lean_ctor_set(v_reuseFailAlloc_558_, 4, v_lDecls_539_);
lean_ctor_set(v_reuseFailAlloc_558_, 5, v_decls_540_);
lean_ctor_set(v_reuseFailAlloc_558_, 6, v_userNames_541_);
lean_ctor_set(v_reuseFailAlloc_558_, 7, v_lAssignment_542_);
lean_ctor_set(v_reuseFailAlloc_558_, 8, v_eAssignment_543_);
lean_ctor_set(v_reuseFailAlloc_558_, 9, v___x_549_);
v___x_551_ = v_reuseFailAlloc_558_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_553_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_551_);
v___x_553_ = v___x_533_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_cache_528_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_zetaDeltaFVarIds_529_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v_postponed_530_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v_diag_531_);
v___x_553_ = v_reuseFailAlloc_557_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_st_ref_set(v___y_524_, v___x_553_);
v___x_555_ = lean_box(0);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg___boxed(lean_object* v_mvarId_561_, lean_object* v_fvars_562_, lean_object* v_mvarIdPending_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_561_, v_fvars_562_, v_mvarIdPending_563_, v___y_564_);
lean_dec(v___y_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(lean_object* v___x_567_, lean_object* v_userName_568_, lean_object* v_lctx_569_, lean_object* v_localInstances_570_, lean_object* v_type_571_, lean_object* v_max_572_, lean_object* v_mvarId_573_, lean_object* v_lctx_574_, lean_object* v_localInsts_575_, lean_object* v_fvars_576_, lean_object* v_type_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_585_ = lean_array_get_size(v_fvars_576_);
v___x_586_ = lean_nat_dec_eq(v___x_585_, v___x_567_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_type_577_, v___x_567_, v___x_585_, v_fvars_576_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; uint8_t v___x_589_; lean_object* v___x_590_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref(v___x_587_);
v___x_589_ = 2;
lean_inc(v___x_567_);
v___x_590_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_574_, v_localInsts_575_, v_a_588_, v___x_589_, v_userName_568_, v___x_567_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref(v___x_590_);
v___x_592_ = lean_box(0);
lean_inc(v___x_567_);
lean_inc_ref(v_type_571_);
v___x_593_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_569_, v_localInstances_570_, v_type_571_, v___x_589_, v___x_592_, v___x_567_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_595_; lean_object* v___y_597_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref(v___x_593_);
v___x_595_ = l_Lean_Expr_mvarId_x21(v_a_591_);
lean_dec(v_a_591_);
v___x_607_ = l_Lean_Expr_mvarId_x21(v_a_594_);
lean_inc(v___x_595_);
lean_inc_ref(v_fvars_576_);
v___x_608_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v___x_607_, v_fvars_576_, v___x_595_, v___y_581_);
lean_dec_ref(v___x_608_);
v___x_609_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkAppBVars(v_a_594_, v___x_585_);
v___x_610_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(v_max_572_, v___x_567_, v_type_571_, v___x_609_);
lean_dec_ref(v___x_609_);
lean_dec(v___x_567_);
v___x_611_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_573_, v___x_610_, v___y_581_);
v___y_597_ = v___x_611_;
goto v___jp_596_;
v___jp_596_:
{
lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_605_; 
v_isSharedCheck_605_ = !lean_is_exclusive(v___y_597_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v___y_597_, 0);
lean_dec(v_unused_606_);
v___x_599_ = v___y_597_;
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
else
{
lean_dec(v___y_597_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v_fvars_576_);
lean_ctor_set(v___x_601_, 1, v___x_595_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_601_);
v___x_603_ = v___x_599_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec(v_a_591_);
lean_dec_ref(v_fvars_576_);
lean_dec(v_mvarId_573_);
lean_dec_ref(v_type_571_);
lean_dec(v___x_567_);
v_a_612_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_593_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_593_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec_ref(v_fvars_576_);
lean_dec(v_mvarId_573_);
lean_dec_ref(v_type_571_);
lean_dec_ref(v_localInstances_570_);
lean_dec_ref(v_lctx_569_);
lean_dec(v___x_567_);
v_a_620_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_590_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_590_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
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
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v_fvars_576_);
lean_dec_ref(v_localInsts_575_);
lean_dec_ref(v_lctx_574_);
lean_dec(v_mvarId_573_);
lean_dec_ref(v_type_571_);
lean_dec_ref(v_localInstances_570_);
lean_dec_ref(v_lctx_569_);
lean_dec(v_userName_568_);
lean_dec(v___x_567_);
v_a_628_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_587_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_587_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec_ref(v_type_577_);
lean_dec_ref(v_fvars_576_);
lean_dec_ref(v_localInsts_575_);
lean_dec_ref(v_lctx_574_);
lean_dec_ref(v_type_571_);
lean_dec_ref(v_localInstances_570_);
lean_dec_ref(v_lctx_569_);
lean_dec(v_userName_568_);
v___x_636_ = lean_mk_empty_array_with_capacity(v___x_567_);
lean_dec(v___x_567_);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v_mvarId_573_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed(lean_object** _args){
lean_object* v___x_639_ = _args[0];
lean_object* v_userName_640_ = _args[1];
lean_object* v_lctx_641_ = _args[2];
lean_object* v_localInstances_642_ = _args[3];
lean_object* v_type_643_ = _args[4];
lean_object* v_max_644_ = _args[5];
lean_object* v_mvarId_645_ = _args[6];
lean_object* v_lctx_646_ = _args[7];
lean_object* v_localInsts_647_ = _args[8];
lean_object* v_fvars_648_ = _args[9];
lean_object* v_type_649_ = _args[10];
lean_object* v___y_650_ = _args[11];
lean_object* v___y_651_ = _args[12];
lean_object* v___y_652_ = _args[13];
lean_object* v___y_653_ = _args[14];
lean_object* v___y_654_ = _args[15];
lean_object* v___y_655_ = _args[16];
lean_object* v___y_656_ = _args[17];
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(v___x_639_, v_userName_640_, v_lctx_641_, v_localInstances_642_, v_type_643_, v_max_644_, v_mvarId_645_, v_lctx_646_, v_localInsts_647_, v_fvars_648_, v_type_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v_max_644_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(lean_object* v_env_658_, lean_object* v_localInsts_659_, lean_object* v_fvar_660_, lean_object* v_type_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Meta_Sym_isClass_x3f(v_env_658_, v_type_661_);
if (lean_obj_tag(v___x_662_) == 1)
{
lean_object* v_val_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_val_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_val_663_);
lean_dec_ref(v___x_662_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v_val_663_);
lean_ctor_set(v___x_664_, 1, v_fvar_660_);
v___x_665_ = lean_array_push(v_localInsts_659_, v___x_664_);
return v___x_665_;
}
else
{
lean_dec(v___x_662_);
lean_dec_ref(v_fvar_660_);
return v_localInsts_659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(size_t v_sz_666_, size_t v_i_667_, lean_object* v_bs_668_){
_start:
{
uint8_t v___x_669_; 
v___x_669_ = lean_usize_dec_lt(v_i_667_, v_sz_666_);
if (v___x_669_ == 0)
{
return v_bs_668_;
}
else
{
lean_object* v_v_670_; lean_object* v___x_671_; lean_object* v_bs_x27_672_; lean_object* v___x_673_; size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
v_v_670_ = lean_array_uget(v_bs_668_, v_i_667_);
v___x_671_ = lean_unsigned_to_nat(0u);
v_bs_x27_672_ = lean_array_uset(v_bs_668_, v_i_667_, v___x_671_);
v___x_673_ = l_Lean_Expr_fvarId_x21(v_v_670_);
lean_dec(v_v_670_);
v___x_674_ = ((size_t)1ULL);
v___x_675_ = lean_usize_add(v_i_667_, v___x_674_);
v___x_676_ = lean_array_uset(v_bs_x27_672_, v_i_667_, v___x_673_);
v_i_667_ = v___x_675_;
v_bs_668_ = v___x_676_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2___boxed(lean_object* v_sz_678_, lean_object* v_i_679_, lean_object* v_bs_680_){
_start:
{
size_t v_sz_boxed_681_; size_t v_i_boxed_682_; lean_object* v_res_683_; 
v_sz_boxed_681_ = lean_unbox_usize(v_sz_678_);
lean_dec(v_sz_678_);
v_i_boxed_682_ = lean_unbox_usize(v_i_679_);
lean_dec(v_i_679_);
v_res_683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_boxed_681_, v_i_boxed_682_, v_bs_680_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(lean_object* v_mvarId_688_, lean_object* v_max_689_, lean_object* v_names_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_nat_dec_eq(v_max_689_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_st_ref_get(v_a_696_);
lean_inc(v_mvarId_688_);
v___x_701_ = l_Lean_MVarId_getDecl(v_mvarId_688_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v_env_703_; lean_object* v_userName_704_; lean_object* v_lctx_705_; lean_object* v_type_706_; lean_object* v_localInstances_707_; lean_object* v___f_708_; lean_object* v___f_709_; lean_object* v___f_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref(v___x_701_);
v_env_703_ = lean_ctor_get(v___x_700_, 0);
lean_inc_ref(v_env_703_);
lean_dec(v___x_700_);
v_userName_704_ = lean_ctor_get(v_a_702_, 0);
lean_inc(v_userName_704_);
v_lctx_705_ = lean_ctor_get(v_a_702_, 1);
lean_inc_ref_n(v_lctx_705_, 2);
v_type_706_ = lean_ctor_get(v_a_702_, 2);
lean_inc_ref_n(v_type_706_, 2);
v_localInstances_707_ = lean_ctor_get(v_a_702_, 4);
lean_inc_ref_n(v_localInstances_707_, 2);
lean_dec(v_a_702_);
v___f_708_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed), 8, 1);
lean_closure_set(v___f_708_, 0, v_names_690_);
lean_inc(v_max_689_);
v___f_709_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed), 18, 7);
lean_closure_set(v___f_709_, 0, v___x_698_);
lean_closure_set(v___f_709_, 1, v_userName_704_);
lean_closure_set(v___f_709_, 2, v_lctx_705_);
lean_closure_set(v___f_709_, 3, v_localInstances_707_);
lean_closure_set(v___f_709_, 4, v_type_706_);
lean_closure_set(v___f_709_, 5, v_max_689_);
lean_closure_set(v___f_709_, 6, v_mvarId_688_);
v___f_710_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2), 4, 1);
lean_closure_set(v___f_710_, 0, v_env_703_);
v___x_711_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0));
v___x_712_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(v_max_689_, v___f_709_, v___f_708_, v___f_710_, v___x_698_, v_lctx_705_, v_localInstances_707_, v___x_711_, v_type_706_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
lean_dec(v_max_689_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_732_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_732_ == 0)
{
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_732_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_732_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v_fst_717_; lean_object* v_snd_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_731_; 
v_fst_717_ = lean_ctor_get(v_a_713_, 0);
v_snd_718_ = lean_ctor_get(v_a_713_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v_a_713_);
if (v_isSharedCheck_731_ == 0)
{
v___x_720_ = v_a_713_;
v_isShared_721_ = v_isSharedCheck_731_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_snd_718_);
lean_inc(v_fst_717_);
lean_dec(v_a_713_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_731_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
size_t v_sz_722_; size_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
v_sz_722_ = lean_array_size(v_fst_717_);
v___x_723_ = ((size_t)0ULL);
v___x_724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_722_, v___x_723_, v_fst_717_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_724_);
v___x_726_ = v___x_720_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_snd_718_);
v___x_726_ = v_reuseFailAlloc_730_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_728_; 
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_726_);
v___x_728_ = v___x_715_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
v_a_733_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_712_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_712_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v___x_700_);
lean_dec_ref(v_names_690_);
lean_dec(v_max_689_);
lean_dec(v_mvarId_688_);
v_a_741_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_701_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_701_);
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
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec_ref(v_names_690_);
lean_dec(v_max_689_);
v___x_749_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v_mvarId_688_);
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___boxed(lean_object* v_mvarId_752_, lean_object* v_max_753_, lean_object* v_names_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_752_, v_max_753_, v_names_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(lean_object* v_mvarId_763_, lean_object* v_fvars_764_, lean_object* v_mvarIdPending_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_763_, v_fvars_764_, v_mvarIdPending_765_, v___y_767_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___boxed(lean_object* v_mvarId_772_, lean_object* v_fvars_773_, lean_object* v_mvarIdPending_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(v_mvarId_772_, v_fvars_773_, v_mvarIdPending_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(lean_object* v_mvarId_781_, lean_object* v_val_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_781_, v_val_782_, v___y_784_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___boxed(lean_object* v_mvarId_789_, lean_object* v_val_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(v_mvarId_789_, v_val_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0(lean_object* v_00_u03b2_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_x_798_, v_x_799_, v_x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_802_, lean_object* v_x_803_, size_t v_x_804_, size_t v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_803_, v_x_804_, v_x_805_, v_x_806_, v_x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
size_t v_x_6501__boxed_815_; size_t v_x_6502__boxed_816_; lean_object* v_res_817_; 
v_x_6501__boxed_815_ = lean_unbox_usize(v_x_811_);
lean_dec(v_x_811_);
v_x_6502__boxed_816_ = lean_unbox_usize(v_x_812_);
lean_dec(v_x_812_);
v_res_817_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(v_00_u03b2_809_, v_x_810_, v_x_6501__boxed_815_, v_x_6502__boxed_816_, v_x_813_, v_x_814_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_818_, lean_object* v_n_819_, lean_object* v_k_820_, lean_object* v_v_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(v_n_819_, v_k_820_, v_v_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_823_, size_t v_depth_824_, lean_object* v_keys_825_, lean_object* v_vals_826_, lean_object* v_heq_827_, lean_object* v_i_828_, lean_object* v_entries_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_824_, v_keys_825_, v_vals_826_, v_i_828_, v_entries_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_831_, lean_object* v_depth_832_, lean_object* v_keys_833_, lean_object* v_vals_834_, lean_object* v_heq_835_, lean_object* v_i_836_, lean_object* v_entries_837_){
_start:
{
size_t v_depth_boxed_838_; lean_object* v_res_839_; 
v_depth_boxed_838_ = lean_unbox_usize(v_depth_832_);
lean_dec(v_depth_832_);
v_res_839_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_831_, v_depth_boxed_838_, v_keys_833_, v_vals_834_, v_heq_835_, v_i_836_, v_entries_837_);
lean_dec_ref(v_vals_834_);
lean_dec_ref(v_keys_833_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_x_841_, v_x_842_, v_x_843_, v_x_844_);
return v___x_845_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat(void){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = lean_unsigned_to_nat(1000000u);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx(lean_object* v_x_847_){
_start:
{
if (lean_obj_tag(v_x_847_) == 0)
{
lean_object* v___x_848_; 
v___x_848_ = lean_unsigned_to_nat(0u);
return v___x_848_;
}
else
{
lean_object* v___x_849_; 
v___x_849_ = lean_unsigned_to_nat(1u);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorIdx___boxed(lean_object* v_x_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_Meta_Sym_IntrosResult_ctorIdx(v_x_850_);
lean_dec(v_x_850_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(lean_object* v_t_852_, lean_object* v_k_853_){
_start:
{
if (lean_obj_tag(v_t_852_) == 0)
{
return v_k_853_;
}
else
{
lean_object* v_newDecls_854_; lean_object* v_mvarId_855_; lean_object* v___x_856_; 
v_newDecls_854_ = lean_ctor_get(v_t_852_, 0);
lean_inc_ref(v_newDecls_854_);
v_mvarId_855_ = lean_ctor_get(v_t_852_, 1);
lean_inc(v_mvarId_855_);
lean_dec_ref(v_t_852_);
v___x_856_ = lean_apply_2(v_k_853_, v_newDecls_854_, v_mvarId_855_);
return v___x_856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim(lean_object* v_motive_857_, lean_object* v_ctorIdx_858_, lean_object* v_t_859_, lean_object* v_h_860_, lean_object* v_k_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_859_, v_k_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_ctorElim___boxed(lean_object* v_motive_863_, lean_object* v_ctorIdx_864_, lean_object* v_t_865_, lean_object* v_h_866_, lean_object* v_k_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Meta_Sym_IntrosResult_ctorElim(v_motive_863_, v_ctorIdx_864_, v_t_865_, v_h_866_, v_k_867_);
lean_dec(v_ctorIdx_864_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim___redArg(lean_object* v_t_869_, lean_object* v_failed_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_869_, v_failed_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_failed_elim(lean_object* v_motive_872_, lean_object* v_t_873_, lean_object* v_h_874_, lean_object* v_failed_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_873_, v_failed_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim___redArg(lean_object* v_t_877_, lean_object* v_goal_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_877_, v_goal_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_IntrosResult_goal_elim(lean_object* v_motive_880_, lean_object* v_t_881_, lean_object* v_h_882_, lean_object* v_goal_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_881_, v_goal_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros(lean_object* v_mvarId_885_, lean_object* v_names_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_result_895_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_911_ = lean_array_get_size(v_names_886_);
v___x_912_ = lean_unsigned_to_nat(0u);
v___x_913_ = lean_nat_dec_eq(v___x_911_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; 
v___x_914_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_885_, v___x_911_, v_names_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref(v___x_914_);
v_result_895_ = v_a_915_;
goto v___jp_894_;
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
v_a_916_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_914_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_914_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec_ref(v_names_886_);
v___x_924_ = lean_unsigned_to_nat(1000000u);
v___x_925_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
v___x_926_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_885_, v___x_924_, v___x_925_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref(v___x_926_);
v_result_895_ = v_a_927_;
goto v___jp_894_;
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
v_a_928_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_926_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_926_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
v___jp_894_:
{
lean_object* v_fst_896_; lean_object* v_snd_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_910_; 
v_fst_896_ = lean_ctor_get(v_result_895_, 0);
v_snd_897_ = lean_ctor_get(v_result_895_, 1);
v_isSharedCheck_910_ = !lean_is_exclusive(v_result_895_);
if (v_isSharedCheck_910_ == 0)
{
v___x_899_ = v_result_895_;
v_isShared_900_ = v_isSharedCheck_910_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_snd_897_);
lean_inc(v_fst_896_);
lean_dec(v_result_895_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_910_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_901_ = lean_array_get_size(v_fst_896_);
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = lean_nat_dec_eq(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_905_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set_tag(v___x_899_, 1);
v___x_905_ = v___x_899_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_fst_896_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_snd_897_);
v___x_905_ = v_reuseFailAlloc_907_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_906_; 
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
return v___x_906_;
}
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; 
lean_del_object(v___x_899_);
lean_dec(v_snd_897_);
lean_dec(v_fst_896_);
v___x_908_ = lean_box(0);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_intros___boxed(lean_object* v_mvarId_936_, lean_object* v_names_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Meta_Sym_intros(v_mvarId_936_, v_names_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN(lean_object* v_mvarId_946_, lean_object* v_num_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1));
lean_inc(v_num_947_);
v___x_956_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(v_mvarId_946_, v_num_947_, v___x_955_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_979_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_979_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_979_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_979_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_fst_961_; lean_object* v_snd_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_978_; 
v_fst_961_ = lean_ctor_get(v_a_957_, 0);
v_snd_962_ = lean_ctor_get(v_a_957_, 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v_a_957_);
if (v_isSharedCheck_978_ == 0)
{
v___x_964_ = v_a_957_;
v_isShared_965_ = v_isSharedCheck_978_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_snd_962_);
lean_inc(v_fst_961_);
lean_dec(v_a_957_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_978_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_966_ = lean_array_get_size(v_fst_961_);
v___x_967_ = lean_nat_dec_eq(v___x_966_, v_num_947_);
lean_dec(v_num_947_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_970_; 
lean_del_object(v___x_964_);
lean_dec(v_snd_962_);
lean_dec(v_fst_961_);
v___x_968_ = lean_box(0);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_968_);
v___x_970_ = v___x_959_;
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
else
{
lean_object* v___x_973_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 1);
v___x_973_ = v___x_964_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_fst_961_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_snd_962_);
v___x_973_ = v_reuseFailAlloc_977_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_975_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_973_);
v___x_975_ = v___x_959_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v_num_947_);
v_a_980_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_956_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_956_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_introN___boxed(lean_object* v_mvarId_988_, lean_object* v_num_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Meta_Sym_introN(v_mvarId_988_, v_num_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
return v_res_997_;
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
