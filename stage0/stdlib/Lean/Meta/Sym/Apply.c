// Lean compiler output
// Module: Lean.Meta.Sym.Apply
// Imports: public import Lean.Meta.Sym.Pattern import Lean.Util.CollectFVars import Init.Data.Range.Polymorphic.Iterators
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
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Pattern_unify_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkPatternFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_CollectFVars_State_ofFVarSet(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_mkPatternFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_sym_pre"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 124, 57, 118, 127, 154, 73, 9)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1;
static const lean_ctor_object l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0_value),((lean_object*)&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_mkBackwardRuleFromExpr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_failed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_failed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_goals_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_goals_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "rule is not applicable to goal"};
static const lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1;
static const lean_string_object l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rule:"};
static const lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(size_t v_sz_1_, size_t v_i_2_, lean_object* v_bs_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = lean_usize_dec_lt(v_i_2_, v_sz_1_);
if (v___x_4_ == 0)
{
return v_bs_3_;
}
else
{
lean_object* v_v_5_; uint8_t v_isInstance_6_; lean_object* v___x_7_; lean_object* v_bs_x27_8_; size_t v___x_9_; size_t v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_v_5_ = lean_array_uget_borrowed(v_bs_3_, v_i_2_);
v_isInstance_6_ = lean_ctor_get_uint8(v_v_5_, 1);
v___x_7_ = lean_unsigned_to_nat(0u);
v_bs_x27_8_ = lean_array_uset(v_bs_3_, v_i_2_, v___x_7_);
v___x_9_ = ((size_t)1ULL);
v___x_10_ = lean_usize_add(v_i_2_, v___x_9_);
v___x_11_ = lean_box(v_isInstance_6_);
v___x_12_ = lean_array_uset(v_bs_x27_8_, v_i_2_, v___x_11_);
v_i_2_ = v___x_10_;
v_bs_3_ = v___x_12_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5___boxed(lean_object* v_sz_14_, lean_object* v_i_15_, lean_object* v_bs_16_){
_start:
{
size_t v_sz_boxed_17_; size_t v_i_boxed_18_; lean_object* v_res_19_; 
v_sz_boxed_17_ = lean_unbox_usize(v_sz_14_);
lean_dec(v_sz_14_);
v_i_boxed_18_ = lean_unbox_usize(v_i_15_);
lean_dec(v_i_15_);
v_res_19_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(v_sz_boxed_17_, v_i_boxed_18_, v_bs_16_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(lean_object* v_as_23_, size_t v_sz_24_, size_t v_i_25_, lean_object* v_b_26_){
_start:
{
lean_object* v_a_28_; uint8_t v___x_32_; 
v___x_32_ = lean_usize_dec_lt(v_i_25_, v_sz_24_);
if (v___x_32_ == 0)
{
return v_b_26_;
}
else
{
lean_object* v_a_33_; 
v_a_33_ = lean_array_uget_borrowed(v_as_23_, v_i_25_);
if (lean_obj_tag(v_a_33_) == 2)
{
lean_object* v_pre_34_; lean_object* v_i_35_; lean_object* v_auxPrefix_36_; uint8_t v___x_37_; 
v_pre_34_ = lean_ctor_get(v_a_33_, 0);
v_i_35_ = lean_ctor_get(v_a_33_, 1);
v_auxPrefix_36_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1));
v___x_37_ = lean_name_eq(v_pre_34_, v_auxPrefix_36_);
if (v___x_37_ == 0)
{
v_a_28_ = v_b_26_;
goto v___jp_27_;
}
else
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_box(v___x_37_);
v___x_39_ = lean_array_set(v_b_26_, v_i_35_, v___x_38_);
v_a_28_ = v___x_39_;
goto v___jp_27_;
}
}
else
{
v_a_28_ = v_b_26_;
goto v___jp_27_;
}
}
v___jp_27_:
{
size_t v___x_29_; size_t v___x_30_; 
v___x_29_ = ((size_t)1ULL);
v___x_30_ = lean_usize_add(v_i_25_, v___x_29_);
v_i_25_ = v___x_30_;
v_b_26_ = v_a_28_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___boxed(lean_object* v_as_40_, lean_object* v_sz_41_, lean_object* v_i_42_, lean_object* v_b_43_){
_start:
{
size_t v_sz_boxed_44_; size_t v_i_boxed_45_; lean_object* v_res_46_; 
v_sz_boxed_44_ = lean_unbox_usize(v_sz_41_);
lean_dec(v_sz_41_);
v_i_boxed_45_ = lean_unbox_usize(v_i_42_);
lean_dec(v_i_42_);
v_res_46_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(v_as_40_, v_sz_boxed_44_, v_i_boxed_45_, v_b_43_);
lean_dec_ref(v_as_40_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(lean_object* v_auxVars_47_, size_t v_sz_48_, size_t v_i_49_, lean_object* v_bs_50_){
_start:
{
uint8_t v___x_51_; 
v___x_51_ = lean_usize_dec_lt(v_i_49_, v_sz_48_);
if (v___x_51_ == 0)
{
return v_bs_50_;
}
else
{
lean_object* v_v_52_; lean_object* v___x_53_; lean_object* v_bs_x27_54_; lean_object* v___x_55_; lean_object* v___x_56_; size_t v___x_57_; size_t v___x_58_; lean_object* v___x_59_; 
v_v_52_ = lean_array_uget(v_bs_50_, v_i_49_);
v___x_53_ = lean_unsigned_to_nat(0u);
v_bs_x27_54_ = lean_array_uset(v_bs_50_, v_i_49_, v___x_53_);
v___x_55_ = lean_usize_to_nat(v_i_49_);
v___x_56_ = lean_expr_instantiate_rev_range(v_v_52_, v___x_53_, v___x_55_, v_auxVars_47_);
lean_dec(v___x_55_);
lean_dec(v_v_52_);
v___x_57_ = ((size_t)1ULL);
v___x_58_ = lean_usize_add(v_i_49_, v___x_57_);
v___x_59_ = lean_array_uset(v_bs_x27_54_, v_i_49_, v___x_56_);
v_i_49_ = v___x_58_;
v_bs_50_ = v___x_59_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg___boxed(lean_object* v_auxVars_61_, lean_object* v_sz_62_, lean_object* v_i_63_, lean_object* v_bs_64_){
_start:
{
size_t v_sz_boxed_65_; size_t v_i_boxed_66_; lean_object* v_res_67_; 
v_sz_boxed_65_ = lean_unbox_usize(v_sz_62_);
lean_dec(v_sz_62_);
v_i_boxed_66_ = lean_unbox_usize(v_i_63_);
lean_dec(v_i_63_);
v_res_67_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_61_, v_sz_boxed_65_, v_i_boxed_66_, v_bs_64_);
lean_dec_ref(v_auxVars_61_);
return v_res_67_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(lean_object* v_upperBound_68_, lean_object* v___x_69_, lean_object* v___x_70_, lean_object* v___x_71_, lean_object* v_next_72_, lean_object* v_upperBound_73_, lean_object* v_a_74_, uint8_t v_b_75_){
_start:
{
uint8_t v_a_77_; uint8_t v___x_81_; 
v___x_81_ = lean_nat_dec_lt(v_a_74_, v_upperBound_68_);
if (v___x_81_ == 0)
{
lean_dec(v_a_74_);
return v_b_75_;
}
else
{
uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_82_ = 0;
v___x_83_ = lean_box(v___x_82_);
v___x_84_ = lean_array_get(v___x_83_, v___x_69_, v_a_74_);
lean_dec(v___x_83_);
v___x_85_ = lean_unbox(v___x_84_);
lean_dec(v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_86_ = l_Lean_instInhabitedExpr;
v___x_87_ = lean_array_get_borrowed(v___x_86_, v___x_70_, v_a_74_);
v___x_88_ = l_Lean_Expr_fvarId_x21(v___x_71_);
v___x_89_ = l_Lean_Expr_containsFVar(v___x_87_, v___x_88_);
lean_dec(v___x_88_);
if (v___x_89_ == 0)
{
v_a_77_ = v_b_75_;
goto v___jp_76_;
}
else
{
uint8_t v___x_90_; 
lean_dec(v_a_74_);
v___x_90_ = lean_nat_dec_lt(v_next_72_, v_upperBound_73_);
return v___x_90_;
}
}
else
{
v_a_77_ = v_b_75_;
goto v___jp_76_;
}
}
v___jp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_add(v_a_74_, v___x_78_);
lean_dec(v_a_74_);
v_a_74_ = v___x_79_;
v_b_75_ = v_a_77_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg___boxed(lean_object* v_upperBound_91_, lean_object* v___x_92_, lean_object* v___x_93_, lean_object* v___x_94_, lean_object* v_next_95_, lean_object* v_upperBound_96_, lean_object* v_a_97_, lean_object* v_b_98_){
_start:
{
uint8_t v_b_boxed_99_; uint8_t v_res_100_; lean_object* v_r_101_; 
v_b_boxed_99_ = lean_unbox(v_b_98_);
v_res_100_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_upperBound_91_, v___x_92_, v___x_93_, v___x_94_, v_next_95_, v_upperBound_96_, v_a_97_, v_b_boxed_99_);
lean_dec(v_upperBound_96_);
lean_dec(v_next_95_);
lean_dec_ref(v___x_94_);
lean_dec_ref(v___x_93_);
lean_dec_ref(v___x_92_);
lean_dec(v_upperBound_91_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(lean_object* v_upperBound_102_, lean_object* v___x_103_, lean_object* v_numArgs_104_, lean_object* v_auxVars_105_, lean_object* v___x_106_, lean_object* v_a_107_, lean_object* v_b_108_){
_start:
{
lean_object* v_a_110_; uint8_t v___x_114_; 
v___x_114_ = lean_nat_dec_lt(v_a_107_, v_upperBound_102_);
if (v___x_114_ == 0)
{
lean_dec(v_a_107_);
return v_b_108_;
}
else
{
lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_141_; 
v_fst_115_ = lean_ctor_get(v_b_108_, 0);
v_snd_116_ = lean_ctor_get(v_b_108_, 1);
v_isSharedCheck_141_ = !lean_is_exclusive(v_b_108_);
if (v_isSharedCheck_141_ == 0)
{
v___x_118_ = v_b_108_;
v_isShared_119_ = v_isSharedCheck_141_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_snd_116_);
lean_inc(v_fst_115_);
lean_dec(v_b_108_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_141_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_120_ = 0;
v___x_121_ = lean_box(v___x_120_);
v___x_122_ = lean_array_get(v___x_121_, v___x_103_, v_a_107_);
lean_dec(v___x_121_);
v___x_123_ = lean_unbox(v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; uint8_t v___x_129_; 
v___x_124_ = l_Lean_instInhabitedExpr;
v___x_125_ = lean_unsigned_to_nat(1u);
v___x_126_ = lean_nat_add(v_a_107_, v___x_125_);
v___x_127_ = lean_array_get_borrowed(v___x_124_, v_auxVars_105_, v_a_107_);
v___x_128_ = lean_unbox(v___x_122_);
lean_dec(v___x_122_);
v___x_129_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_numArgs_104_, v___x_103_, v___x_106_, v___x_127_, v_a_107_, v_upperBound_102_, v___x_126_, v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_132_; 
lean_inc(v_a_107_);
v___x_130_ = lean_array_push(v_snd_116_, v_a_107_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v___x_130_);
v___x_132_ = v___x_118_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_fst_115_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
v_a_110_ = v___x_132_;
goto v___jp_109_;
}
}
else
{
lean_object* v___x_134_; lean_object* v___x_136_; 
lean_inc(v_a_107_);
v___x_134_ = lean_array_push(v_fst_115_, v_a_107_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_134_);
v___x_136_ = v___x_118_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_snd_116_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
v_a_110_ = v___x_136_;
goto v___jp_109_;
}
}
}
else
{
lean_object* v___x_139_; 
lean_dec(v___x_122_);
if (v_isShared_119_ == 0)
{
v___x_139_ = v___x_118_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_fst_115_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_snd_116_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
v_a_110_ = v___x_139_;
goto v___jp_109_;
}
}
}
}
v___jp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = lean_nat_add(v_a_107_, v___x_111_);
lean_dec(v_a_107_);
v_a_107_ = v___x_112_;
v_b_108_ = v_a_110_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg___boxed(lean_object* v_upperBound_142_, lean_object* v___x_143_, lean_object* v_numArgs_144_, lean_object* v_auxVars_145_, lean_object* v___x_146_, lean_object* v_a_147_, lean_object* v_b_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_upperBound_142_, v___x_143_, v_numArgs_144_, v_auxVars_145_, v___x_146_, v_a_147_, v_b_148_);
lean_dec_ref(v___x_146_);
lean_dec_ref(v_auxVars_145_);
lean_dec(v_numArgs_144_);
lean_dec_ref(v___x_143_);
lean_dec(v_upperBound_142_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(size_t v_sz_150_, size_t v_i_151_, lean_object* v_bs_152_){
_start:
{
uint8_t v___x_153_; 
v___x_153_ = lean_usize_dec_lt(v_i_151_, v_sz_150_);
if (v___x_153_ == 0)
{
return v_bs_152_;
}
else
{
lean_object* v_auxPrefix_154_; lean_object* v___x_155_; lean_object* v_bs_x27_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; size_t v___x_160_; size_t v___x_161_; lean_object* v___x_162_; 
v_auxPrefix_154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1));
v___x_155_ = lean_unsigned_to_nat(0u);
v_bs_x27_156_ = lean_array_uset(v_bs_152_, v_i_151_, v___x_155_);
v___x_157_ = lean_usize_to_nat(v_i_151_);
v___x_158_ = l_Lean_Name_num___override(v_auxPrefix_154_, v___x_157_);
v___x_159_ = l_Lean_mkFVar(v___x_158_);
v___x_160_ = ((size_t)1ULL);
v___x_161_ = lean_usize_add(v_i_151_, v___x_160_);
v___x_162_ = lean_array_uset(v_bs_x27_156_, v_i_151_, v___x_159_);
v_i_151_ = v___x_161_;
v_bs_152_ = v___x_162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg___boxed(lean_object* v_sz_164_, lean_object* v_i_165_, lean_object* v_bs_166_){
_start:
{
size_t v_sz_boxed_167_; size_t v_i_boxed_168_; lean_object* v_res_169_; 
v_sz_boxed_167_ = lean_unbox_usize(v_sz_164_);
lean_dec(v_sz_164_);
v_i_boxed_168_ = lean_unbox_usize(v_i_165_);
lean_dec(v_i_165_);
v_res_169_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(v_sz_boxed_167_, v_i_boxed_168_, v_bs_166_);
return v_res_169_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = ((lean_object*)(l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0));
v___x_173_ = lean_box(1);
v___x_174_ = l_Lean_CollectFVars_State_ofFVarSet(v___x_173_, v___x_172_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(lean_object* v_pattern_177_){
_start:
{
lean_object* v_varTypes_178_; lean_object* v_varInfos_x3f_179_; lean_object* v_pattern_180_; lean_object* v_numArgs_181_; lean_object* v___y_183_; 
v_varTypes_178_ = lean_ctor_get(v_pattern_177_, 1);
lean_inc_ref(v_varTypes_178_);
v_varInfos_x3f_179_ = lean_ctor_get(v_pattern_177_, 2);
lean_inc(v_varInfos_x3f_179_);
v_pattern_180_ = lean_ctor_get(v_pattern_177_, 3);
lean_inc_ref(v_pattern_180_);
lean_dec_ref(v_pattern_177_);
v_numArgs_181_ = lean_array_get_size(v_varTypes_178_);
if (lean_obj_tag(v_varInfos_x3f_179_) == 1)
{
lean_object* v_val_201_; size_t v_sz_202_; size_t v___x_203_; lean_object* v___x_204_; 
v_val_201_ = lean_ctor_get(v_varInfos_x3f_179_, 0);
lean_inc(v_val_201_);
lean_dec_ref_known(v_varInfos_x3f_179_, 1);
v_sz_202_ = lean_array_size(v_val_201_);
v___x_203_ = ((size_t)0ULL);
v___x_204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(v_sz_202_, v___x_203_, v_val_201_);
v___y_183_ = v___x_204_;
goto v___jp_182_;
}
else
{
uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec(v_varInfos_x3f_179_);
v___x_205_ = 0;
v___x_206_ = lean_box(v___x_205_);
v___x_207_ = lean_mk_array(v_numArgs_181_, v___x_206_);
v___y_183_ = v___x_207_;
goto v___jp_182_;
}
v___jp_182_:
{
size_t v_sz_184_; size_t v___x_185_; lean_object* v_auxVars_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v_fvarIds_191_; size_t v_sz_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v_fst_197_; lean_object* v_snd_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_sz_184_ = lean_array_size(v_varTypes_178_);
v___x_185_ = ((size_t)0ULL);
lean_inc_ref(v_varTypes_178_);
v_auxVars_186_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(v_sz_184_, v___x_185_, v_varTypes_178_);
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = lean_obj_once(&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1, &l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1_once, _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1);
v___x_189_ = lean_expr_instantiate_rev(v_pattern_180_, v_auxVars_186_);
lean_dec_ref(v_pattern_180_);
v___x_190_ = l_Lean_collectFVars(v___x_188_, v___x_189_);
v_fvarIds_191_ = lean_ctor_get(v___x_190_, 2);
lean_inc_ref(v_fvarIds_191_);
lean_dec_ref(v___x_190_);
v_sz_192_ = lean_array_size(v_fvarIds_191_);
v___x_193_ = ((lean_object*)(l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2));
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(v_fvarIds_191_, v_sz_192_, v___x_185_, v___y_183_);
lean_dec_ref(v_fvarIds_191_);
v___x_195_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_186_, v_sz_184_, v___x_185_, v_varTypes_178_);
v___x_196_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_numArgs_181_, v___x_194_, v_numArgs_181_, v_auxVars_186_, v___x_195_, v___x_187_, v___x_193_);
lean_dec_ref(v___x_195_);
lean_dec_ref(v_auxVars_186_);
lean_dec_ref(v___x_194_);
v_fst_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_fst_197_);
v_snd_198_ = lean_ctor_get(v___x_196_, 1);
lean_inc(v_snd_198_);
lean_dec_ref(v___x_196_);
v___x_199_ = l_Array_append___redArg(v_snd_198_, v_fst_197_);
lean_dec(v_fst_197_);
v___x_200_ = lean_array_to_list(v___x_199_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0(lean_object* v_as_208_, size_t v_sz_209_, size_t v_i_210_, lean_object* v_bs_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(v_sz_209_, v_i_210_, v_bs_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___boxed(lean_object* v_as_213_, lean_object* v_sz_214_, lean_object* v_i_215_, lean_object* v_bs_216_){
_start:
{
size_t v_sz_boxed_217_; size_t v_i_boxed_218_; lean_object* v_res_219_; 
v_sz_boxed_217_ = lean_unbox_usize(v_sz_214_);
lean_dec(v_sz_214_);
v_i_boxed_218_ = lean_unbox_usize(v_i_215_);
lean_dec(v_i_215_);
v_res_219_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0(v_as_213_, v_sz_boxed_217_, v_i_boxed_218_, v_bs_216_);
lean_dec_ref(v_as_213_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2(lean_object* v_auxVars_220_, lean_object* v_as_221_, size_t v_sz_222_, size_t v_i_223_, lean_object* v_bs_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_220_, v_sz_222_, v_i_223_, v_bs_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___boxed(lean_object* v_auxVars_226_, lean_object* v_as_227_, lean_object* v_sz_228_, lean_object* v_i_229_, lean_object* v_bs_230_){
_start:
{
size_t v_sz_boxed_231_; size_t v_i_boxed_232_; lean_object* v_res_233_; 
v_sz_boxed_231_ = lean_unbox_usize(v_sz_228_);
lean_dec(v_sz_228_);
v_i_boxed_232_ = lean_unbox_usize(v_i_229_);
lean_dec(v_i_229_);
v_res_233_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2(v_auxVars_226_, v_as_227_, v_sz_boxed_231_, v_i_boxed_232_, v_bs_230_);
lean_dec_ref(v_as_227_);
lean_dec_ref(v_auxVars_226_);
return v_res_233_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3(lean_object* v_upperBound_234_, lean_object* v___x_235_, lean_object* v___x_236_, lean_object* v___x_237_, lean_object* v_next_238_, lean_object* v_upperBound_239_, lean_object* v_inst_240_, lean_object* v_R_241_, lean_object* v_a_242_, uint8_t v_b_243_, lean_object* v_c_244_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_upperBound_234_, v___x_235_, v___x_236_, v___x_237_, v_next_238_, v_upperBound_239_, v_a_242_, v_b_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___boxed(lean_object* v_upperBound_246_, lean_object* v___x_247_, lean_object* v___x_248_, lean_object* v___x_249_, lean_object* v_next_250_, lean_object* v_upperBound_251_, lean_object* v_inst_252_, lean_object* v_R_253_, lean_object* v_a_254_, lean_object* v_b_255_, lean_object* v_c_256_){
_start:
{
uint8_t v_b_boxed_257_; uint8_t v_res_258_; lean_object* v_r_259_; 
v_b_boxed_257_ = lean_unbox(v_b_255_);
v_res_258_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3(v_upperBound_246_, v___x_247_, v___x_248_, v___x_249_, v_next_250_, v_upperBound_251_, v_inst_252_, v_R_253_, v_a_254_, v_b_boxed_257_, v_c_256_);
lean_dec(v_upperBound_251_);
lean_dec(v_next_250_);
lean_dec_ref(v___x_249_);
lean_dec_ref(v___x_248_);
lean_dec_ref(v___x_247_);
lean_dec(v_upperBound_246_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4(lean_object* v_upperBound_260_, lean_object* v___x_261_, lean_object* v_numArgs_262_, lean_object* v_auxVars_263_, lean_object* v___x_264_, lean_object* v_inst_265_, lean_object* v_R_266_, lean_object* v_a_267_, lean_object* v_b_268_, lean_object* v_c_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_upperBound_260_, v___x_261_, v_numArgs_262_, v_auxVars_263_, v___x_264_, v_a_267_, v_b_268_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___boxed(lean_object* v_upperBound_271_, lean_object* v___x_272_, lean_object* v_numArgs_273_, lean_object* v_auxVars_274_, lean_object* v___x_275_, lean_object* v_inst_276_, lean_object* v_R_277_, lean_object* v_a_278_, lean_object* v_b_279_, lean_object* v_c_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4(v_upperBound_271_, v___x_272_, v_numArgs_273_, v_auxVars_274_, v___x_275_, v_inst_276_, v_R_277_, v_a_278_, v_b_279_, v_c_280_);
lean_dec_ref(v___x_275_);
lean_dec_ref(v_auxVars_274_);
lean_dec(v_numArgs_273_);
lean_dec_ref(v___x_272_);
lean_dec(v_upperBound_271_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object* v_declName_282_, lean_object* v_num_x3f_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_289_; 
lean_inc(v_declName_282_);
v___x_289_ = l_Lean_Meta_Sym_mkPatternFromDecl(v_declName_282_, v_num_x3f_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_301_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_301_ == 0)
{
v___x_292_ = v___x_289_;
v_isShared_293_ = v_isSharedCheck_301_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_301_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
lean_inc(v_a_290_);
v___x_294_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(v_a_290_);
v___x_295_ = lean_box(0);
v___x_296_ = l_Lean_mkConst(v_declName_282_, v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_a_290_);
lean_ctor_set(v___x_297_, 2, v___x_294_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_297_);
v___x_299_ = v___x_292_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec(v_declName_282_);
v_a_302_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_289_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_289_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl___boxed(lean_object* v_declName_310_, lean_object* v_num_x3f_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v_declName_310_, v_num_x3f_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_num_x3f_311_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_mkBackwardRuleFromExpr_spec__0(lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
if (lean_obj_tag(v_a_318_) == 0)
{
lean_object* v___x_320_; 
v___x_320_ = l_List_reverse___redArg(v_a_319_);
return v___x_320_;
}
else
{
lean_object* v_head_321_; lean_object* v_tail_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_331_; 
v_head_321_ = lean_ctor_get(v_a_318_, 0);
v_tail_322_ = lean_ctor_get(v_a_318_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v_a_318_);
if (v_isSharedCheck_331_ == 0)
{
v___x_324_ = v_a_318_;
v_isShared_325_ = v_isSharedCheck_331_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_tail_322_);
lean_inc(v_head_321_);
lean_dec(v_a_318_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_331_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_326_ = l_Lean_mkLevelParam(v_head_321_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 1, v_a_319_);
lean_ctor_set(v___x_324_, 0, v___x_326_);
v___x_328_ = v___x_324_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_a_319_);
v___x_328_ = v_reuseFailAlloc_330_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
v_a_318_ = v_tail_322_;
v_a_319_ = v___x_328_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr(lean_object* v_e_332_, lean_object* v_levelParams_333_, lean_object* v_num_x3f_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___x_340_; 
lean_inc_ref(v_e_332_);
v___x_340_ = l_Lean_Meta_Sym_mkPatternFromExpr(v_e_332_, v_levelParams_333_, v_num_x3f_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_354_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_354_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_354_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_354_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v_levelParams_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
v_levelParams_345_ = lean_ctor_get(v_a_341_, 0);
lean_inc(v_a_341_);
v___x_346_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(v_a_341_);
v___x_347_ = lean_box(0);
lean_inc(v_levelParams_345_);
v___x_348_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_mkBackwardRuleFromExpr_spec__0(v_levelParams_345_, v___x_347_);
v___x_349_ = l_Lean_Expr_instantiateLevelParams(v_e_332_, v_levelParams_333_, v___x_348_);
lean_dec(v___x_348_);
lean_dec_ref(v_e_332_);
v___x_350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v_a_341_);
lean_ctor_set(v___x_350_, 2, v___x_346_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_350_);
v___x_352_ = v___x_343_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec_ref(v_e_332_);
v_a_355_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_340_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_340_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr___boxed(lean_object* v_e_363_, lean_object* v_levelParams_364_, lean_object* v_num_x3f_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_e_363_, v_levelParams_364_, v_num_x3f_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_num_x3f_365_);
lean_dec(v_levelParams_364_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(lean_object* v_expr_372_, lean_object* v_pattern_373_, lean_object* v_result_374_){
_start:
{
if (lean_obj_tag(v_expr_372_) == 4)
{
lean_object* v_us_381_; 
v_us_381_ = lean_ctor_get(v_expr_372_, 1);
if (lean_obj_tag(v_us_381_) == 0)
{
lean_object* v_declName_382_; lean_object* v_us_383_; lean_object* v_args_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v_declName_382_ = lean_ctor_get(v_expr_372_, 0);
lean_inc(v_declName_382_);
lean_dec_ref_known(v_expr_372_, 2);
v_us_383_ = lean_ctor_get(v_result_374_, 0);
lean_inc(v_us_383_);
v_args_384_ = lean_ctor_get(v_result_374_, 1);
lean_inc_ref(v_args_384_);
lean_dec_ref(v_result_374_);
v___x_385_ = l_Lean_mkConst(v_declName_382_, v_us_383_);
v___x_386_ = l_Lean_mkAppN(v___x_385_, v_args_384_);
lean_dec_ref(v_args_384_);
return v___x_386_;
}
else
{
goto v___jp_375_;
}
}
else
{
goto v___jp_375_;
}
v___jp_375_:
{
lean_object* v_levelParams_376_; lean_object* v_us_377_; lean_object* v_args_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_levelParams_376_ = lean_ctor_get(v_pattern_373_, 0);
v_us_377_ = lean_ctor_get(v_result_374_, 0);
lean_inc(v_us_377_);
v_args_378_ = lean_ctor_get(v_result_374_, 1);
lean_inc_ref(v_args_378_);
lean_dec_ref(v_result_374_);
v___x_379_ = l_Lean_Expr_instantiateLevelParams(v_expr_372_, v_levelParams_376_, v_us_377_);
lean_dec(v_us_377_);
lean_dec_ref(v_expr_372_);
v___x_380_ = l_Lean_mkAppN(v___x_379_, v_args_378_);
lean_dec_ref(v_args_378_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue___boxed(lean_object* v_expr_387_, lean_object* v_pattern_388_, lean_object* v_result_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(v_expr_387_, v_pattern_388_, v_result_389_);
lean_dec_ref(v_pattern_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx___impl(lean_object* v_x_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_obj_tag_nat(v_x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx___impl___boxed(lean_object* v_x_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Meta_Sym_ApplyResult_ctorIdx___impl(v_x_393_);
lean_dec(v_x_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(lean_object* v_t_395_, lean_object* v_k_396_){
_start:
{
if (lean_obj_tag(v_t_395_) == 0)
{
return v_k_396_;
}
else
{
lean_object* v_mvarIds_397_; lean_object* v___x_398_; 
v_mvarIds_397_ = lean_ctor_get(v_t_395_, 0);
lean_inc(v_mvarIds_397_);
lean_dec_ref_known(v_t_395_, 1);
v___x_398_ = lean_apply_1(v_k_396_, v_mvarIds_397_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim(lean_object* v_motive_399_, lean_object* v_ctorIdx_400_, lean_object* v_t_401_, lean_object* v_h_402_, lean_object* v_k_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_401_, v_k_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim___boxed(lean_object* v_motive_405_, lean_object* v_ctorIdx_406_, lean_object* v_t_407_, lean_object* v_h_408_, lean_object* v_k_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Meta_Sym_ApplyResult_ctorElim(v_motive_405_, v_ctorIdx_406_, v_t_407_, v_h_408_, v_k_409_);
lean_dec(v_ctorIdx_406_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_failed_elim___redArg(lean_object* v_t_411_, lean_object* v_failed_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_411_, v_failed_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_failed_elim(lean_object* v_motive_414_, lean_object* v_t_415_, lean_object* v_h_416_, lean_object* v_failed_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_415_, v_failed_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_goals_elim___redArg(lean_object* v_t_419_, lean_object* v_goals_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_419_, v_goals_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_goals_elim(lean_object* v_motive_422_, lean_object* v_t_423_, lean_object* v_h_424_, lean_object* v_goals_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_423_, v_goals_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(lean_object* v_x_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
lean_inc(v___y_429_);
lean_inc_ref(v___y_428_);
v___x_435_ = lean_apply_7(v_x_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, lean_box(0));
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0___boxed(lean_object* v_x_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(v_x_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(lean_object* v_mvarId_445_, lean_object* v_x_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v___f_454_; lean_object* v___x_455_; 
lean_inc(v___y_448_);
lean_inc_ref(v___y_447_);
v___f_454_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_454_, 0, v_x_446_);
lean_closure_set(v___f_454_, 1, v___y_447_);
lean_closure_set(v___f_454_, 2, v___y_448_);
v___x_455_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_445_, v___f_454_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
if (lean_obj_tag(v___x_455_) == 0)
{
return v___x_455_;
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___boxed(lean_object* v_mvarId_464_, lean_object* v_x_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_464_, v_x_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(lean_object* v_00_u03b1_474_, lean_object* v_mvarId_475_, lean_object* v_x_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_475_, v_x_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___boxed(lean_object* v_00_u03b1_485_, lean_object* v_mvarId_486_, lean_object* v_x_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(v_00_u03b1_485_, v_mvarId_486_, v_x_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(lean_object* v_val_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
if (lean_obj_tag(v_a_497_) == 0)
{
lean_object* v___x_499_; 
v___x_499_ = l_List_reverse___redArg(v_a_498_);
return v___x_499_;
}
else
{
lean_object* v_head_500_; lean_object* v_tail_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_513_; 
v_head_500_ = lean_ctor_get(v_a_497_, 0);
v_tail_501_ = lean_ctor_get(v_a_497_, 1);
v_isSharedCheck_513_ = !lean_is_exclusive(v_a_497_);
if (v_isSharedCheck_513_ == 0)
{
v___x_503_ = v_a_497_;
v_isShared_504_ = v_isSharedCheck_513_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_tail_501_);
lean_inc(v_head_500_);
lean_dec(v_a_497_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_513_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v_args_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v_args_505_ = lean_ctor_get(v_val_496_, 1);
v___x_506_ = l_Lean_instInhabitedExpr;
v___x_507_ = lean_array_get_borrowed(v___x_506_, v_args_505_, v_head_500_);
lean_dec(v_head_500_);
v___x_508_ = l_Lean_Expr_mvarId_x21(v___x_507_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v_a_498_);
lean_ctor_set(v___x_503_, 0, v___x_508_);
v___x_510_ = v___x_503_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_a_498_);
v___x_510_ = v_reuseFailAlloc_512_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
v_a_497_ = v_tail_501_;
v_a_498_ = v___x_510_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1___boxed(lean_object* v_val_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(v_val_514_, v_a_515_, v_a_516_);
lean_dec_ref(v_val_514_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v_x_521_){
_start:
{
lean_object* v_ks_522_; lean_object* v_vs_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_547_; 
v_ks_522_ = lean_ctor_get(v_x_518_, 0);
v_vs_523_ = lean_ctor_get(v_x_518_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_x_518_);
if (v_isSharedCheck_547_ == 0)
{
v___x_525_ = v_x_518_;
v_isShared_526_ = v_isSharedCheck_547_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_vs_523_);
lean_inc(v_ks_522_);
lean_dec(v_x_518_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_547_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_array_get_size(v_ks_522_);
v___x_528_ = lean_nat_dec_lt(v_x_519_, v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
lean_dec(v_x_519_);
v___x_529_ = lean_array_push(v_ks_522_, v_x_520_);
v___x_530_ = lean_array_push(v_vs_523_, v_x_521_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v___x_530_);
lean_ctor_set(v___x_525_, 0, v___x_529_);
v___x_532_ = v___x_525_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
else
{
lean_object* v_k_x27_534_; uint8_t v___x_535_; 
v_k_x27_534_ = lean_array_fget_borrowed(v_ks_522_, v_x_519_);
v___x_535_ = l_Lean_instBEqMVarId_beq(v_x_520_, v_k_x27_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_537_; 
if (v_isShared_526_ == 0)
{
v___x_537_ = v___x_525_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_ks_522_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_vs_523_);
v___x_537_ = v_reuseFailAlloc_541_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_nat_add(v_x_519_, v___x_538_);
lean_dec(v_x_519_);
v_x_518_ = v___x_537_;
v_x_519_ = v___x_539_;
goto _start;
}
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_542_ = lean_array_fset(v_ks_522_, v_x_519_, v_x_520_);
v___x_543_ = lean_array_fset(v_vs_523_, v_x_519_, v_x_521_);
lean_dec(v_x_519_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v___x_543_);
lean_ctor_set(v___x_525_, 0, v___x_542_);
v___x_545_ = v___x_525_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_n_548_, lean_object* v_k_549_, lean_object* v_v_550_){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_548_, v___x_551_, v_k_549_, v_v_550_);
return v___x_552_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(lean_object* v_x_554_, size_t v_x_555_, size_t v_x_556_, lean_object* v_x_557_, lean_object* v_x_558_){
_start:
{
if (lean_obj_tag(v_x_554_) == 0)
{
lean_object* v_es_559_; size_t v___x_560_; size_t v___x_561_; lean_object* v_j_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_es_559_ = lean_ctor_get(v_x_554_, 0);
v___x_560_ = ((size_t)31ULL);
v___x_561_ = lean_usize_land(v_x_555_, v___x_560_);
v_j_562_ = lean_usize_to_nat(v___x_561_);
v___x_563_ = lean_array_get_size(v_es_559_);
v___x_564_ = lean_nat_dec_lt(v_j_562_, v___x_563_);
if (v___x_564_ == 0)
{
lean_dec(v_j_562_);
lean_dec(v_x_558_);
lean_dec(v_x_557_);
return v_x_554_;
}
else
{
lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_603_; 
lean_inc_ref(v_es_559_);
v_isSharedCheck_603_ = !lean_is_exclusive(v_x_554_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v_x_554_, 0);
lean_dec(v_unused_604_);
v___x_566_ = v_x_554_;
v_isShared_567_ = v_isSharedCheck_603_;
goto v_resetjp_565_;
}
else
{
lean_dec(v_x_554_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_603_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v_v_568_; lean_object* v___x_569_; lean_object* v_xs_x27_570_; lean_object* v___y_572_; 
v_v_568_ = lean_array_fget(v_es_559_, v_j_562_);
v___x_569_ = lean_box(0);
v_xs_x27_570_ = lean_array_fset(v_es_559_, v_j_562_, v___x_569_);
switch(lean_obj_tag(v_v_568_))
{
case 0:
{
lean_object* v_key_577_; lean_object* v_val_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_588_; 
v_key_577_ = lean_ctor_get(v_v_568_, 0);
v_val_578_ = lean_ctor_get(v_v_568_, 1);
v_isSharedCheck_588_ = !lean_is_exclusive(v_v_568_);
if (v_isSharedCheck_588_ == 0)
{
v___x_580_ = v_v_568_;
v_isShared_581_ = v_isSharedCheck_588_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_val_578_);
lean_inc(v_key_577_);
lean_dec(v_v_568_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_588_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
uint8_t v___x_582_; 
v___x_582_ = l_Lean_instBEqMVarId_beq(v_x_557_, v_key_577_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_del_object(v___x_580_);
v___x_583_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_577_, v_val_578_, v_x_557_, v_x_558_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
v___y_572_ = v___x_584_;
goto v___jp_571_;
}
else
{
lean_object* v___x_586_; 
lean_dec(v_val_578_);
lean_dec(v_key_577_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v_x_558_);
lean_ctor_set(v___x_580_, 0, v_x_557_);
v___x_586_ = v___x_580_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_x_557_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_x_558_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
v___y_572_ = v___x_586_;
goto v___jp_571_;
}
}
}
}
case 1:
{
lean_object* v_node_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_601_; 
v_node_589_ = lean_ctor_get(v_v_568_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v_v_568_);
if (v_isSharedCheck_601_ == 0)
{
v___x_591_ = v_v_568_;
v_isShared_592_ = v_isSharedCheck_601_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_node_589_);
lean_dec(v_v_568_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_601_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
size_t v___x_593_; size_t v___x_594_; size_t v___x_595_; size_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_593_ = ((size_t)5ULL);
v___x_594_ = lean_usize_shift_right(v_x_555_, v___x_593_);
v___x_595_ = ((size_t)1ULL);
v___x_596_ = lean_usize_add(v_x_556_, v___x_595_);
v___x_597_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_node_589_, v___x_594_, v___x_596_, v_x_557_, v_x_558_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_597_);
v___x_599_ = v___x_591_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
v___y_572_ = v___x_599_;
goto v___jp_571_;
}
}
}
default: 
{
lean_object* v___x_602_; 
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v_x_557_);
lean_ctor_set(v___x_602_, 1, v_x_558_);
v___y_572_ = v___x_602_;
goto v___jp_571_;
}
}
v___jp_571_:
{
lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_573_ = lean_array_fset(v_xs_x27_570_, v_j_562_, v___y_572_);
lean_dec(v_j_562_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_573_);
v___x_575_ = v___x_566_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
else
{
lean_object* v_ks_605_; lean_object* v_vs_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_624_; 
v_ks_605_ = lean_ctor_get(v_x_554_, 0);
v_vs_606_ = lean_ctor_get(v_x_554_, 1);
v_isSharedCheck_624_ = !lean_is_exclusive(v_x_554_);
if (v_isSharedCheck_624_ == 0)
{
v___x_608_ = v_x_554_;
v_isShared_609_ = v_isSharedCheck_624_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_vs_606_);
lean_inc(v_ks_605_);
lean_dec(v_x_554_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_624_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_ks_605_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_vs_606_);
v___x_611_ = v_reuseFailAlloc_623_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v_newNode_612_; size_t v___x_613_; uint8_t v___x_614_; 
v_newNode_612_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(v___x_611_, v_x_557_, v_x_558_);
v___x_613_ = ((size_t)7ULL);
v___x_614_ = lean_usize_dec_le(v___x_613_, v_x_556_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_615_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_612_);
v___x_616_ = lean_unsigned_to_nat(4u);
v___x_617_ = lean_nat_dec_lt(v___x_615_, v___x_616_);
lean_dec(v___x_615_);
if (v___x_617_ == 0)
{
lean_object* v_ks_618_; lean_object* v_vs_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_ks_618_ = lean_ctor_get(v_newNode_612_, 0);
lean_inc_ref(v_ks_618_);
v_vs_619_ = lean_ctor_get(v_newNode_612_, 1);
lean_inc_ref(v_vs_619_);
lean_dec_ref(v_newNode_612_);
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_622_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_x_556_, v_ks_618_, v_vs_619_, v___x_620_, v___x_621_);
lean_dec_ref(v_vs_619_);
lean_dec_ref(v_ks_618_);
return v___x_622_;
}
else
{
return v_newNode_612_;
}
}
else
{
return v_newNode_612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_625_, lean_object* v_keys_626_, lean_object* v_vals_627_, lean_object* v_i_628_, lean_object* v_entries_629_){
_start:
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_array_get_size(v_keys_626_);
v___x_631_ = lean_nat_dec_lt(v_i_628_, v___x_630_);
if (v___x_631_ == 0)
{
lean_dec(v_i_628_);
return v_entries_629_;
}
else
{
lean_object* v_k_632_; lean_object* v_v_633_; uint64_t v___x_634_; size_t v_h_635_; size_t v___x_636_; lean_object* v___x_637_; size_t v___x_638_; size_t v___x_639_; size_t v___x_640_; size_t v_h_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_k_632_ = lean_array_fget_borrowed(v_keys_626_, v_i_628_);
v_v_633_ = lean_array_fget_borrowed(v_vals_627_, v_i_628_);
v___x_634_ = l_Lean_instHashableMVarId_hash(v_k_632_);
v_h_635_ = lean_uint64_to_usize(v___x_634_);
v___x_636_ = ((size_t)5ULL);
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = ((size_t)1ULL);
v___x_639_ = lean_usize_sub(v_depth_625_, v___x_638_);
v___x_640_ = lean_usize_mul(v___x_636_, v___x_639_);
v_h_641_ = lean_usize_shift_right(v_h_635_, v___x_640_);
v___x_642_ = lean_nat_add(v_i_628_, v___x_637_);
lean_dec(v_i_628_);
lean_inc(v_v_633_);
lean_inc(v_k_632_);
v___x_643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_entries_629_, v_h_641_, v_depth_625_, v_k_632_, v_v_633_);
v_i_628_ = v___x_642_;
v_entries_629_ = v___x_643_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_645_, lean_object* v_keys_646_, lean_object* v_vals_647_, lean_object* v_i_648_, lean_object* v_entries_649_){
_start:
{
size_t v_depth_boxed_650_; lean_object* v_res_651_; 
v_depth_boxed_650_ = lean_unbox_usize(v_depth_645_);
lean_dec(v_depth_645_);
v_res_651_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_650_, v_keys_646_, v_vals_647_, v_i_648_, v_entries_649_);
lean_dec_ref(v_vals_647_);
lean_dec_ref(v_keys_646_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
size_t v_x_3030__boxed_657_; size_t v_x_3031__boxed_658_; lean_object* v_res_659_; 
v_x_3030__boxed_657_ = lean_unbox_usize(v_x_653_);
lean_dec(v_x_653_);
v_x_3031__boxed_658_ = lean_unbox_usize(v_x_654_);
lean_dec(v_x_654_);
v_res_659_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_652_, v_x_3030__boxed_657_, v_x_3031__boxed_658_, v_x_655_, v_x_656_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
uint64_t v___x_663_; size_t v___x_664_; size_t v___x_665_; lean_object* v___x_666_; 
v___x_663_ = l_Lean_instHashableMVarId_hash(v_x_661_);
v___x_664_ = lean_uint64_to_usize(v___x_663_);
v___x_665_ = ((size_t)1ULL);
v___x_666_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_660_, v___x_664_, v___x_665_, v_x_661_, v_x_662_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(lean_object* v_mvarId_667_, lean_object* v_val_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; lean_object* v_mctx_672_; lean_object* v_cache_673_; lean_object* v_zetaDeltaFVarIds_674_; lean_object* v_postponed_675_; lean_object* v_diag_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_706_; 
v___x_671_ = lean_st_ref_take(v___y_669_);
v_mctx_672_ = lean_ctor_get(v___x_671_, 0);
v_cache_673_ = lean_ctor_get(v___x_671_, 1);
v_zetaDeltaFVarIds_674_ = lean_ctor_get(v___x_671_, 2);
v_postponed_675_ = lean_ctor_get(v___x_671_, 3);
v_diag_676_ = lean_ctor_get(v___x_671_, 4);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_706_ == 0)
{
v___x_678_ = v___x_671_;
v_isShared_679_ = v_isSharedCheck_706_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_diag_676_);
lean_inc(v_postponed_675_);
lean_inc(v_zetaDeltaFVarIds_674_);
lean_inc(v_cache_673_);
lean_inc(v_mctx_672_);
lean_dec(v___x_671_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_706_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_depth_680_; lean_object* v_levelAssignDepth_681_; lean_object* v_lmvarCounter_682_; lean_object* v_mvarCounter_683_; lean_object* v_lDecls_684_; lean_object* v_decls_685_; lean_object* v_userNames_686_; lean_object* v_lAssignment_687_; lean_object* v_eAssignment_688_; lean_object* v_dAssignment_689_; lean_object* v_instanceTypedMVars_690_; lean_object* v_synthNormMemo_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_705_; 
v_depth_680_ = lean_ctor_get(v_mctx_672_, 0);
v_levelAssignDepth_681_ = lean_ctor_get(v_mctx_672_, 1);
v_lmvarCounter_682_ = lean_ctor_get(v_mctx_672_, 2);
v_mvarCounter_683_ = lean_ctor_get(v_mctx_672_, 3);
v_lDecls_684_ = lean_ctor_get(v_mctx_672_, 4);
v_decls_685_ = lean_ctor_get(v_mctx_672_, 5);
v_userNames_686_ = lean_ctor_get(v_mctx_672_, 6);
v_lAssignment_687_ = lean_ctor_get(v_mctx_672_, 7);
v_eAssignment_688_ = lean_ctor_get(v_mctx_672_, 8);
v_dAssignment_689_ = lean_ctor_get(v_mctx_672_, 9);
v_instanceTypedMVars_690_ = lean_ctor_get(v_mctx_672_, 10);
v_synthNormMemo_691_ = lean_ctor_get(v_mctx_672_, 11);
v_isSharedCheck_705_ = !lean_is_exclusive(v_mctx_672_);
if (v_isSharedCheck_705_ == 0)
{
v___x_693_ = v_mctx_672_;
v_isShared_694_ = v_isSharedCheck_705_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_synthNormMemo_691_);
lean_inc(v_instanceTypedMVars_690_);
lean_inc(v_dAssignment_689_);
lean_inc(v_eAssignment_688_);
lean_inc(v_lAssignment_687_);
lean_inc(v_userNames_686_);
lean_inc(v_decls_685_);
lean_inc(v_lDecls_684_);
lean_inc(v_mvarCounter_683_);
lean_inc(v_lmvarCounter_682_);
lean_inc(v_levelAssignDepth_681_);
lean_inc(v_depth_680_);
lean_dec(v_mctx_672_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_705_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_695_ = lean_box(0);
v___x_696_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(v_eAssignment_688_, v_mvarId_667_, v_val_668_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 8, v___x_696_);
v___x_698_ = v___x_693_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_depth_680_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_levelAssignDepth_681_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_lmvarCounter_682_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_mvarCounter_683_);
lean_ctor_set(v_reuseFailAlloc_704_, 4, v_lDecls_684_);
lean_ctor_set(v_reuseFailAlloc_704_, 5, v_decls_685_);
lean_ctor_set(v_reuseFailAlloc_704_, 6, v_userNames_686_);
lean_ctor_set(v_reuseFailAlloc_704_, 7, v_lAssignment_687_);
lean_ctor_set(v_reuseFailAlloc_704_, 8, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_704_, 9, v_dAssignment_689_);
lean_ctor_set(v_reuseFailAlloc_704_, 10, v_instanceTypedMVars_690_);
lean_ctor_set(v_reuseFailAlloc_704_, 11, v_synthNormMemo_691_);
v___x_698_ = v_reuseFailAlloc_704_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_700_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_698_);
v___x_700_ = v___x_678_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_cache_673_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_zetaDeltaFVarIds_674_);
lean_ctor_set(v_reuseFailAlloc_703_, 3, v_postponed_675_);
lean_ctor_set(v_reuseFailAlloc_703_, 4, v_diag_676_);
v___x_700_ = v_reuseFailAlloc_703_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_st_ref_put(v___y_669_, v___x_700_);
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_695_);
return v___x_702_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg___boxed(lean_object* v_mvarId_707_, lean_object* v_val_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_707_, v_val_708_, v___y_709_);
lean_dec(v___y_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___lam__0(lean_object* v_mvarId_712_, lean_object* v_rule_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; 
lean_inc(v_mvarId_712_);
v___x_721_ = l_Lean_MVarId_getDecl(v_mvarId_712_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v_expr_723_; lean_object* v_pattern_724_; lean_object* v_resultPos_725_; lean_object* v_type_726_; uint8_t v___x_727_; lean_object* v___x_728_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v_expr_723_ = lean_ctor_get(v_rule_713_, 0);
lean_inc_ref(v_expr_723_);
v_pattern_724_ = lean_ctor_get(v_rule_713_, 1);
lean_inc_ref_n(v_pattern_724_, 2);
v_resultPos_725_ = lean_ctor_get(v_rule_713_, 2);
lean_inc(v_resultPos_725_);
lean_dec_ref(v_rule_713_);
v_type_726_ = lean_ctor_get(v_a_722_, 2);
lean_inc_ref(v_type_726_);
lean_dec(v_a_722_);
v___x_727_ = 1;
v___x_728_ = l_Lean_Meta_Sym_Pattern_unify_x3f(v_pattern_724_, v_type_726_, v___x_727_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_765_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_765_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_765_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_765_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
if (lean_obj_tag(v_a_729_) == 1)
{
lean_object* v_val_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_760_; 
v_val_733_ = lean_ctor_get(v_a_729_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v_a_729_);
if (v_isSharedCheck_760_ == 0)
{
v___x_735_ = v_a_729_;
v_isShared_736_ = v_isSharedCheck_760_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_val_733_);
lean_dec(v_a_729_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_760_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_unresolvedInsts_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_unresolvedInsts_737_ = lean_ctor_get(v_val_733_, 2);
v___x_738_ = lean_array_get_size(v_unresolvedInsts_737_);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_nat_dec_eq(v___x_738_, v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_743_; 
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec(v_resultPos_725_);
lean_dec_ref(v_pattern_724_);
lean_dec_ref(v_expr_723_);
lean_dec(v_mvarId_712_);
v___x_741_ = lean_box(0);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_741_);
v___x_743_ = v___x_731_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_758_; 
lean_del_object(v___x_731_);
lean_inc(v_val_733_);
v___x_745_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(v_expr_723_, v_pattern_724_, v_val_733_);
lean_dec_ref(v_pattern_724_);
v___x_746_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_712_, v___x_745_, v___y_717_);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v___x_746_, 0);
lean_dec(v_unused_759_);
v___x_748_ = v___x_746_;
v_isShared_749_ = v_isSharedCheck_758_;
goto v_resetjp_747_;
}
else
{
lean_dec(v___x_746_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_758_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_750_ = lean_box(0);
v___x_751_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(v_val_733_, v_resultPos_725_, v___x_750_);
lean_dec(v_val_733_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_751_);
v___x_753_ = v___x_735_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_757_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_753_);
v___x_755_ = v___x_748_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
}
else
{
lean_object* v___x_761_; lean_object* v___x_763_; 
lean_dec(v_a_729_);
lean_dec(v_resultPos_725_);
lean_dec_ref(v_pattern_724_);
lean_dec_ref(v_expr_723_);
lean_dec(v_mvarId_712_);
v___x_761_ = lean_box(0);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_761_);
v___x_763_ = v___x_731_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_resultPos_725_);
lean_dec_ref(v_pattern_724_);
lean_dec_ref(v_expr_723_);
lean_dec(v_mvarId_712_);
v_a_766_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_728_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_728_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec_ref(v_rule_713_);
lean_dec(v_mvarId_712_);
v_a_774_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_721_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_721_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___lam__0___boxed(lean_object* v_mvarId_782_, lean_object* v_rule_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Meta_Sym_BackwardRule_apply___lam__0(v_mvarId_782_, v_rule_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object* v_mvarId_792_, lean_object* v_rule_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___f_801_; lean_object* v___x_802_; 
lean_inc(v_mvarId_792_);
v___f_801_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_BackwardRule_apply___lam__0___boxed), 9, 2);
lean_closure_set(v___f_801_, 0, v_mvarId_792_);
lean_closure_set(v___f_801_, 1, v_rule_793_);
v___x_802_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_792_, v___f_801_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___boxed(lean_object* v_mvarId_803_, lean_object* v_rule_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Meta_Sym_BackwardRule_apply(v_mvarId_803_, v_rule_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(lean_object* v_mvarId_813_, lean_object* v_val_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_813_, v_val_814_, v___y_818_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___boxed(lean_object* v_mvarId_823_, lean_object* v_val_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(v_mvarId_823_, v_val_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0(lean_object* v_00_u03b2_833_, lean_object* v_x_834_, lean_object* v_x_835_, lean_object* v_x_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(v_x_834_, v_x_835_, v_x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_838_, lean_object* v_x_839_, size_t v_x_840_, size_t v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_839_, v_x_840_, v_x_841_, v_x_842_, v_x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_845_, lean_object* v_x_846_, lean_object* v_x_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
size_t v_x_3413__boxed_851_; size_t v_x_3414__boxed_852_; lean_object* v_res_853_; 
v_x_3413__boxed_851_ = lean_unbox_usize(v_x_847_);
lean_dec(v_x_847_);
v_x_3414__boxed_852_ = lean_unbox_usize(v_x_848_);
lean_dec(v_x_848_);
v_res_853_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(v_00_u03b2_845_, v_x_846_, v_x_3413__boxed_851_, v_x_3414__boxed_852_, v_x_849_, v_x_850_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_854_, lean_object* v_n_855_, lean_object* v_k_856_, lean_object* v_v_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(v_n_855_, v_k_856_, v_v_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_859_, size_t v_depth_860_, lean_object* v_keys_861_, lean_object* v_vals_862_, lean_object* v_heq_863_, lean_object* v_i_864_, lean_object* v_entries_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_860_, v_keys_861_, v_vals_862_, v_i_864_, v_entries_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_867_, lean_object* v_depth_868_, lean_object* v_keys_869_, lean_object* v_vals_870_, lean_object* v_heq_871_, lean_object* v_i_872_, lean_object* v_entries_873_){
_start:
{
size_t v_depth_boxed_874_; lean_object* v_res_875_; 
v_depth_boxed_874_ = lean_unbox_usize(v_depth_868_);
lean_dec(v_depth_868_);
v_res_875_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_867_, v_depth_boxed_874_, v_keys_869_, v_vals_870_, v_heq_871_, v_i_872_, v_entries_873_);
lean_dec_ref(v_vals_870_);
lean_dec_ref(v_keys_869_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_876_, lean_object* v_x_877_, lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_877_, v_x_878_, v_x_879_, v_x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(lean_object* v_msgData_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; lean_object* v_env_889_; uint8_t v___x_890_; lean_object* v_env_891_; lean_object* v___x_892_; lean_object* v_toCold_893_; lean_object* v_mctx_894_; lean_object* v_lctx_895_; lean_object* v_options_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_888_ = lean_st_ref_get(v___y_886_);
v_env_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc_ref(v_env_889_);
lean_dec(v___x_888_);
v___x_890_ = 0;
v_env_891_ = l_Lean_Environment_setRecordingDeps(v_env_889_, v___x_890_);
v___x_892_ = lean_st_ref_get(v___y_884_);
v_toCold_893_ = lean_ctor_get(v___y_885_, 0);
v_mctx_894_ = lean_ctor_get(v___x_892_, 0);
lean_inc_ref(v_mctx_894_);
lean_dec(v___x_892_);
v_lctx_895_ = lean_ctor_get(v___y_883_, 2);
v_options_896_ = lean_ctor_get(v_toCold_893_, 2);
lean_inc_ref(v_options_896_);
lean_inc_ref(v_lctx_895_);
v___x_897_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_897_, 0, v_env_891_);
lean_ctor_set(v___x_897_, 1, v_mctx_894_);
lean_ctor_set(v___x_897_, 2, v_lctx_895_);
lean_ctor_set(v___x_897_, 3, v_options_896_);
v___x_898_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v_msgData_882_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0___boxed(lean_object* v_msgData_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(v_msgData_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(lean_object* v_msg_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_ref_913_; lean_object* v___x_914_; lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_923_; 
v_ref_913_ = lean_ctor_get(v___y_910_, 2);
v___x_914_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(v_msg_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_923_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
lean_inc(v_ref_913_);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v_ref_913_);
lean_ctor_set(v___x_919_, 1, v_a_915_);
if (v_isShared_918_ == 0)
{
lean_ctor_set_tag(v___x_917_, 1);
lean_ctor_set(v___x_917_, 0, v___x_919_);
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg___boxed(lean_object* v_msg_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v_msg_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
return v_res_930_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = ((lean_object*)(l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__0));
v___x_933_ = l_Lean_stringToMessageData(v___x_932_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = ((lean_object*)(l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__2));
v___x_936_ = l_Lean_stringToMessageData(v___x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27(lean_object* v_mvarId_937_, lean_object* v_rule_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v___x_946_; 
lean_inc_ref(v_rule_938_);
lean_inc(v_mvarId_937_);
v___x_946_ = l_Lean_Meta_Sym_BackwardRule_apply(v_mvarId_937_, v_rule_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_964_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_964_ == 0)
{
v___x_949_ = v___x_946_;
v_isShared_950_ = v_isSharedCheck_964_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_946_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_964_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
if (lean_obj_tag(v_a_947_) == 1)
{
lean_object* v_mvarIds_951_; lean_object* v___x_953_; 
lean_dec_ref(v_rule_938_);
lean_dec(v_mvarId_937_);
v_mvarIds_951_ = lean_ctor_get(v_a_947_, 0);
lean_inc(v_mvarIds_951_);
lean_dec_ref_known(v_a_947_, 1);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v_mvarIds_951_);
v___x_953_ = v___x_949_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_mvarIds_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
else
{
lean_object* v_expr_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
lean_del_object(v___x_949_);
lean_dec(v_a_947_);
v_expr_955_ = lean_ctor_get(v_rule_938_, 0);
lean_inc_ref(v_expr_955_);
lean_dec_ref(v_rule_938_);
v___x_956_ = lean_obj_once(&l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1, &l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1_once, _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1);
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v_mvarId_937_);
v___x_958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_obj_once(&l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3, &l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3_once, _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3);
v___x_960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = l_Lean_indentExpr(v_expr_955_);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v___x_962_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
return v___x_963_;
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
lean_dec_ref(v_rule_938_);
lean_dec(v_mvarId_937_);
v_a_965_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_946_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_946_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27___boxed(lean_object* v_mvarId_973_, lean_object* v_rule_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_Meta_Sym_BackwardRule_apply_x27(v_mvarId_973_, v_rule_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(lean_object* v_00_u03b1_983_, lean_object* v_msg_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v_msg_984_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___boxed(lean_object* v_00_u03b1_993_, lean_object* v_msg_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(v_00_u03b1_993_, v_msg_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_1002_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Apply(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Apply(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Apply(builtin);
}
#ifdef __cplusplus
}
#endif
