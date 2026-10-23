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
lean_inc(v_levelParams_333_);
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
lean_dec(v_levelParams_333_);
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
lean_dec_ref(v_pattern_373_);
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
lean_inc(v_levelParams_376_);
lean_dec_ref(v_pattern_373_);
v_us_377_ = lean_ctor_get(v_result_374_, 0);
lean_inc(v_us_377_);
v_args_378_ = lean_ctor_get(v_result_374_, 1);
lean_inc_ref(v_args_378_);
lean_dec_ref(v_result_374_);
v___x_379_ = l_Lean_Expr_instantiateLevelParams(v_expr_372_, v_levelParams_376_, v_us_377_);
lean_dec_ref(v_expr_372_);
v___x_380_ = l_Lean_mkAppN(v___x_379_, v_args_378_);
lean_dec_ref(v_args_378_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx___impl(lean_object* v_x_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = lean_obj_tag_nat(v_x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx___impl___boxed(lean_object* v_x_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Meta_Sym_ApplyResult_ctorIdx___impl(v_x_389_);
lean_dec(v_x_389_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(lean_object* v_t_391_, lean_object* v_k_392_){
_start:
{
if (lean_obj_tag(v_t_391_) == 0)
{
return v_k_392_;
}
else
{
lean_object* v_mvarIds_393_; lean_object* v___x_394_; 
v_mvarIds_393_ = lean_ctor_get(v_t_391_, 0);
lean_inc(v_mvarIds_393_);
lean_dec_ref_known(v_t_391_, 1);
v___x_394_ = lean_apply_1(v_k_392_, v_mvarIds_393_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim(lean_object* v_motive_395_, lean_object* v_ctorIdx_396_, lean_object* v_t_397_, lean_object* v_h_398_, lean_object* v_k_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_397_, v_k_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim___boxed(lean_object* v_motive_401_, lean_object* v_ctorIdx_402_, lean_object* v_t_403_, lean_object* v_h_404_, lean_object* v_k_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Meta_Sym_ApplyResult_ctorElim(v_motive_401_, v_ctorIdx_402_, v_t_403_, v_h_404_, v_k_405_);
lean_dec(v_ctorIdx_402_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_failed_elim___redArg(lean_object* v_t_407_, lean_object* v_failed_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_407_, v_failed_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_failed_elim(lean_object* v_motive_410_, lean_object* v_t_411_, lean_object* v_h_412_, lean_object* v_failed_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_411_, v_failed_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_goals_elim___redArg(lean_object* v_t_415_, lean_object* v_goals_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_415_, v_goals_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_goals_elim(lean_object* v_motive_418_, lean_object* v_t_419_, lean_object* v_h_420_, lean_object* v_goals_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_419_, v_goals_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(lean_object* v_x_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___x_431_; 
lean_inc(v___y_425_);
lean_inc_ref(v___y_424_);
v___x_431_ = lean_apply_7(v_x_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, lean_box(0));
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0___boxed(lean_object* v_x_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(v_x_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(lean_object* v_mvarId_441_, lean_object* v_x_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___f_450_; lean_object* v___x_451_; 
lean_inc(v___y_444_);
lean_inc_ref(v___y_443_);
v___f_450_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_450_, 0, v_x_442_);
lean_closure_set(v___f_450_, 1, v___y_443_);
lean_closure_set(v___f_450_, 2, v___y_444_);
v___x_451_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_441_, v___f_450_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
if (lean_obj_tag(v___x_451_) == 0)
{
return v___x_451_;
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___boxed(lean_object* v_mvarId_460_, lean_object* v_x_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_460_, v_x_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(lean_object* v_00_u03b1_470_, lean_object* v_mvarId_471_, lean_object* v_x_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_471_, v_x_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___boxed(lean_object* v_00_u03b1_481_, lean_object* v_mvarId_482_, lean_object* v_x_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(v_00_u03b1_481_, v_mvarId_482_, v_x_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(lean_object* v_val_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
if (lean_obj_tag(v_a_493_) == 0)
{
lean_object* v___x_495_; 
v___x_495_ = l_List_reverse___redArg(v_a_494_);
return v___x_495_;
}
else
{
lean_object* v_head_496_; lean_object* v_tail_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_509_; 
v_head_496_ = lean_ctor_get(v_a_493_, 0);
v_tail_497_ = lean_ctor_get(v_a_493_, 1);
v_isSharedCheck_509_ = !lean_is_exclusive(v_a_493_);
if (v_isSharedCheck_509_ == 0)
{
v___x_499_ = v_a_493_;
v_isShared_500_ = v_isSharedCheck_509_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_tail_497_);
lean_inc(v_head_496_);
lean_dec(v_a_493_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_509_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v_args_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v_args_501_ = lean_ctor_get(v_val_492_, 1);
v___x_502_ = l_Lean_instInhabitedExpr;
v___x_503_ = lean_array_get_borrowed(v___x_502_, v_args_501_, v_head_496_);
lean_dec(v_head_496_);
v___x_504_ = l_Lean_Expr_mvarId_x21(v___x_503_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 1, v_a_494_);
lean_ctor_set(v___x_499_, 0, v___x_504_);
v___x_506_ = v___x_499_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_a_494_);
v___x_506_ = v_reuseFailAlloc_508_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
v_a_493_ = v_tail_497_;
v_a_494_ = v___x_506_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1___boxed(lean_object* v_val_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(v_val_510_, v_a_511_, v_a_512_);
lean_dec_ref(v_val_510_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_514_, lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
lean_object* v_ks_518_; lean_object* v_vs_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_543_; 
v_ks_518_ = lean_ctor_get(v_x_514_, 0);
v_vs_519_ = lean_ctor_get(v_x_514_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v_x_514_);
if (v_isSharedCheck_543_ == 0)
{
v___x_521_ = v_x_514_;
v_isShared_522_ = v_isSharedCheck_543_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_vs_519_);
lean_inc(v_ks_518_);
lean_dec(v_x_514_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_543_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_array_get_size(v_ks_518_);
v___x_524_ = lean_nat_dec_lt(v_x_515_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
lean_dec(v_x_515_);
v___x_525_ = lean_array_push(v_ks_518_, v_x_516_);
v___x_526_ = lean_array_push(v_vs_519_, v_x_517_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_526_);
lean_ctor_set(v___x_521_, 0, v___x_525_);
v___x_528_ = v___x_521_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
else
{
lean_object* v_k_x27_530_; uint8_t v___x_531_; 
v_k_x27_530_ = lean_array_fget_borrowed(v_ks_518_, v_x_515_);
v___x_531_ = l_Lean_instBEqMVarId_beq(v_x_516_, v_k_x27_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_533_; 
if (v_isShared_522_ == 0)
{
v___x_533_ = v___x_521_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_ks_518_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_vs_519_);
v___x_533_ = v_reuseFailAlloc_537_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_add(v_x_515_, v___x_534_);
lean_dec(v_x_515_);
v_x_514_ = v___x_533_;
v_x_515_ = v___x_535_;
goto _start;
}
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_538_ = lean_array_fset(v_ks_518_, v_x_515_, v_x_516_);
v___x_539_ = lean_array_fset(v_vs_519_, v_x_515_, v_x_517_);
lean_dec(v_x_515_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_539_);
lean_ctor_set(v___x_521_, 0, v___x_538_);
v___x_541_ = v___x_521_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_n_544_, lean_object* v_k_545_, lean_object* v_v_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_544_, v___x_547_, v_k_545_, v_v_546_);
return v___x_548_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(lean_object* v_x_550_, size_t v_x_551_, size_t v_x_552_, lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
if (lean_obj_tag(v_x_550_) == 0)
{
lean_object* v_es_555_; size_t v___x_556_; size_t v___x_557_; lean_object* v_j_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v_es_555_ = lean_ctor_get(v_x_550_, 0);
v___x_556_ = ((size_t)31ULL);
v___x_557_ = lean_usize_land(v_x_551_, v___x_556_);
v_j_558_ = lean_usize_to_nat(v___x_557_);
v___x_559_ = lean_array_get_size(v_es_555_);
v___x_560_ = lean_nat_dec_lt(v_j_558_, v___x_559_);
if (v___x_560_ == 0)
{
lean_dec(v_j_558_);
lean_dec(v_x_554_);
lean_dec(v_x_553_);
return v_x_550_;
}
else
{
lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_599_; 
lean_inc_ref(v_es_555_);
v_isSharedCheck_599_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v_x_550_, 0);
lean_dec(v_unused_600_);
v___x_562_ = v_x_550_;
v_isShared_563_ = v_isSharedCheck_599_;
goto v_resetjp_561_;
}
else
{
lean_dec(v_x_550_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_599_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v_v_564_; lean_object* v___x_565_; lean_object* v_xs_x27_566_; lean_object* v___y_568_; 
v_v_564_ = lean_array_fget(v_es_555_, v_j_558_);
v___x_565_ = lean_box(0);
v_xs_x27_566_ = lean_array_fset(v_es_555_, v_j_558_, v___x_565_);
switch(lean_obj_tag(v_v_564_))
{
case 0:
{
lean_object* v_key_573_; lean_object* v_val_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_584_; 
v_key_573_ = lean_ctor_get(v_v_564_, 0);
v_val_574_ = lean_ctor_get(v_v_564_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_v_564_);
if (v_isSharedCheck_584_ == 0)
{
v___x_576_ = v_v_564_;
v_isShared_577_ = v_isSharedCheck_584_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_val_574_);
lean_inc(v_key_573_);
lean_dec(v_v_564_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_584_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
uint8_t v___x_578_; 
v___x_578_ = l_Lean_instBEqMVarId_beq(v_x_553_, v_key_573_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_del_object(v___x_576_);
v___x_579_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_573_, v_val_574_, v_x_553_, v_x_554_);
v___x_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
v___y_568_ = v___x_580_;
goto v___jp_567_;
}
else
{
lean_object* v___x_582_; 
lean_dec(v_val_574_);
lean_dec(v_key_573_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 1, v_x_554_);
lean_ctor_set(v___x_576_, 0, v_x_553_);
v___x_582_ = v___x_576_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_x_553_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_x_554_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
v___y_568_ = v___x_582_;
goto v___jp_567_;
}
}
}
}
case 1:
{
lean_object* v_node_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_597_; 
v_node_585_ = lean_ctor_get(v_v_564_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_v_564_);
if (v_isSharedCheck_597_ == 0)
{
v___x_587_ = v_v_564_;
v_isShared_588_ = v_isSharedCheck_597_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_node_585_);
lean_dec(v_v_564_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_597_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
size_t v___x_589_; size_t v___x_590_; size_t v___x_591_; size_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_589_ = ((size_t)5ULL);
v___x_590_ = lean_usize_shift_right(v_x_551_, v___x_589_);
v___x_591_ = ((size_t)1ULL);
v___x_592_ = lean_usize_add(v_x_552_, v___x_591_);
v___x_593_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_node_585_, v___x_590_, v___x_592_, v_x_553_, v_x_554_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_593_);
v___x_595_ = v___x_587_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
v___y_568_ = v___x_595_;
goto v___jp_567_;
}
}
}
default: 
{
lean_object* v___x_598_; 
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_x_553_);
lean_ctor_set(v___x_598_, 1, v_x_554_);
v___y_568_ = v___x_598_;
goto v___jp_567_;
}
}
v___jp_567_:
{
lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_569_ = lean_array_fset(v_xs_x27_566_, v_j_558_, v___y_568_);
lean_dec(v_j_558_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_569_);
v___x_571_ = v___x_562_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
else
{
lean_object* v_ks_601_; lean_object* v_vs_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_620_; 
v_ks_601_ = lean_ctor_get(v_x_550_, 0);
v_vs_602_ = lean_ctor_get(v_x_550_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_620_ == 0)
{
v___x_604_ = v_x_550_;
v_isShared_605_ = v_isSharedCheck_620_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_vs_602_);
lean_inc(v_ks_601_);
lean_dec(v_x_550_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_620_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_ks_601_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_vs_602_);
v___x_607_ = v_reuseFailAlloc_619_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v_newNode_608_; size_t v___x_609_; uint8_t v___x_610_; 
v_newNode_608_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(v___x_607_, v_x_553_, v_x_554_);
v___x_609_ = ((size_t)7ULL);
v___x_610_ = lean_usize_dec_le(v___x_609_, v_x_552_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_611_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_608_);
v___x_612_ = lean_unsigned_to_nat(4u);
v___x_613_ = lean_nat_dec_lt(v___x_611_, v___x_612_);
lean_dec(v___x_611_);
if (v___x_613_ == 0)
{
lean_object* v_ks_614_; lean_object* v_vs_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_ks_614_ = lean_ctor_get(v_newNode_608_, 0);
lean_inc_ref(v_ks_614_);
v_vs_615_ = lean_ctor_get(v_newNode_608_, 1);
lean_inc_ref(v_vs_615_);
lean_dec_ref(v_newNode_608_);
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_618_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_x_552_, v_ks_614_, v_vs_615_, v___x_616_, v___x_617_);
lean_dec_ref(v_vs_615_);
lean_dec_ref(v_ks_614_);
return v___x_618_;
}
else
{
return v_newNode_608_;
}
}
else
{
return v_newNode_608_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_621_, lean_object* v_keys_622_, lean_object* v_vals_623_, lean_object* v_i_624_, lean_object* v_entries_625_){
_start:
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_array_get_size(v_keys_622_);
v___x_627_ = lean_nat_dec_lt(v_i_624_, v___x_626_);
if (v___x_627_ == 0)
{
lean_dec(v_i_624_);
return v_entries_625_;
}
else
{
lean_object* v_k_628_; lean_object* v_v_629_; uint64_t v___x_630_; size_t v_h_631_; size_t v___x_632_; lean_object* v___x_633_; size_t v___x_634_; size_t v___x_635_; size_t v___x_636_; size_t v_h_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_k_628_ = lean_array_fget_borrowed(v_keys_622_, v_i_624_);
v_v_629_ = lean_array_fget_borrowed(v_vals_623_, v_i_624_);
v___x_630_ = l_Lean_instHashableMVarId_hash(v_k_628_);
v_h_631_ = lean_uint64_to_usize(v___x_630_);
v___x_632_ = ((size_t)5ULL);
v___x_633_ = lean_unsigned_to_nat(1u);
v___x_634_ = ((size_t)1ULL);
v___x_635_ = lean_usize_sub(v_depth_621_, v___x_634_);
v___x_636_ = lean_usize_mul(v___x_632_, v___x_635_);
v_h_637_ = lean_usize_shift_right(v_h_631_, v___x_636_);
v___x_638_ = lean_nat_add(v_i_624_, v___x_633_);
lean_dec(v_i_624_);
lean_inc(v_v_629_);
lean_inc(v_k_628_);
v___x_639_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_entries_625_, v_h_637_, v_depth_621_, v_k_628_, v_v_629_);
v_i_624_ = v___x_638_;
v_entries_625_ = v___x_639_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_641_, lean_object* v_keys_642_, lean_object* v_vals_643_, lean_object* v_i_644_, lean_object* v_entries_645_){
_start:
{
size_t v_depth_boxed_646_; lean_object* v_res_647_; 
v_depth_boxed_646_ = lean_unbox_usize(v_depth_641_);
lean_dec(v_depth_641_);
v_res_647_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_646_, v_keys_642_, v_vals_643_, v_i_644_, v_entries_645_);
lean_dec_ref(v_vals_643_);
lean_dec_ref(v_keys_642_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_648_, lean_object* v_x_649_, lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
size_t v_x_3030__boxed_653_; size_t v_x_3031__boxed_654_; lean_object* v_res_655_; 
v_x_3030__boxed_653_ = lean_unbox_usize(v_x_649_);
lean_dec(v_x_649_);
v_x_3031__boxed_654_ = lean_unbox_usize(v_x_650_);
lean_dec(v_x_650_);
v_res_655_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_648_, v_x_3030__boxed_653_, v_x_3031__boxed_654_, v_x_651_, v_x_652_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
uint64_t v___x_659_; size_t v___x_660_; size_t v___x_661_; lean_object* v___x_662_; 
v___x_659_ = l_Lean_instHashableMVarId_hash(v_x_657_);
v___x_660_ = lean_uint64_to_usize(v___x_659_);
v___x_661_ = ((size_t)1ULL);
v___x_662_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_656_, v___x_660_, v___x_661_, v_x_657_, v_x_658_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(lean_object* v_mvarId_663_, lean_object* v_val_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_667_; lean_object* v_mctx_668_; lean_object* v_cache_669_; lean_object* v_zetaDeltaFVarIds_670_; lean_object* v_postponed_671_; lean_object* v_diag_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_702_; 
v___x_667_ = lean_st_ref_take(v___y_665_);
v_mctx_668_ = lean_ctor_get(v___x_667_, 0);
v_cache_669_ = lean_ctor_get(v___x_667_, 1);
v_zetaDeltaFVarIds_670_ = lean_ctor_get(v___x_667_, 2);
v_postponed_671_ = lean_ctor_get(v___x_667_, 3);
v_diag_672_ = lean_ctor_get(v___x_667_, 4);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_702_ == 0)
{
v___x_674_ = v___x_667_;
v_isShared_675_ = v_isSharedCheck_702_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_diag_672_);
lean_inc(v_postponed_671_);
lean_inc(v_zetaDeltaFVarIds_670_);
lean_inc(v_cache_669_);
lean_inc(v_mctx_668_);
lean_dec(v___x_667_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_702_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_depth_676_; lean_object* v_levelAssignDepth_677_; lean_object* v_lmvarCounter_678_; lean_object* v_mvarCounter_679_; lean_object* v_lDecls_680_; lean_object* v_decls_681_; lean_object* v_userNames_682_; lean_object* v_lAssignment_683_; lean_object* v_eAssignment_684_; lean_object* v_dAssignment_685_; lean_object* v_instanceTypedMVars_686_; lean_object* v_synthNormMemo_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_701_; 
v_depth_676_ = lean_ctor_get(v_mctx_668_, 0);
v_levelAssignDepth_677_ = lean_ctor_get(v_mctx_668_, 1);
v_lmvarCounter_678_ = lean_ctor_get(v_mctx_668_, 2);
v_mvarCounter_679_ = lean_ctor_get(v_mctx_668_, 3);
v_lDecls_680_ = lean_ctor_get(v_mctx_668_, 4);
v_decls_681_ = lean_ctor_get(v_mctx_668_, 5);
v_userNames_682_ = lean_ctor_get(v_mctx_668_, 6);
v_lAssignment_683_ = lean_ctor_get(v_mctx_668_, 7);
v_eAssignment_684_ = lean_ctor_get(v_mctx_668_, 8);
v_dAssignment_685_ = lean_ctor_get(v_mctx_668_, 9);
v_instanceTypedMVars_686_ = lean_ctor_get(v_mctx_668_, 10);
v_synthNormMemo_687_ = lean_ctor_get(v_mctx_668_, 11);
v_isSharedCheck_701_ = !lean_is_exclusive(v_mctx_668_);
if (v_isSharedCheck_701_ == 0)
{
v___x_689_ = v_mctx_668_;
v_isShared_690_ = v_isSharedCheck_701_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_synthNormMemo_687_);
lean_inc(v_instanceTypedMVars_686_);
lean_inc(v_dAssignment_685_);
lean_inc(v_eAssignment_684_);
lean_inc(v_lAssignment_683_);
lean_inc(v_userNames_682_);
lean_inc(v_decls_681_);
lean_inc(v_lDecls_680_);
lean_inc(v_mvarCounter_679_);
lean_inc(v_lmvarCounter_678_);
lean_inc(v_levelAssignDepth_677_);
lean_inc(v_depth_676_);
lean_dec(v_mctx_668_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_701_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_691_ = lean_box(0);
v___x_692_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(v_eAssignment_684_, v_mvarId_663_, v_val_664_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 8, v___x_692_);
v___x_694_ = v___x_689_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_depth_676_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_levelAssignDepth_677_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_lmvarCounter_678_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_mvarCounter_679_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v_lDecls_680_);
lean_ctor_set(v_reuseFailAlloc_700_, 5, v_decls_681_);
lean_ctor_set(v_reuseFailAlloc_700_, 6, v_userNames_682_);
lean_ctor_set(v_reuseFailAlloc_700_, 7, v_lAssignment_683_);
lean_ctor_set(v_reuseFailAlloc_700_, 8, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_700_, 9, v_dAssignment_685_);
lean_ctor_set(v_reuseFailAlloc_700_, 10, v_instanceTypedMVars_686_);
lean_ctor_set(v_reuseFailAlloc_700_, 11, v_synthNormMemo_687_);
v___x_694_ = v_reuseFailAlloc_700_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_696_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_694_);
v___x_696_ = v___x_674_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_cache_669_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_zetaDeltaFVarIds_670_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v_postponed_671_);
lean_ctor_set(v_reuseFailAlloc_699_, 4, v_diag_672_);
v___x_696_ = v_reuseFailAlloc_699_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_st_ref_put(v___y_665_, v___x_696_);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_691_);
return v___x_698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg___boxed(lean_object* v_mvarId_703_, lean_object* v_val_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_703_, v_val_704_, v___y_705_);
lean_dec(v___y_705_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___lam__0(lean_object* v_mvarId_708_, lean_object* v_rule_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___x_717_; 
lean_inc(v_mvarId_708_);
v___x_717_ = l_Lean_MVarId_getDecl(v_mvarId_708_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v_expr_719_; lean_object* v_pattern_720_; lean_object* v_resultPos_721_; lean_object* v_type_722_; uint8_t v___x_723_; lean_object* v___x_724_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
v_expr_719_ = lean_ctor_get(v_rule_709_, 0);
lean_inc_ref(v_expr_719_);
v_pattern_720_ = lean_ctor_get(v_rule_709_, 1);
lean_inc_ref_n(v_pattern_720_, 2);
v_resultPos_721_ = lean_ctor_get(v_rule_709_, 2);
lean_inc(v_resultPos_721_);
lean_dec_ref(v_rule_709_);
v_type_722_ = lean_ctor_get(v_a_718_, 2);
lean_inc_ref(v_type_722_);
lean_dec(v_a_718_);
v___x_723_ = 1;
v___x_724_ = l_Lean_Meta_Sym_Pattern_unify_x3f(v_pattern_720_, v_type_722_, v___x_723_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_761_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_761_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_761_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_761_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
if (lean_obj_tag(v_a_725_) == 1)
{
lean_object* v_val_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_756_; 
v_val_729_ = lean_ctor_get(v_a_725_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v_a_725_);
if (v_isSharedCheck_756_ == 0)
{
v___x_731_ = v_a_725_;
v_isShared_732_ = v_isSharedCheck_756_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_val_729_);
lean_dec(v_a_725_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_756_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v_unresolvedInsts_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v_unresolvedInsts_733_ = lean_ctor_get(v_val_729_, 2);
v___x_734_ = lean_array_get_size(v_unresolvedInsts_733_);
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = lean_nat_dec_eq(v___x_734_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_739_; 
lean_del_object(v___x_731_);
lean_dec(v_val_729_);
lean_dec(v_resultPos_721_);
lean_dec_ref(v_pattern_720_);
lean_dec_ref(v_expr_719_);
lean_dec(v_mvarId_708_);
v___x_737_ = lean_box(0);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_737_);
v___x_739_ = v___x_727_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_754_; 
lean_del_object(v___x_727_);
lean_inc(v_val_729_);
v___x_741_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(v_expr_719_, v_pattern_720_, v_val_729_);
v___x_742_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_708_, v___x_741_, v___y_713_);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v___x_742_, 0);
lean_dec(v_unused_755_);
v___x_744_ = v___x_742_;
v_isShared_745_ = v_isSharedCheck_754_;
goto v_resetjp_743_;
}
else
{
lean_dec(v___x_742_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_754_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_746_ = lean_box(0);
v___x_747_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(v_val_729_, v_resultPos_721_, v___x_746_);
lean_dec(v_val_729_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_747_);
v___x_749_ = v___x_731_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_753_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_749_);
v___x_751_ = v___x_744_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
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
}
}
else
{
lean_object* v___x_757_; lean_object* v___x_759_; 
lean_dec(v_a_725_);
lean_dec(v_resultPos_721_);
lean_dec_ref(v_pattern_720_);
lean_dec_ref(v_expr_719_);
lean_dec(v_mvarId_708_);
v___x_757_ = lean_box(0);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_757_);
v___x_759_ = v___x_727_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
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
lean_dec(v_resultPos_721_);
lean_dec_ref(v_pattern_720_);
lean_dec_ref(v_expr_719_);
lean_dec(v_mvarId_708_);
v_a_762_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_724_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_724_);
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
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref(v_rule_709_);
lean_dec(v_mvarId_708_);
v_a_770_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_717_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_717_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___lam__0___boxed(lean_object* v_mvarId_778_, lean_object* v_rule_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Meta_Sym_BackwardRule_apply___lam__0(v_mvarId_778_, v_rule_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object* v_mvarId_788_, lean_object* v_rule_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v___f_797_; lean_object* v___x_798_; 
lean_inc(v_mvarId_788_);
v___f_797_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_BackwardRule_apply___lam__0___boxed), 9, 2);
lean_closure_set(v___f_797_, 0, v_mvarId_788_);
lean_closure_set(v___f_797_, 1, v_rule_789_);
v___x_798_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_788_, v___f_797_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___boxed(lean_object* v_mvarId_799_, lean_object* v_rule_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Meta_Sym_BackwardRule_apply(v_mvarId_799_, v_rule_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(lean_object* v_mvarId_809_, lean_object* v_val_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_809_, v_val_810_, v___y_814_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___boxed(lean_object* v_mvarId_819_, lean_object* v_val_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(v_mvarId_819_, v_val_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0(lean_object* v_00_u03b2_829_, lean_object* v_x_830_, lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(v_x_830_, v_x_831_, v_x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_834_, lean_object* v_x_835_, size_t v_x_836_, size_t v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_835_, v_x_836_, v_x_837_, v_x_838_, v_x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
size_t v_x_3413__boxed_847_; size_t v_x_3414__boxed_848_; lean_object* v_res_849_; 
v_x_3413__boxed_847_ = lean_unbox_usize(v_x_843_);
lean_dec(v_x_843_);
v_x_3414__boxed_848_ = lean_unbox_usize(v_x_844_);
lean_dec(v_x_844_);
v_res_849_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(v_00_u03b2_841_, v_x_842_, v_x_3413__boxed_847_, v_x_3414__boxed_848_, v_x_845_, v_x_846_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_850_, lean_object* v_n_851_, lean_object* v_k_852_, lean_object* v_v_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(v_n_851_, v_k_852_, v_v_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_855_, size_t v_depth_856_, lean_object* v_keys_857_, lean_object* v_vals_858_, lean_object* v_heq_859_, lean_object* v_i_860_, lean_object* v_entries_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_856_, v_keys_857_, v_vals_858_, v_i_860_, v_entries_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_863_, lean_object* v_depth_864_, lean_object* v_keys_865_, lean_object* v_vals_866_, lean_object* v_heq_867_, lean_object* v_i_868_, lean_object* v_entries_869_){
_start:
{
size_t v_depth_boxed_870_; lean_object* v_res_871_; 
v_depth_boxed_870_ = lean_unbox_usize(v_depth_864_);
lean_dec(v_depth_864_);
v_res_871_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_863_, v_depth_boxed_870_, v_keys_865_, v_vals_866_, v_heq_867_, v_i_868_, v_entries_869_);
lean_dec_ref(v_vals_866_);
lean_dec_ref(v_keys_865_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_873_, v_x_874_, v_x_875_, v_x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(lean_object* v_msgData_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; lean_object* v_env_885_; uint8_t v___x_886_; lean_object* v_env_887_; lean_object* v___x_888_; lean_object* v_toCold_889_; lean_object* v_mctx_890_; lean_object* v_lctx_891_; lean_object* v_options_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_884_ = lean_st_ref_get(v___y_882_);
v_env_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc_ref(v_env_885_);
lean_dec(v___x_884_);
v___x_886_ = 0;
v_env_887_ = l_Lean_Environment_setRecordingDeps(v_env_885_, v___x_886_);
v___x_888_ = lean_st_ref_get(v___y_880_);
v_toCold_889_ = lean_ctor_get(v___y_881_, 0);
v_mctx_890_ = lean_ctor_get(v___x_888_, 0);
lean_inc_ref(v_mctx_890_);
lean_dec(v___x_888_);
v_lctx_891_ = lean_ctor_get(v___y_879_, 2);
v_options_892_ = lean_ctor_get(v_toCold_889_, 2);
lean_inc_ref(v_options_892_);
lean_inc_ref(v_lctx_891_);
v___x_893_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_893_, 0, v_env_887_);
lean_ctor_set(v___x_893_, 1, v_mctx_890_);
lean_ctor_set(v___x_893_, 2, v_lctx_891_);
lean_ctor_set(v___x_893_, 3, v_options_892_);
v___x_894_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v_msgData_878_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0___boxed(lean_object* v_msgData_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(v_msgData_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(lean_object* v_msg_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_ref_909_; lean_object* v___x_910_; lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_919_; 
v_ref_909_ = lean_ctor_get(v___y_906_, 2);
v___x_910_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(v_msg_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_919_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_919_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_919_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
lean_inc(v_ref_909_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v_ref_909_);
lean_ctor_set(v___x_915_, 1, v_a_911_);
if (v_isShared_914_ == 0)
{
lean_ctor_set_tag(v___x_913_, 1);
lean_ctor_set(v___x_913_, 0, v___x_915_);
v___x_917_ = v___x_913_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg___boxed(lean_object* v_msg_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v_msg_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
return v_res_926_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__0));
v___x_929_ = l_Lean_stringToMessageData(v___x_928_);
return v___x_929_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__2));
v___x_932_ = l_Lean_stringToMessageData(v___x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27(lean_object* v_mvarId_933_, lean_object* v_rule_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v___x_942_; 
lean_inc_ref(v_rule_934_);
lean_inc(v_mvarId_933_);
v___x_942_ = l_Lean_Meta_Sym_BackwardRule_apply(v_mvarId_933_, v_rule_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_960_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_960_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_960_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_960_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
if (lean_obj_tag(v_a_943_) == 1)
{
lean_object* v_mvarIds_947_; lean_object* v___x_949_; 
lean_dec_ref(v_rule_934_);
lean_dec(v_mvarId_933_);
v_mvarIds_947_ = lean_ctor_get(v_a_943_, 0);
lean_inc(v_mvarIds_947_);
lean_dec_ref_known(v_a_943_, 1);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v_mvarIds_947_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_mvarIds_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
else
{
lean_object* v_expr_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
lean_del_object(v___x_945_);
lean_dec(v_a_943_);
v_expr_951_ = lean_ctor_get(v_rule_934_, 0);
lean_inc_ref(v_expr_951_);
lean_dec_ref(v_rule_934_);
v___x_952_ = lean_obj_once(&l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1, &l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1_once, _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1);
v___x_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_953_, 0, v_mvarId_933_);
v___x_954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_obj_once(&l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3, &l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3_once, _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3);
v___x_956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = l_Lean_indentExpr(v_expr_951_);
v___x_958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v___x_958_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
return v___x_959_;
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec_ref(v_rule_934_);
lean_dec(v_mvarId_933_);
v_a_961_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_942_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_942_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27___boxed(lean_object* v_mvarId_969_, lean_object* v_rule_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_Meta_Sym_BackwardRule_apply_x27(v_mvarId_969_, v_rule_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(lean_object* v_00_u03b1_979_, lean_object* v_msg_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v_msg_980_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___boxed(lean_object* v_00_u03b1_989_, lean_object* v_msg_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(v_00_u03b1_989_, v_msg_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
return v_res_998_;
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
