// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.ReorderVars
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Lean.Meta.Tactic.Grind.Arith.Cutsat.EqCnstr import Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr import Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default___redArg();
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_getGoalStackDepth___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_norm(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Internal_Linear_instBEqPoly_beq(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2083(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2083___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmpPenalty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmpPenalty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_reorder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__7_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__4_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__8_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__6_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__32(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__32___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__31_spec__40(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__31(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__31_spec__40___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__31(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__31___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__18_spec__23(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__18(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__18_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__28(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__27_spec__35(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__27_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34_spec__45___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34_spec__45___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__33___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__33___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7___redArg(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__21_spec__27(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__21(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__21_spec__27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__11_spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "old2new: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reorder"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value;
static const lean_array_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "search"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_value),LEAN_SCALAR_PTR_LITERAL(116, 65, 210, 255, 142, 133, 148, 120)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value),LEAN_SCALAR_PTR_LITERAL(236, 159, 191, 181, 87, 7, 198, 44)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "new2old: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value),LEAN_SCALAR_PTR_LITERAL(144, 165, 104, 86, 70, 21, 218, 13)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "reordering variables, epoch: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__33(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34_spec__45(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34_spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(lean_object* v_a_5_, lean_object* v_x_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_9_; lean_object* v___y_11_; lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_9_ = lean_box(0);
v___x_14_ = lean_array_get_size(v_a_7_);
v___x_15_ = lean_nat_dec_lt(v_x_6_, v___x_14_);
if (v___x_15_ == 0)
{
lean_dec(v_a_5_);
v___y_11_ = v_a_7_;
goto v___jp_10_;
}
else
{
lean_object* v_v_16_; lean_object* v_maxLowerCoeff_17_; lean_object* v_maxUpperCoeff_18_; lean_object* v_maxDvdCoeff_19_; lean_object* v_minCoeff_20_; lean_object* v_penalty_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_33_; 
v_v_16_ = lean_array_fget(v_a_7_, v_x_6_);
v_maxLowerCoeff_17_ = lean_ctor_get(v_v_16_, 0);
v_maxUpperCoeff_18_ = lean_ctor_get(v_v_16_, 1);
v_maxDvdCoeff_19_ = lean_ctor_get(v_v_16_, 2);
v_minCoeff_20_ = lean_ctor_get(v_v_16_, 3);
v_penalty_21_ = lean_ctor_get(v_v_16_, 4);
v_isSharedCheck_33_ = !lean_is_exclusive(v_v_16_);
if (v_isSharedCheck_33_ == 0)
{
v___x_23_ = v_v_16_;
v_isShared_24_ = v_isSharedCheck_33_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_penalty_21_);
lean_inc(v_minCoeff_20_);
lean_inc(v_maxDvdCoeff_19_);
lean_inc(v_maxUpperCoeff_18_);
lean_inc(v_maxLowerCoeff_17_);
lean_dec(v_v_16_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_33_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v_xs_x27_25_; lean_object* v___y_27_; uint8_t v___x_32_; 
v_xs_x27_25_ = lean_array_fset(v_a_7_, v_x_6_, v___x_9_);
v___x_32_ = lean_nat_dec_le(v_a_5_, v_maxLowerCoeff_17_);
if (v___x_32_ == 0)
{
lean_dec(v_maxLowerCoeff_17_);
v___y_27_ = v_a_5_;
goto v___jp_26_;
}
else
{
lean_dec(v_a_5_);
v___y_27_ = v_maxLowerCoeff_17_;
goto v___jp_26_;
}
v___jp_26_:
{
lean_object* v___x_29_; 
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 0, v___y_27_);
v___x_29_ = v___x_23_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___y_27_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_maxUpperCoeff_18_);
lean_ctor_set(v_reuseFailAlloc_31_, 2, v_maxDvdCoeff_19_);
lean_ctor_set(v_reuseFailAlloc_31_, 3, v_minCoeff_20_);
lean_ctor_set(v_reuseFailAlloc_31_, 4, v_penalty_21_);
v___x_29_ = v_reuseFailAlloc_31_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
lean_object* v___x_30_; 
v___x_30_ = lean_array_fset(v_xs_x27_25_, v_x_6_, v___x_29_);
v___y_11_ = v___x_30_;
goto v___jp_10_;
}
}
}
}
v___jp_10_:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_9_);
lean_ctor_set(v___x_12_, 1, v___y_11_);
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg___boxed(lean_object* v_a_34_, lean_object* v_x_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v_a_34_, v_x_35_, v_a_36_);
lean_dec(v_x_35_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(lean_object* v_a_39_, lean_object* v_x_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v_a_39_, v_x_40_, v_a_41_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___boxed(lean_object* v_a_54_, lean_object* v_x_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(v_a_54_, v_x_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec(v_a_57_);
lean_dec(v_x_55_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(lean_object* v_a_69_, lean_object* v_x_70_, lean_object* v_a_71_){
_start:
{
lean_object* v___x_73_; lean_object* v___y_75_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_73_ = lean_box(0);
v___x_78_ = lean_array_get_size(v_a_71_);
v___x_79_ = lean_nat_dec_lt(v_x_70_, v___x_78_);
if (v___x_79_ == 0)
{
lean_dec(v_a_69_);
v___y_75_ = v_a_71_;
goto v___jp_74_;
}
else
{
lean_object* v_v_80_; lean_object* v_maxLowerCoeff_81_; lean_object* v_maxUpperCoeff_82_; lean_object* v_maxDvdCoeff_83_; lean_object* v_minCoeff_84_; lean_object* v_penalty_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_97_; 
v_v_80_ = lean_array_fget(v_a_71_, v_x_70_);
v_maxLowerCoeff_81_ = lean_ctor_get(v_v_80_, 0);
v_maxUpperCoeff_82_ = lean_ctor_get(v_v_80_, 1);
v_maxDvdCoeff_83_ = lean_ctor_get(v_v_80_, 2);
v_minCoeff_84_ = lean_ctor_get(v_v_80_, 3);
v_penalty_85_ = lean_ctor_get(v_v_80_, 4);
v_isSharedCheck_97_ = !lean_is_exclusive(v_v_80_);
if (v_isSharedCheck_97_ == 0)
{
v___x_87_ = v_v_80_;
v_isShared_88_ = v_isSharedCheck_97_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_penalty_85_);
lean_inc(v_minCoeff_84_);
lean_inc(v_maxDvdCoeff_83_);
lean_inc(v_maxUpperCoeff_82_);
lean_inc(v_maxLowerCoeff_81_);
lean_dec(v_v_80_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_97_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v_xs_x27_89_; lean_object* v___y_91_; uint8_t v___x_96_; 
v_xs_x27_89_ = lean_array_fset(v_a_71_, v_x_70_, v___x_73_);
v___x_96_ = lean_nat_dec_le(v_a_69_, v_maxUpperCoeff_82_);
if (v___x_96_ == 0)
{
lean_dec(v_maxUpperCoeff_82_);
v___y_91_ = v_a_69_;
goto v___jp_90_;
}
else
{
lean_dec(v_a_69_);
v___y_91_ = v_maxUpperCoeff_82_;
goto v___jp_90_;
}
v___jp_90_:
{
lean_object* v___x_93_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 1, v___y_91_);
v___x_93_ = v___x_87_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_maxLowerCoeff_81_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v___y_91_);
lean_ctor_set(v_reuseFailAlloc_95_, 2, v_maxDvdCoeff_83_);
lean_ctor_set(v_reuseFailAlloc_95_, 3, v_minCoeff_84_);
lean_ctor_set(v_reuseFailAlloc_95_, 4, v_penalty_85_);
v___x_93_ = v_reuseFailAlloc_95_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_94_; 
v___x_94_ = lean_array_fset(v_xs_x27_89_, v_x_70_, v___x_93_);
v___y_75_ = v___x_94_;
goto v___jp_74_;
}
}
}
}
v___jp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_73_);
lean_ctor_set(v___x_76_, 1, v___y_75_);
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg___boxed(lean_object* v_a_98_, lean_object* v_x_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_98_, v_x_99_, v_a_100_);
lean_dec(v_x_99_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(lean_object* v_a_103_, lean_object* v_x_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_103_, v_x_104_, v_a_105_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___boxed(lean_object* v_a_118_, lean_object* v_x_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(v_a_118_, v_x_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec(v_a_121_);
lean_dec(v_x_119_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin___redArg(lean_object* v_a_133_, lean_object* v_x_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_137_; lean_object* v___y_139_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_137_ = lean_box(0);
v___x_142_ = lean_array_get_size(v_a_135_);
v___x_143_ = lean_nat_dec_lt(v_x_134_, v___x_142_);
if (v___x_143_ == 0)
{
lean_dec(v_a_133_);
v___y_139_ = v_a_135_;
goto v___jp_138_;
}
else
{
lean_object* v_v_144_; lean_object* v_maxLowerCoeff_145_; lean_object* v_maxUpperCoeff_146_; lean_object* v_maxDvdCoeff_147_; lean_object* v_minCoeff_148_; lean_object* v_penalty_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_163_; 
v_v_144_ = lean_array_fget(v_a_135_, v_x_134_);
v_maxLowerCoeff_145_ = lean_ctor_get(v_v_144_, 0);
v_maxUpperCoeff_146_ = lean_ctor_get(v_v_144_, 1);
v_maxDvdCoeff_147_ = lean_ctor_get(v_v_144_, 2);
v_minCoeff_148_ = lean_ctor_get(v_v_144_, 3);
v_penalty_149_ = lean_ctor_get(v_v_144_, 4);
v_isSharedCheck_163_ = !lean_is_exclusive(v_v_144_);
if (v_isSharedCheck_163_ == 0)
{
v___x_151_ = v_v_144_;
v_isShared_152_ = v_isSharedCheck_163_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_penalty_149_);
lean_inc(v_minCoeff_148_);
lean_inc(v_maxDvdCoeff_147_);
lean_inc(v_maxUpperCoeff_146_);
lean_inc(v_maxLowerCoeff_145_);
lean_dec(v_v_144_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_163_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v_xs_x27_153_; lean_object* v___y_155_; lean_object* v___x_160_; uint8_t v___x_161_; 
v_xs_x27_153_ = lean_array_fset(v_a_135_, v_x_134_, v___x_137_);
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = lean_nat_dec_eq(v_minCoeff_148_, v___x_160_);
if (v___x_161_ == 0)
{
uint8_t v___x_162_; 
v___x_162_ = lean_nat_dec_le(v_a_133_, v_minCoeff_148_);
if (v___x_162_ == 0)
{
lean_dec(v_a_133_);
v___y_155_ = v_minCoeff_148_;
goto v___jp_154_;
}
else
{
lean_dec(v_minCoeff_148_);
v___y_155_ = v_a_133_;
goto v___jp_154_;
}
}
else
{
lean_dec(v_minCoeff_148_);
v___y_155_ = v_a_133_;
goto v___jp_154_;
}
v___jp_154_:
{
lean_object* v___x_157_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 3, v___y_155_);
v___x_157_ = v___x_151_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_maxLowerCoeff_145_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_maxUpperCoeff_146_);
lean_ctor_set(v_reuseFailAlloc_159_, 2, v_maxDvdCoeff_147_);
lean_ctor_set(v_reuseFailAlloc_159_, 3, v___y_155_);
lean_ctor_set(v_reuseFailAlloc_159_, 4, v_penalty_149_);
v___x_157_ = v_reuseFailAlloc_159_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_158_; 
v___x_158_ = lean_array_fset(v_xs_x27_153_, v_x_134_, v___x_157_);
v___y_139_ = v___x_158_;
goto v___jp_138_;
}
}
}
}
v___jp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_137_);
lean_ctor_set(v___x_140_, 1, v___y_139_);
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin___redArg___boxed(lean_object* v_a_164_, lean_object* v_x_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin___redArg(v_a_164_, v_x_165_, v_a_166_);
lean_dec(v_x_165_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin(lean_object* v_a_169_, lean_object* v_x_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin___redArg(v_a_169_, v_x_170_, v_a_171_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin___boxed(lean_object* v_a_184_, lean_object* v_x_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin(v_a_184_, v_x_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec(v_a_188_);
lean_dec(v_a_187_);
lean_dec(v_x_185_);
return v_res_198_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = lean_nat_to_int(v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(lean_object* v_a_201_, lean_object* v_x_202_, lean_object* v_a_203_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v_a_207_; lean_object* v_snd_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_205_ = lean_nat_abs(v_a_201_);
lean_inc(v___x_205_);
v___x_206_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin___redArg(v___x_205_, v_x_202_, v_a_203_);
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref(v___x_206_);
v_snd_208_ = lean_ctor_get(v_a_207_, 1);
lean_inc(v_snd_208_);
lean_dec(v_a_207_);
v___x_209_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0);
v___x_210_ = lean_int_dec_lt(v_a_201_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; 
v___x_211_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v___x_205_, v_x_202_, v_snd_208_);
return v___x_211_;
}
else
{
lean_object* v___x_212_; 
v___x_212_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v___x_205_, v_x_202_, v_snd_208_);
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___boxed(lean_object* v_a_213_, lean_object* v_x_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_213_, v_x_214_, v_a_215_);
lean_dec(v_x_214_);
lean_dec(v_a_213_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(lean_object* v_a_218_, lean_object* v_x_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_218_, v_x_219_, v_a_220_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___boxed(lean_object* v_a_233_, lean_object* v_x_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(v_a_233_, v_x_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec(v_a_236_);
lean_dec(v_x_234_);
lean_dec(v_a_233_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(lean_object* v_a_248_, lean_object* v_x_249_, lean_object* v_a_250_){
_start:
{
lean_object* v___x_252_; lean_object* v___y_254_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_252_ = lean_box(0);
v___x_257_ = lean_array_get_size(v_a_250_);
v___x_258_ = lean_nat_dec_lt(v_x_249_, v___x_257_);
if (v___x_258_ == 0)
{
lean_dec(v_a_248_);
v___y_254_ = v_a_250_;
goto v___jp_253_;
}
else
{
lean_object* v_v_259_; lean_object* v_maxLowerCoeff_260_; lean_object* v_maxUpperCoeff_261_; lean_object* v_maxDvdCoeff_262_; lean_object* v_minCoeff_263_; lean_object* v_penalty_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_276_; 
v_v_259_ = lean_array_fget(v_a_250_, v_x_249_);
v_maxLowerCoeff_260_ = lean_ctor_get(v_v_259_, 0);
v_maxUpperCoeff_261_ = lean_ctor_get(v_v_259_, 1);
v_maxDvdCoeff_262_ = lean_ctor_get(v_v_259_, 2);
v_minCoeff_263_ = lean_ctor_get(v_v_259_, 3);
v_penalty_264_ = lean_ctor_get(v_v_259_, 4);
v_isSharedCheck_276_ = !lean_is_exclusive(v_v_259_);
if (v_isSharedCheck_276_ == 0)
{
v___x_266_ = v_v_259_;
v_isShared_267_ = v_isSharedCheck_276_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_penalty_264_);
lean_inc(v_minCoeff_263_);
lean_inc(v_maxDvdCoeff_262_);
lean_inc(v_maxUpperCoeff_261_);
lean_inc(v_maxLowerCoeff_260_);
lean_dec(v_v_259_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_276_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v_xs_x27_268_; lean_object* v___y_270_; uint8_t v___x_275_; 
v_xs_x27_268_ = lean_array_fset(v_a_250_, v_x_249_, v___x_252_);
v___x_275_ = lean_nat_dec_le(v_a_248_, v_maxDvdCoeff_262_);
if (v___x_275_ == 0)
{
lean_dec(v_maxDvdCoeff_262_);
v___y_270_ = v_a_248_;
goto v___jp_269_;
}
else
{
lean_dec(v_a_248_);
v___y_270_ = v_maxDvdCoeff_262_;
goto v___jp_269_;
}
v___jp_269_:
{
lean_object* v___x_272_; 
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 2, v___y_270_);
v___x_272_ = v___x_266_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_maxLowerCoeff_260_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_maxUpperCoeff_261_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v___y_270_);
lean_ctor_set(v_reuseFailAlloc_274_, 3, v_minCoeff_263_);
lean_ctor_set(v_reuseFailAlloc_274_, 4, v_penalty_264_);
v___x_272_ = v_reuseFailAlloc_274_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; 
v___x_273_ = lean_array_fset(v_xs_x27_268_, v_x_249_, v___x_272_);
v___y_254_ = v___x_273_;
goto v___jp_253_;
}
}
}
}
v___jp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_252_);
lean_ctor_set(v___x_255_, 1, v___y_254_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg___boxed(lean_object* v_a_277_, lean_object* v_x_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_277_, v_x_278_, v_a_279_);
lean_dec(v_x_278_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(lean_object* v_a_282_, lean_object* v_x_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_282_, v_x_283_, v_a_284_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___boxed(lean_object* v_a_297_, lean_object* v_x_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(v_a_297_, v_x_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec(v_a_300_);
lean_dec(v_x_298_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
if (lean_obj_tag(v_a_312_) == 0)
{
lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_323_; 
v_isSharedCheck_323_ = !lean_is_exclusive(v_a_312_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; 
v_unused_324_ = lean_ctor_get(v_a_312_, 0);
lean_dec(v_unused_324_);
v___x_316_ = v_a_312_;
v_isShared_317_ = v_isSharedCheck_323_;
goto v_resetjp_315_;
}
else
{
lean_dec(v_a_312_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_323_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_318_ = lean_box(0);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_a_313_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_319_);
v___x_321_ = v___x_316_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
else
{
lean_object* v_k_325_; lean_object* v_v_326_; lean_object* v_p_327_; lean_object* v___x_328_; lean_object* v_a_329_; lean_object* v_snd_330_; 
v_k_325_ = lean_ctor_get(v_a_312_, 0);
lean_inc(v_k_325_);
v_v_326_ = lean_ctor_get(v_a_312_, 1);
lean_inc(v_v_326_);
v_p_327_ = lean_ctor_get(v_a_312_, 2);
lean_inc_ref(v_p_327_);
lean_dec_ref_known(v_a_312_, 3);
v___x_328_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_k_325_, v_v_326_, v_a_313_);
lean_dec(v_v_326_);
lean_dec(v_k_325_);
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref(v___x_328_);
v_snd_330_ = lean_ctor_get(v_a_329_, 1);
lean_inc(v_snd_330_);
lean_dec(v_a_329_);
v_a_312_ = v_p_327_;
v_a_313_ = v_snd_330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg___boxed(lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_332_, v_a_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_336_, v_a_337_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___boxed(lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec(v_a_352_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3_spec__7___redArg(lean_object* v_keys_364_, lean_object* v_vals_365_, lean_object* v_i_366_, lean_object* v_k_367_){
_start:
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_array_get_size(v_keys_364_);
v___x_369_ = lean_nat_dec_lt(v_i_366_, v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
lean_dec(v_i_366_);
v___x_370_ = lean_box(0);
return v___x_370_;
}
else
{
lean_object* v_k_x27_371_; size_t v___x_372_; size_t v___x_373_; uint8_t v___x_374_; 
v_k_x27_371_ = lean_array_fget_borrowed(v_keys_364_, v_i_366_);
v___x_372_ = lean_ptr_addr(v_k_367_);
v___x_373_ = lean_ptr_addr(v_k_x27_371_);
v___x_374_ = lean_usize_dec_eq(v___x_372_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_nat_add(v_i_366_, v___x_375_);
lean_dec(v_i_366_);
v_i_366_ = v___x_376_;
goto _start;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_array_fget_borrowed(v_vals_365_, v_i_366_);
lean_dec(v_i_366_);
lean_inc(v___x_378_);
v___x_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
return v___x_379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_keys_380_, lean_object* v_vals_381_, lean_object* v_i_382_, lean_object* v_k_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3_spec__7___redArg(v_keys_380_, v_vals_381_, v_i_382_, v_k_383_);
lean_dec_ref(v_k_383_);
lean_dec_ref(v_vals_381_);
lean_dec_ref(v_keys_380_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3___redArg(lean_object* v_x_385_, size_t v_x_386_, lean_object* v_x_387_){
_start:
{
if (lean_obj_tag(v_x_385_) == 0)
{
lean_object* v_es_388_; lean_object* v___x_389_; size_t v___x_390_; size_t v___x_391_; lean_object* v_j_392_; lean_object* v___x_393_; 
v_es_388_ = lean_ctor_get(v_x_385_, 0);
v___x_389_ = lean_box(2);
v___x_390_ = ((size_t)31ULL);
v___x_391_ = lean_usize_land(v_x_386_, v___x_390_);
v_j_392_ = lean_usize_to_nat(v___x_391_);
v___x_393_ = lean_array_get_borrowed(v___x_389_, v_es_388_, v_j_392_);
lean_dec(v_j_392_);
switch(lean_obj_tag(v___x_393_))
{
case 0:
{
lean_object* v_key_394_; lean_object* v_val_395_; size_t v___x_396_; size_t v___x_397_; uint8_t v___x_398_; 
v_key_394_ = lean_ctor_get(v___x_393_, 0);
v_val_395_ = lean_ctor_get(v___x_393_, 1);
v___x_396_ = lean_ptr_addr(v_x_387_);
v___x_397_ = lean_ptr_addr(v_key_394_);
v___x_398_ = lean_usize_dec_eq(v___x_396_, v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
v___x_399_ = lean_box(0);
return v___x_399_;
}
else
{
lean_object* v___x_400_; 
lean_inc(v_val_395_);
v___x_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_400_, 0, v_val_395_);
return v___x_400_;
}
}
case 1:
{
lean_object* v_node_401_; size_t v___x_402_; size_t v___x_403_; 
v_node_401_ = lean_ctor_get(v___x_393_, 0);
v___x_402_ = ((size_t)5ULL);
v___x_403_ = lean_usize_shift_right(v_x_386_, v___x_402_);
v_x_385_ = v_node_401_;
v_x_386_ = v___x_403_;
goto _start;
}
default: 
{
lean_object* v___x_405_; 
v___x_405_ = lean_box(0);
return v___x_405_;
}
}
}
else
{
lean_object* v_ks_406_; lean_object* v_vs_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_ks_406_ = lean_ctor_get(v_x_385_, 0);
v_vs_407_ = lean_ctor_get(v_x_385_, 1);
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3_spec__7___redArg(v_ks_406_, v_vs_407_, v___x_408_, v_x_387_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3___redArg___boxed(lean_object* v_x_410_, lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
size_t v_x_41581__boxed_413_; lean_object* v_res_414_; 
v_x_41581__boxed_413_ = lean_unbox_usize(v_x_411_);
lean_dec(v_x_411_);
v_res_414_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3___redArg(v_x_410_, v_x_41581__boxed_413_, v_x_412_);
lean_dec_ref(v_x_412_);
lean_dec_ref(v_x_410_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
size_t v___x_417_; size_t v___x_418_; size_t v___x_419_; uint64_t v___x_420_; size_t v___x_421_; lean_object* v___x_422_; 
v___x_417_ = lean_ptr_addr(v_x_416_);
v___x_418_ = ((size_t)3ULL);
v___x_419_ = lean_usize_shift_right(v___x_417_, v___x_418_);
v___x_420_ = lean_usize_to_uint64(v___x_419_);
v___x_421_ = lean_uint64_to_usize(v___x_420_);
v___x_422_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3___redArg(v_x_415_, v___x_421_, v_x_416_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___boxed(lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_x_423_, v_x_424_);
lean_dec_ref(v_x_424_);
lean_dec_ref(v_x_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(lean_object* v_as_429_, size_t v_sz_430_, size_t v_i_431_, lean_object* v_b_432_, lean_object* v___y_433_){
_start:
{
uint8_t v___x_435_; 
v___x_435_ = lean_usize_dec_lt(v_i_431_, v_sz_430_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v_b_432_);
lean_ctor_set(v___x_436_, 1, v___y_433_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
else
{
lean_object* v_a_438_; lean_object* v_p_439_; lean_object* v___x_440_; 
lean_dec_ref(v_b_432_);
v_a_438_ = lean_array_uget_borrowed(v_as_429_, v_i_431_);
v_p_439_ = lean_ctor_get(v_a_438_, 0);
lean_inc_ref(v_p_439_);
v___x_440_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_439_, v___y_433_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v_snd_442_; lean_object* v___x_443_; size_t v___x_444_; size_t v___x_445_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v___x_440_, 1);
v_snd_442_ = lean_ctor_get(v_a_441_, 1);
lean_inc(v_snd_442_);
lean_dec(v_a_441_);
v___x_443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_444_ = ((size_t)1ULL);
v___x_445_ = lean_usize_add(v_i_431_, v___x_444_);
v_i_431_ = v___x_445_;
v_b_432_ = v___x_443_;
v___y_433_ = v_snd_442_;
goto _start;
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_a_447_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_440_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_440_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_as_455_, lean_object* v_sz_456_, lean_object* v_i_457_, lean_object* v_b_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
size_t v_sz_boxed_461_; size_t v_i_boxed_462_; lean_object* v_res_463_; 
v_sz_boxed_461_ = lean_unbox_usize(v_sz_456_);
lean_dec(v_sz_456_);
v_i_boxed_462_ = lean_unbox_usize(v_i_457_);
lean_dec(v_i_457_);
v_res_463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_455_, v_sz_boxed_461_, v_i_boxed_462_, v_b_458_, v___y_459_);
lean_dec_ref(v_as_455_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(lean_object* v_as_464_, size_t v_sz_465_, size_t v_i_466_, lean_object* v_b_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
uint8_t v___x_480_; 
v___x_480_ = lean_usize_dec_lt(v_i_466_, v_sz_465_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v_b_467_);
lean_ctor_set(v___x_481_, 1, v___y_468_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
else
{
lean_object* v_a_483_; lean_object* v_p_484_; lean_object* v___x_485_; 
lean_dec_ref(v_b_467_);
v_a_483_ = lean_array_uget_borrowed(v_as_464_, v_i_466_);
v_p_484_ = lean_ctor_get(v_a_483_, 0);
lean_inc_ref(v_p_484_);
v___x_485_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_484_, v___y_468_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v_snd_487_; lean_object* v___x_488_; size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
v_snd_487_ = lean_ctor_get(v_a_486_, 1);
lean_inc(v_snd_487_);
lean_dec(v_a_486_);
v___x_488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_add(v_i_466_, v___x_489_);
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_464_, v_sz_465_, v___x_490_, v___x_488_, v_snd_487_);
return v___x_491_;
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
v_a_492_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_485_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_485_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1___boxed(lean_object* v_as_500_, lean_object* v_sz_501_, lean_object* v_i_502_, lean_object* v_b_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
size_t v_sz_boxed_516_; size_t v_i_boxed_517_; lean_object* v_res_518_; 
v_sz_boxed_516_ = lean_unbox_usize(v_sz_501_);
lean_dec(v_sz_501_);
v_i_boxed_517_ = lean_unbox_usize(v_i_502_);
lean_dec(v_i_502_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_as_500_, v_sz_boxed_516_, v_i_boxed_517_, v_b_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v_as_500_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_522_, size_t v_sz_523_, size_t v_i_524_, lean_object* v_b_525_, lean_object* v___y_526_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = lean_usize_dec_lt(v_i_524_, v_sz_523_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_b_525_);
lean_ctor_set(v___x_529_, 1, v___y_526_);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
else
{
lean_object* v_a_531_; lean_object* v_p_532_; lean_object* v___x_533_; 
lean_dec_ref(v_b_525_);
v_a_531_ = lean_array_uget_borrowed(v_as_522_, v_i_524_);
v_p_532_ = lean_ctor_get(v_a_531_, 0);
lean_inc_ref(v_p_532_);
v___x_533_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_532_, v___y_526_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v_snd_535_; lean_object* v___x_536_; size_t v___x_537_; size_t v___x_538_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_533_, 1);
v_snd_535_ = lean_ctor_get(v_a_534_, 1);
lean_inc(v_snd_535_);
lean_dec(v_a_534_);
v___x_536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5___redArg___closed__0));
v___x_537_ = ((size_t)1ULL);
v___x_538_ = lean_usize_add(v_i_524_, v___x_537_);
v_i_524_ = v___x_538_;
v_b_525_ = v___x_536_;
v___y_526_ = v_snd_535_;
goto _start;
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
v_a_540_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_533_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_533_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_548_, lean_object* v_sz_549_, lean_object* v_i_550_, lean_object* v_b_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
size_t v_sz_boxed_554_; size_t v_i_boxed_555_; lean_object* v_res_556_; 
v_sz_boxed_554_ = lean_unbox_usize(v_sz_549_);
lean_dec(v_sz_549_);
v_i_boxed_555_ = lean_unbox_usize(v_i_550_);
lean_dec(v_i_550_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5___redArg(v_as_548_, v_sz_boxed_554_, v_i_boxed_555_, v_b_551_, v___y_552_);
lean_dec_ref(v_as_548_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(lean_object* v_as_557_, size_t v_sz_558_, size_t v_i_559_, lean_object* v_b_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
uint8_t v___x_573_; 
v___x_573_ = lean_usize_dec_lt(v_i_559_, v_sz_558_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v_b_560_);
lean_ctor_set(v___x_574_, 1, v___y_561_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
else
{
lean_object* v_a_576_; lean_object* v_p_577_; lean_object* v___x_578_; 
lean_dec_ref(v_b_560_);
v_a_576_ = lean_array_uget_borrowed(v_as_557_, v_i_559_);
v_p_577_ = lean_ctor_get(v_a_576_, 0);
lean_inc_ref(v_p_577_);
v___x_578_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_577_, v___y_561_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v_snd_580_; lean_object* v___x_581_; size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
v_snd_580_ = lean_ctor_get(v_a_579_, 1);
lean_inc(v_snd_580_);
lean_dec(v_a_579_);
v___x_581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5___redArg___closed__0));
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_add(v_i_559_, v___x_582_);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5___redArg(v_as_557_, v_sz_558_, v___x_583_, v___x_581_, v_snd_580_);
return v___x_584_;
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
v_a_585_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_578_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_578_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2___boxed(lean_object* v_as_593_, lean_object* v_sz_594_, lean_object* v_i_595_, lean_object* v_b_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
size_t v_sz_boxed_609_; size_t v_i_boxed_610_; lean_object* v_res_611_; 
v_sz_boxed_609_ = lean_unbox_usize(v_sz_594_);
lean_dec(v_sz_594_);
v_i_boxed_610_ = lean_unbox_usize(v_i_595_);
lean_dec(v_i_595_);
v_res_611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_as_593_, v_sz_boxed_609_, v_i_boxed_610_, v_b_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v_as_593_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(lean_object* v_init_612_, lean_object* v_n_613_, lean_object* v_b_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
if (lean_obj_tag(v_n_613_) == 0)
{
lean_object* v_cs_627_; lean_object* v___x_628_; lean_object* v___x_629_; size_t v_sz_630_; size_t v___x_631_; lean_object* v___x_632_; 
v_cs_627_ = lean_ctor_get(v_n_613_, 0);
v___x_628_ = lean_box(0);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_b_614_);
v_sz_630_ = lean_array_size(v_cs_627_);
v___x_631_ = ((size_t)0ULL);
v___x_632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_612_, v_cs_627_, v_sz_630_, v___x_631_, v___x_629_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_667_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_667_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_667_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_667_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_fst_637_; lean_object* v_fst_638_; 
v_fst_637_ = lean_ctor_get(v_a_633_, 0);
lean_inc(v_fst_637_);
v_fst_638_ = lean_ctor_get(v_fst_637_, 0);
if (lean_obj_tag(v_fst_638_) == 0)
{
lean_object* v_snd_639_; lean_object* v_snd_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_651_; 
v_snd_639_ = lean_ctor_get(v_a_633_, 1);
lean_inc(v_snd_639_);
lean_dec(v_a_633_);
v_snd_640_ = lean_ctor_get(v_fst_637_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_fst_637_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v_fst_637_, 0);
lean_dec(v_unused_652_);
v___x_642_ = v_fst_637_;
v_isShared_643_ = v_isSharedCheck_651_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_snd_640_);
lean_dec(v_fst_637_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_651_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v_snd_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v_snd_639_);
lean_ctor_set(v___x_642_, 0, v___x_644_);
v___x_646_ = v___x_642_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_snd_639_);
v___x_646_ = v_reuseFailAlloc_650_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_648_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_646_);
v___x_648_ = v___x_635_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_664_; 
lean_inc_ref(v_fst_638_);
v_isSharedCheck_664_ = !lean_is_exclusive(v_fst_637_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; lean_object* v_unused_666_; 
v_unused_665_ = lean_ctor_get(v_fst_637_, 1);
lean_dec(v_unused_665_);
v_unused_666_ = lean_ctor_get(v_fst_637_, 0);
lean_dec(v_unused_666_);
v___x_654_ = v_fst_637_;
v_isShared_655_ = v_isSharedCheck_664_;
goto v_resetjp_653_;
}
else
{
lean_dec(v_fst_637_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_664_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_snd_656_; lean_object* v_val_657_; lean_object* v___x_659_; 
v_snd_656_ = lean_ctor_get(v_a_633_, 1);
lean_inc(v_snd_656_);
lean_dec(v_a_633_);
v_val_657_ = lean_ctor_get(v_fst_638_, 0);
lean_inc(v_val_657_);
lean_dec_ref_known(v_fst_638_, 1);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v_snd_656_);
lean_ctor_set(v___x_654_, 0, v_val_657_);
v___x_659_ = v___x_654_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_val_657_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_snd_656_);
v___x_659_ = v_reuseFailAlloc_663_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_661_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_659_);
v___x_661_ = v___x_635_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
v_a_668_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_632_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_632_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
lean_object* v_vs_676_; lean_object* v___x_677_; lean_object* v___x_678_; size_t v_sz_679_; size_t v___x_680_; lean_object* v___x_681_; 
v_vs_676_ = lean_ctor_get(v_n_613_, 0);
v___x_677_ = lean_box(0);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v_b_614_);
v_sz_679_ = lean_array_size(v_vs_676_);
v___x_680_ = ((size_t)0ULL);
v___x_681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_vs_676_, v_sz_679_, v___x_680_, v___x_678_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_716_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_716_ == 0)
{
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_716_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_716_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v_fst_686_; lean_object* v_fst_687_; 
v_fst_686_ = lean_ctor_get(v_a_682_, 0);
lean_inc(v_fst_686_);
v_fst_687_ = lean_ctor_get(v_fst_686_, 0);
if (lean_obj_tag(v_fst_687_) == 0)
{
lean_object* v_snd_688_; lean_object* v_snd_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_700_; 
v_snd_688_ = lean_ctor_get(v_a_682_, 1);
lean_inc(v_snd_688_);
lean_dec(v_a_682_);
v_snd_689_ = lean_ctor_get(v_fst_686_, 1);
v_isSharedCheck_700_ = !lean_is_exclusive(v_fst_686_);
if (v_isSharedCheck_700_ == 0)
{
lean_object* v_unused_701_; 
v_unused_701_ = lean_ctor_get(v_fst_686_, 0);
lean_dec(v_unused_701_);
v___x_691_ = v_fst_686_;
v_isShared_692_ = v_isSharedCheck_700_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_snd_689_);
lean_dec(v_fst_686_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_700_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v_snd_689_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v_snd_688_);
lean_ctor_set(v___x_691_, 0, v___x_693_);
v___x_695_ = v___x_691_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_snd_688_);
v___x_695_ = v_reuseFailAlloc_699_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_697_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_695_);
v___x_697_ = v___x_684_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
else
{
lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_713_; 
lean_inc_ref(v_fst_687_);
v_isSharedCheck_713_ = !lean_is_exclusive(v_fst_686_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; lean_object* v_unused_715_; 
v_unused_714_ = lean_ctor_get(v_fst_686_, 1);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_fst_686_, 0);
lean_dec(v_unused_715_);
v___x_703_ = v_fst_686_;
v_isShared_704_ = v_isSharedCheck_713_;
goto v_resetjp_702_;
}
else
{
lean_dec(v_fst_686_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_713_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_snd_705_; lean_object* v_val_706_; lean_object* v___x_708_; 
v_snd_705_ = lean_ctor_get(v_a_682_, 1);
lean_inc(v_snd_705_);
lean_dec(v_a_682_);
v_val_706_ = lean_ctor_get(v_fst_687_, 0);
lean_inc(v_val_706_);
lean_dec_ref_known(v_fst_687_, 1);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v_snd_705_);
lean_ctor_set(v___x_703_, 0, v_val_706_);
v___x_708_ = v___x_703_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_val_706_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_snd_705_);
v___x_708_ = v_reuseFailAlloc_712_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_710_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_708_);
v___x_710_ = v___x_684_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
v_a_717_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_681_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_681_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(lean_object* v_init_725_, lean_object* v_as_726_, size_t v_sz_727_, size_t v_i_728_, lean_object* v_b_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
uint8_t v___x_742_; 
v___x_742_ = lean_usize_dec_lt(v_i_728_, v_sz_727_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v_b_729_);
lean_ctor_set(v___x_743_, 1, v___y_730_);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
else
{
lean_object* v_snd_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_795_; 
v_snd_745_ = lean_ctor_get(v_b_729_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_b_729_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v_b_729_, 0);
lean_dec(v_unused_796_);
v___x_747_ = v_b_729_;
v_isShared_748_ = v_isSharedCheck_795_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_snd_745_);
lean_dec(v_b_729_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_795_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v_a_750_; lean_object* v___x_751_; 
v___x_749_ = lean_box(0);
v_a_750_ = lean_array_uget_borrowed(v_as_726_, v_i_728_);
lean_inc(v_snd_745_);
v___x_751_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_725_, v_a_750_, v_snd_745_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_786_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_786_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_786_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_786_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_fst_756_; 
v_fst_756_ = lean_ctor_get(v_a_752_, 0);
lean_inc(v_fst_756_);
if (lean_obj_tag(v_fst_756_) == 0)
{
lean_object* v_snd_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_771_; 
v_snd_757_ = lean_ctor_get(v_a_752_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v_a_752_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v_a_752_, 0);
lean_dec(v_unused_772_);
v___x_759_ = v_a_752_;
v_isShared_760_ = v_isSharedCheck_771_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_snd_757_);
lean_dec(v_a_752_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_771_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v_fst_756_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 1, v_snd_745_);
lean_ctor_set(v___x_759_, 0, v___x_761_);
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_snd_745_);
v___x_763_ = v_reuseFailAlloc_770_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_765_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v_snd_757_);
lean_ctor_set(v___x_747_, 0, v___x_763_);
v___x_765_ = v___x_747_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_snd_757_);
v___x_765_ = v_reuseFailAlloc_769_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_767_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_765_);
v___x_767_ = v___x_754_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
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
}
else
{
lean_object* v_snd_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_784_; 
lean_del_object(v___x_754_);
lean_del_object(v___x_747_);
lean_dec(v_snd_745_);
v_snd_773_ = lean_ctor_get(v_a_752_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v_a_752_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; 
v_unused_785_ = lean_ctor_get(v_a_752_, 0);
lean_dec(v_unused_785_);
v___x_775_ = v_a_752_;
v_isShared_776_ = v_isSharedCheck_784_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_snd_773_);
lean_dec(v_a_752_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_784_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_a_777_; lean_object* v___x_779_; 
v_a_777_ = lean_ctor_get(v_fst_756_, 0);
lean_inc(v_a_777_);
lean_dec_ref_known(v_fst_756_, 1);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v_a_777_);
lean_ctor_set(v___x_775_, 0, v___x_749_);
v___x_779_ = v___x_775_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_a_777_);
v___x_779_ = v_reuseFailAlloc_783_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
size_t v___x_780_; size_t v___x_781_; 
v___x_780_ = ((size_t)1ULL);
v___x_781_ = lean_usize_add(v_i_728_, v___x_780_);
v_i_728_ = v___x_781_;
v_b_729_ = v___x_779_;
v___y_730_ = v_snd_773_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_del_object(v___x_747_);
lean_dec(v_snd_745_);
v_a_787_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_751_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_751_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_797_ = _args[0];
lean_object* v_as_798_ = _args[1];
lean_object* v_sz_799_ = _args[2];
lean_object* v_i_800_ = _args[3];
lean_object* v_b_801_ = _args[4];
lean_object* v___y_802_ = _args[5];
lean_object* v___y_803_ = _args[6];
lean_object* v___y_804_ = _args[7];
lean_object* v___y_805_ = _args[8];
lean_object* v___y_806_ = _args[9];
lean_object* v___y_807_ = _args[10];
lean_object* v___y_808_ = _args[11];
lean_object* v___y_809_ = _args[12];
lean_object* v___y_810_ = _args[13];
lean_object* v___y_811_ = _args[14];
lean_object* v___y_812_ = _args[15];
lean_object* v___y_813_ = _args[16];
_start:
{
size_t v_sz_boxed_814_; size_t v_i_boxed_815_; lean_object* v_res_816_; 
v_sz_boxed_814_ = lean_unbox_usize(v_sz_799_);
lean_dec(v_sz_799_);
v_i_boxed_815_ = lean_unbox_usize(v_i_800_);
lean_dec(v_i_800_);
v_res_816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_797_, v_as_798_, v_sz_boxed_814_, v_i_boxed_815_, v_b_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v_as_798_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0___boxed(lean_object* v_init_817_, lean_object* v_n_818_, lean_object* v_b_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_817_, v_n_818_, v_b_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec(v___y_821_);
lean_dec_ref(v_n_818_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(lean_object* v_t_833_, lean_object* v_init_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_b_848_; lean_object* v___y_849_; lean_object* v_root_852_; lean_object* v_tail_853_; lean_object* v___x_854_; 
v_root_852_ = lean_ctor_get(v_t_833_, 0);
v_tail_853_ = lean_ctor_get(v_t_833_, 1);
v___x_854_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_834_, v_root_852_, v_init_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v_fst_856_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v_fst_856_ = lean_ctor_get(v_a_855_, 0);
lean_inc(v_fst_856_);
if (lean_obj_tag(v_fst_856_) == 0)
{
lean_object* v_snd_857_; lean_object* v_a_858_; 
v_snd_857_ = lean_ctor_get(v_a_855_, 1);
lean_inc(v_snd_857_);
lean_dec(v_a_855_);
v_a_858_ = lean_ctor_get(v_fst_856_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v_fst_856_, 1);
v_b_848_ = v_a_858_;
v___y_849_ = v_snd_857_;
goto v___jp_847_;
}
else
{
lean_object* v_snd_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_901_; 
v_snd_859_ = lean_ctor_get(v_a_855_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v_a_855_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; 
v_unused_902_ = lean_ctor_get(v_a_855_, 0);
lean_dec(v_unused_902_);
v___x_861_ = v_a_855_;
v_isShared_862_ = v_isSharedCheck_901_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_snd_859_);
lean_dec(v_a_855_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_901_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_a_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v_a_863_ = lean_ctor_get(v_fst_856_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v_fst_856_, 1);
v___x_864_ = lean_box(0);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v_a_863_);
lean_ctor_set(v___x_861_, 0, v___x_864_);
v___x_866_ = v___x_861_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_a_863_);
v___x_866_ = v_reuseFailAlloc_900_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
size_t v_sz_867_; size_t v___x_868_; lean_object* v___x_869_; 
v_sz_867_ = lean_array_size(v_tail_853_);
v___x_868_ = ((size_t)0ULL);
v___x_869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_tail_853_, v_sz_867_, v___x_868_, v___x_866_, v_snd_859_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_891_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_891_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_891_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_891_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v_fst_874_; lean_object* v_fst_875_; 
v_fst_874_ = lean_ctor_get(v_a_870_, 0);
lean_inc(v_fst_874_);
v_fst_875_ = lean_ctor_get(v_fst_874_, 0);
if (lean_obj_tag(v_fst_875_) == 0)
{
lean_object* v_snd_876_; lean_object* v_snd_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_887_; 
v_snd_876_ = lean_ctor_get(v_a_870_, 1);
lean_inc(v_snd_876_);
lean_dec(v_a_870_);
v_snd_877_ = lean_ctor_get(v_fst_874_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_fst_874_);
if (v_isSharedCheck_887_ == 0)
{
lean_object* v_unused_888_; 
v_unused_888_ = lean_ctor_get(v_fst_874_, 0);
lean_dec(v_unused_888_);
v___x_879_ = v_fst_874_;
v_isShared_880_ = v_isSharedCheck_887_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_snd_877_);
lean_dec(v_fst_874_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_887_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 1, v_snd_876_);
lean_ctor_set(v___x_879_, 0, v_snd_877_);
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_snd_877_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_snd_876_);
v___x_882_ = v_reuseFailAlloc_886_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_882_);
v___x_884_ = v___x_872_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
lean_object* v_snd_889_; lean_object* v_val_890_; 
lean_inc_ref(v_fst_875_);
lean_dec(v_fst_874_);
lean_del_object(v___x_872_);
v_snd_889_ = lean_ctor_get(v_a_870_, 1);
lean_inc(v_snd_889_);
lean_dec(v_a_870_);
v_val_890_ = lean_ctor_get(v_fst_875_, 0);
lean_inc(v_val_890_);
lean_dec_ref_known(v_fst_875_, 1);
v_b_848_ = v_val_890_;
v___y_849_ = v_snd_889_;
goto v___jp_847_;
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v_a_892_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_869_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_869_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
v_a_903_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_854_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_854_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
v___jp_847_:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v_b_848_);
lean_ctor_set(v___x_850_, 1, v___y_849_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0___boxed(lean_object* v_t_911_, lean_object* v_init_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v_t_911_, v_init_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v_t_911_);
return v_res_925_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg___lam__0(lean_object* v_xs_926_, lean_object* v_i_927_){
_start:
{
lean_object* v_size_928_; uint8_t v___x_929_; 
v_size_928_ = lean_ctor_get(v_xs_926_, 2);
v___x_929_ = lean_nat_dec_lt(v_i_927_, v_size_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg___lam__0___boxed(lean_object* v_xs_930_, lean_object* v_i_931_){
_start:
{
uint8_t v_res_932_; lean_object* v_r_933_; 
v_res_932_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg___lam__0(v_xs_930_, v_i_931_);
lean_dec(v_i_931_);
lean_dec_ref(v_xs_930_);
v_r_933_ = lean_box(v_res_932_);
return v_r_933_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg(lean_object* v_a_935_, lean_object* v___x_936_, lean_object* v_range_937_, lean_object* v_b_938_, lean_object* v_i_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_stop_952_; lean_object* v_step_953_; uint8_t v___x_954_; 
v_stop_952_ = lean_ctor_get(v_range_937_, 1);
v_step_953_ = lean_ctor_get(v_range_937_, 2);
v___x_954_ = lean_nat_dec_lt(v_i_939_, v_stop_952_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec(v_i_939_);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v_b_938_);
lean_ctor_set(v___x_955_, 1, v___y_940_);
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
else
{
lean_object* v_dvds_957_; lean_object* v_lowers_958_; lean_object* v_uppers_959_; lean_object* v_penalties_960_; lean_object* v_size_961_; lean_object* v___x_962_; lean_object* v_snd_964_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___x_976_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___x_997_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1044_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v_dvds_957_ = lean_ctor_get(v_a_935_, 5);
v_lowers_958_ = lean_ctor_get(v_a_935_, 6);
v_uppers_959_ = lean_ctor_get(v_a_935_, 7);
v_penalties_960_ = lean_ctor_get(v_a_935_, 16);
v_size_961_ = lean_ctor_get(v___x_936_, 2);
v___x_962_ = lean_box(0);
v___x_976_ = lean_box(0);
v___x_997_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg___closed__0);
v___x_1064_ = l_Lean_instInhabitedExpr;
v___x_1065_ = lean_nat_dec_lt(v_i_939_, v_size_961_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
v___x_1066_ = l_outOfBounds___redArg(v___x_1064_);
v___y_1044_ = v___x_1066_;
goto v___jp_1043_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1064_, v___x_936_, v_i_939_);
v___y_1044_ = v___x_1067_;
goto v___jp_1043_;
}
v___jp_963_:
{
lean_object* v___x_965_; 
v___x_965_ = lean_nat_add(v_i_939_, v_step_953_);
lean_dec(v_i_939_);
v_b_938_ = v___x_962_;
v_i_939_ = v___x_965_;
v___y_940_ = v_snd_964_;
goto _start;
}
v___jp_967_:
{
if (lean_obj_tag(v___y_969_) == 1)
{
lean_object* v_val_970_; lean_object* v_d_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v_a_974_; lean_object* v_snd_975_; 
v_val_970_ = lean_ctor_get(v___y_969_, 0);
lean_inc(v_val_970_);
lean_dec_ref_known(v___y_969_, 1);
v_d_971_ = lean_ctor_get(v_val_970_, 0);
lean_inc(v_d_971_);
lean_dec(v_val_970_);
v___x_972_ = lean_nat_abs(v_d_971_);
lean_dec(v_d_971_);
v___x_973_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v___x_972_, v_i_939_, v___y_968_);
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref(v___x_973_);
v_snd_975_ = lean_ctor_get(v_a_974_, 1);
lean_inc(v_snd_975_);
lean_dec(v_a_974_);
v_snd_964_ = v_snd_975_;
goto v___jp_963_;
}
else
{
lean_dec(v___y_969_);
v_snd_964_ = v___y_968_;
goto v___jp_963_;
}
}
v___jp_977_:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v___y_989_, v___x_962_, v___y_983_, v___y_987_, v___y_985_, v___y_982_, v___y_988_, v___y_986_, v___y_984_, v___y_981_, v___y_980_, v___y_979_, v___y_978_);
lean_dec_ref(v___y_989_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v_snd_992_; lean_object* v_size_993_; uint8_t v___x_994_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
v_snd_992_ = lean_ctor_get(v_a_991_, 1);
lean_inc(v_snd_992_);
lean_dec(v_a_991_);
v_size_993_ = lean_ctor_get(v_dvds_957_, 2);
v___x_994_ = lean_nat_dec_lt(v_i_939_, v_size_993_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; 
v___x_995_ = l_outOfBounds___redArg(v___x_976_);
v___y_968_ = v_snd_992_;
v___y_969_ = v___x_995_;
goto v___jp_967_;
}
else
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_PersistentArray_get_x21___redArg(v___x_976_, v_dvds_957_, v_i_939_);
v___y_968_ = v_snd_992_;
v___y_969_ = v___x_996_;
goto v___jp_967_;
}
}
else
{
lean_dec(v_i_939_);
return v___x_990_;
}
}
v___jp_998_:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v___y_1010_, v___x_962_, v___y_1007_, v___y_1008_, v___y_1005_, v___y_1003_, v___y_1009_, v___y_1006_, v___y_1004_, v___y_1002_, v___y_1001_, v___y_1000_, v___y_999_);
lean_dec_ref(v___y_1010_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v_snd_1013_; uint8_t v___x_1014_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v_snd_1013_ = lean_ctor_get(v_a_1012_, 1);
lean_inc(v_snd_1013_);
lean_dec(v_a_1012_);
v___x_1014_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg___lam__0(v_uppers_959_, v_i_939_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; 
v___x_1015_ = l_outOfBounds___redArg(v___x_997_);
v___y_978_ = v___y_999_;
v___y_979_ = v___y_1000_;
v___y_980_ = v___y_1001_;
v___y_981_ = v___y_1002_;
v___y_982_ = v___y_1003_;
v___y_983_ = v_snd_1013_;
v___y_984_ = v___y_1004_;
v___y_985_ = v___y_1005_;
v___y_986_ = v___y_1006_;
v___y_987_ = v___y_1008_;
v___y_988_ = v___y_1009_;
v___y_989_ = v___x_1015_;
goto v___jp_977_;
}
else
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_PersistentArray_get_x21___redArg(v___x_997_, v_uppers_959_, v_i_939_);
v___y_978_ = v___y_999_;
v___y_979_ = v___y_1000_;
v___y_980_ = v___y_1001_;
v___y_981_ = v___y_1002_;
v___y_982_ = v___y_1003_;
v___y_983_ = v_snd_1013_;
v___y_984_ = v___y_1004_;
v___y_985_ = v___y_1005_;
v___y_986_ = v___y_1006_;
v___y_987_ = v___y_1008_;
v___y_988_ = v___y_1009_;
v___y_989_ = v___x_1016_;
goto v___jp_977_;
}
}
else
{
lean_dec(v_i_939_);
return v___x_1011_;
}
}
v___jp_1017_:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_i_939_, v___y_1019_, v___y_1027_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; uint8_t v___x_1031_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___x_1029_, 1);
v___x_1031_ = lean_unbox(v_a_1030_);
lean_dec(v_a_1030_);
if (v___x_1031_ == 0)
{
uint8_t v___x_1032_; 
v___x_1032_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg___lam__0(v_lowers_958_, v_i_939_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
v___x_1033_ = l_outOfBounds___redArg(v___x_997_);
v___y_999_ = v___y_1028_;
v___y_1000_ = v___y_1027_;
v___y_1001_ = v___y_1026_;
v___y_1002_ = v___y_1025_;
v___y_1003_ = v___y_1021_;
v___y_1004_ = v___y_1024_;
v___y_1005_ = v___y_1020_;
v___y_1006_ = v___y_1023_;
v___y_1007_ = v___y_1018_;
v___y_1008_ = v___y_1019_;
v___y_1009_ = v___y_1022_;
v___y_1010_ = v___x_1033_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_PersistentArray_get_x21___redArg(v___x_997_, v_lowers_958_, v_i_939_);
v___y_999_ = v___y_1028_;
v___y_1000_ = v___y_1027_;
v___y_1001_ = v___y_1026_;
v___y_1002_ = v___y_1025_;
v___y_1003_ = v___y_1021_;
v___y_1004_ = v___y_1024_;
v___y_1005_ = v___y_1020_;
v___y_1006_ = v___y_1023_;
v___y_1007_ = v___y_1018_;
v___y_1008_ = v___y_1019_;
v___y_1009_ = v___y_1022_;
v___y_1010_ = v___x_1034_;
goto v___jp_998_;
}
}
else
{
v_snd_964_ = v___y_1018_;
goto v___jp_963_;
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec_ref(v___y_1018_);
lean_dec(v_i_939_);
v_a_1035_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1029_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1029_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
v___jp_1043_:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_penalties_960_, v___y_1044_);
lean_dec_ref(v___y_1044_);
if (lean_obj_tag(v___x_1045_) == 1)
{
lean_object* v_val_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_val_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_val_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v___x_1047_ = lean_array_get_size(v___y_940_);
v___x_1048_ = lean_nat_dec_lt(v_i_939_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_dec(v_val_1046_);
v___y_1018_ = v___y_940_;
v___y_1019_ = v___y_941_;
v___y_1020_ = v___y_942_;
v___y_1021_ = v___y_943_;
v___y_1022_ = v___y_944_;
v___y_1023_ = v___y_945_;
v___y_1024_ = v___y_946_;
v___y_1025_ = v___y_947_;
v___y_1026_ = v___y_948_;
v___y_1027_ = v___y_949_;
v___y_1028_ = v___y_950_;
goto v___jp_1017_;
}
else
{
lean_object* v_v_1049_; lean_object* v_maxLowerCoeff_1050_; lean_object* v_maxUpperCoeff_1051_; lean_object* v_maxDvdCoeff_1052_; lean_object* v_minCoeff_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1062_; 
v_v_1049_ = lean_array_fget(v___y_940_, v_i_939_);
v_maxLowerCoeff_1050_ = lean_ctor_get(v_v_1049_, 0);
v_maxUpperCoeff_1051_ = lean_ctor_get(v_v_1049_, 1);
v_maxDvdCoeff_1052_ = lean_ctor_get(v_v_1049_, 2);
v_minCoeff_1053_ = lean_ctor_get(v_v_1049_, 3);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_v_1049_);
if (v_isSharedCheck_1062_ == 0)
{
lean_object* v_unused_1063_; 
v_unused_1063_ = lean_ctor_get(v_v_1049_, 4);
lean_dec(v_unused_1063_);
v___x_1055_ = v_v_1049_;
v_isShared_1056_ = v_isSharedCheck_1062_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_minCoeff_1053_);
lean_inc(v_maxDvdCoeff_1052_);
lean_inc(v_maxUpperCoeff_1051_);
lean_inc(v_maxLowerCoeff_1050_);
lean_dec(v_v_1049_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1062_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_xs_x27_1057_; lean_object* v___x_1059_; 
v_xs_x27_1057_ = lean_array_fset(v___y_940_, v_i_939_, v___x_962_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 4, v_val_1046_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_maxLowerCoeff_1050_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_maxUpperCoeff_1051_);
lean_ctor_set(v_reuseFailAlloc_1061_, 2, v_maxDvdCoeff_1052_);
lean_ctor_set(v_reuseFailAlloc_1061_, 3, v_minCoeff_1053_);
lean_ctor_set(v_reuseFailAlloc_1061_, 4, v_val_1046_);
v___x_1059_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_array_fset(v_xs_x27_1057_, v_i_939_, v___x_1059_);
v___y_1018_ = v___x_1060_;
v___y_1019_ = v___y_941_;
v___y_1020_ = v___y_942_;
v___y_1021_ = v___y_943_;
v___y_1022_ = v___y_944_;
v___y_1023_ = v___y_945_;
v___y_1024_ = v___y_946_;
v___y_1025_ = v___y_947_;
v___y_1026_ = v___y_948_;
v___y_1027_ = v___y_949_;
v___y_1028_ = v___y_950_;
goto v___jp_1017_;
}
}
}
}
else
{
lean_dec(v___x_1045_);
v___y_1018_ = v___y_940_;
v___y_1019_ = v___y_941_;
v___y_1020_ = v___y_942_;
v___y_1021_ = v___y_943_;
v___y_1022_ = v___y_944_;
v___y_1023_ = v___y_945_;
v___y_1024_ = v___y_946_;
v___y_1025_ = v___y_947_;
v___y_1026_ = v___y_948_;
v___y_1027_ = v___y_949_;
v___y_1028_ = v___y_950_;
goto v___jp_1017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg___boxed(lean_object** _args){
lean_object* v_a_1068_ = _args[0];
lean_object* v___x_1069_ = _args[1];
lean_object* v_range_1070_ = _args[2];
lean_object* v_b_1071_ = _args[3];
lean_object* v_i_1072_ = _args[4];
lean_object* v___y_1073_ = _args[5];
lean_object* v___y_1074_ = _args[6];
lean_object* v___y_1075_ = _args[7];
lean_object* v___y_1076_ = _args[8];
lean_object* v___y_1077_ = _args[9];
lean_object* v___y_1078_ = _args[10];
lean_object* v___y_1079_ = _args[11];
lean_object* v___y_1080_ = _args[12];
lean_object* v___y_1081_ = _args[13];
lean_object* v___y_1082_ = _args[14];
lean_object* v___y_1083_ = _args[15];
lean_object* v___y_1084_ = _args[16];
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg(v_a_1068_, v___x_1069_, v_range_1070_, v_b_1071_, v_i_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v_range_1070_);
lean_dec_ref(v___x_1069_);
lean_dec_ref(v_a_1068_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1087_, v_a_1095_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v_vars_1100_; lean_object* v_size_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1098_, 1);
v_vars_1100_ = lean_ctor_get(v_a_1099_, 0);
lean_inc_ref(v_vars_1100_);
v_size_1101_ = lean_ctor_get(v_vars_1100_, 2);
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = lean_unsigned_to_nat(1u);
lean_inc(v_size_1101_);
v___x_1104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v_size_1101_);
lean_ctor_set(v___x_1104_, 2, v___x_1103_);
v___x_1105_ = lean_box(0);
v___x_1106_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg(v_a_1099_, v_vars_1100_, v___x_1104_, v___x_1105_, v___x_1102_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
lean_dec_ref_known(v___x_1104_, 3);
lean_dec_ref(v_vars_1100_);
lean_dec(v_a_1099_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1123_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1123_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1123_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_snd_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1121_; 
v_snd_1111_ = lean_ctor_get(v_a_1107_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_a_1107_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v_a_1107_, 0);
lean_dec(v_unused_1122_);
v___x_1113_ = v_a_1107_;
v_isShared_1114_ = v_isSharedCheck_1121_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_snd_1111_);
lean_dec(v_a_1107_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1121_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1105_);
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_snd_1111_);
v___x_1116_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1118_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1116_);
v___x_1118_ = v___x_1109_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
else
{
return v___x_1106_;
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec_ref(v_a_1086_);
v_a_1124_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1098_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1098_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go___boxed(lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec(v_a_1133_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(lean_object* v_00_u03b2_1145_, lean_object* v_x_1146_, lean_object* v_x_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_x_1146_, v_x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___boxed(lean_object* v_00_u03b2_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(v_00_u03b2_1149_, v_x_1150_, v_x_1151_);
lean_dec_ref(v_x_1151_);
lean_dec_ref(v_x_1150_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2(lean_object* v_a_1153_, lean_object* v___x_1154_, lean_object* v_range_1155_, lean_object* v_b_1156_, lean_object* v_i_1157_, lean_object* v_hs_1158_, lean_object* v_hl_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___redArg(v_a_1153_, v___x_1154_, v_range_1155_, v_b_1156_, v_i_1157_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2___boxed(lean_object** _args){
lean_object* v_a_1173_ = _args[0];
lean_object* v___x_1174_ = _args[1];
lean_object* v_range_1175_ = _args[2];
lean_object* v_b_1176_ = _args[3];
lean_object* v_i_1177_ = _args[4];
lean_object* v_hs_1178_ = _args[5];
lean_object* v_hl_1179_ = _args[6];
lean_object* v___y_1180_ = _args[7];
lean_object* v___y_1181_ = _args[8];
lean_object* v___y_1182_ = _args[9];
lean_object* v___y_1183_ = _args[10];
lean_object* v___y_1184_ = _args[11];
lean_object* v___y_1185_ = _args[12];
lean_object* v___y_1186_ = _args[13];
lean_object* v___y_1187_ = _args[14];
lean_object* v___y_1188_ = _args[15];
lean_object* v___y_1189_ = _args[16];
lean_object* v___y_1190_ = _args[17];
lean_object* v___y_1191_ = _args[18];
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__2(v_a_1173_, v___x_1174_, v_range_1175_, v_b_1176_, v_i_1177_, v_hs_1178_, v_hl_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v_range_1175_);
lean_dec_ref(v___x_1174_);
lean_dec_ref(v_a_1173_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3(lean_object* v_00_u03b2_1193_, lean_object* v_x_1194_, size_t v_x_1195_, lean_object* v_x_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3___redArg(v_x_1194_, v_x_1195_, v_x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1198_, lean_object* v_x_1199_, lean_object* v_x_1200_, lean_object* v_x_1201_){
_start:
{
size_t v_x_42803__boxed_1202_; lean_object* v_res_1203_; 
v_x_42803__boxed_1202_ = lean_unbox_usize(v_x_1200_);
lean_dec(v_x_1200_);
v_res_1203_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3(v_00_u03b2_1198_, v_x_1199_, v_x_42803__boxed_1202_, v_x_1201_);
lean_dec_ref(v_x_1201_);
lean_dec_ref(v_x_1199_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(lean_object* v_as_1204_, size_t v_sz_1205_, size_t v_i_1206_, lean_object* v_b_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_1204_, v_sz_1205_, v_i_1206_, v_b_1207_, v___y_1208_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1221_, lean_object* v_sz_1222_, lean_object* v_i_1223_, lean_object* v_b_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
size_t v_sz_boxed_1237_; size_t v_i_boxed_1238_; lean_object* v_res_1239_; 
v_sz_boxed_1237_ = lean_unbox_usize(v_sz_1222_);
lean_dec(v_sz_1222_);
v_i_boxed_1238_ = lean_unbox_usize(v_i_1223_);
lean_dec(v_i_1223_);
v_res_1239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(v_as_1221_, v_sz_boxed_1237_, v_i_boxed_1238_, v_b_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v_as_1221_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_1240_, lean_object* v_keys_1241_, lean_object* v_vals_1242_, lean_object* v_heq_1243_, lean_object* v_i_1244_, lean_object* v_k_1245_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3_spec__7___redArg(v_keys_1241_, v_vals_1242_, v_i_1244_, v_k_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1247_, lean_object* v_keys_1248_, lean_object* v_vals_1249_, lean_object* v_heq_1250_, lean_object* v_i_1251_, lean_object* v_k_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_spec__3_spec__7(v_00_u03b2_1247_, v_keys_1248_, v_vals_1249_, v_heq_1250_, v_i_1251_, v_k_1252_);
lean_dec_ref(v_k_1252_);
lean_dec_ref(v_vals_1249_);
lean_dec_ref(v_keys_1248_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_1254_, size_t v_sz_1255_, size_t v_i_1256_, lean_object* v_b_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5___redArg(v_as_1254_, v_sz_1255_, v_i_1256_, v_b_1257_, v___y_1258_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_1271_, lean_object* v_sz_1272_, lean_object* v_i_1273_, lean_object* v_b_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
size_t v_sz_boxed_1287_; size_t v_i_boxed_1288_; lean_object* v_res_1289_; 
v_sz_boxed_1287_ = lean_unbox_usize(v_sz_1272_);
lean_dec(v_sz_1272_);
v_i_boxed_1288_ = lean_unbox_usize(v_i_1273_);
lean_dec(v_i_1273_);
v_res_1289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__5(v_as_1271_, v_sz_boxed_1287_, v_i_boxed_1288_, v_b_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v_as_1271_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1290_, v_a_1298_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v_vars_1303_; lean_object* v_size_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1301_, 1);
v_vars_1303_ = lean_ctor_get(v_a_1302_, 0);
lean_inc_ref(v_vars_1303_);
lean_dec(v_a_1302_);
v_size_1304_ = lean_ctor_get(v_vars_1303_, 2);
lean_inc(v_size_1304_);
lean_dec_ref(v_vars_1303_);
v___x_1305_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0));
v___x_1306_ = lean_mk_array(v_size_1304_, v___x_1305_);
v___x_1307_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v___x_1306_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1316_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v_snd_1312_; lean_object* v___x_1314_; 
v_snd_1312_ = lean_ctor_get(v_a_1308_, 1);
lean_inc(v_snd_1312_);
lean_dec(v_a_1308_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v_snd_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_snd_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
v_a_1317_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1307_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1307_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
v_a_1325_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1301_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1301_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo___boxed(lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec(v_a_1334_);
lean_dec(v_a_1333_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(lean_object* v_info_1345_){
_start:
{
lean_object* v_maxLowerCoeff_1346_; lean_object* v_maxUpperCoeff_1347_; lean_object* v_maxDvdCoeff_1348_; lean_object* v___y_1350_; uint8_t v___x_1352_; 
v_maxLowerCoeff_1346_ = lean_ctor_get(v_info_1345_, 0);
v_maxUpperCoeff_1347_ = lean_ctor_get(v_info_1345_, 1);
v_maxDvdCoeff_1348_ = lean_ctor_get(v_info_1345_, 2);
v___x_1352_ = lean_nat_dec_le(v_maxLowerCoeff_1346_, v_maxUpperCoeff_1347_);
if (v___x_1352_ == 0)
{
v___y_1350_ = v_maxUpperCoeff_1347_;
goto v___jp_1349_;
}
else
{
v___y_1350_ = v_maxLowerCoeff_1346_;
goto v___jp_1349_;
}
v___jp_1349_:
{
uint8_t v___x_1351_; 
v___x_1351_ = lean_nat_dec_le(v_maxDvdCoeff_1348_, v___y_1350_);
if (v___x_1351_ == 0)
{
lean_inc(v_maxDvdCoeff_1348_);
return v_maxDvdCoeff_1348_;
}
else
{
lean_inc(v___y_1350_);
return v___y_1350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081___boxed(lean_object* v_info_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v_info_1353_);
lean_dec_ref(v_info_1353_);
return v_res_1354_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(lean_object* v_infos_1355_, lean_object* v_x_1356_, lean_object* v_y_1357_){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1358_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1359_ = lean_array_get_borrowed(v___x_1358_, v_infos_1355_, v_x_1356_);
v___x_1360_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_1359_);
v___x_1361_ = lean_array_get_borrowed(v___x_1358_, v_infos_1355_, v_y_1357_);
v___x_1362_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_1361_);
v___x_1363_ = lean_nat_dec_lt(v___x_1360_, v___x_1362_);
if (v___x_1363_ == 0)
{
uint8_t v___x_1364_; 
v___x_1364_ = lean_nat_dec_eq(v___x_1360_, v___x_1362_);
lean_dec(v___x_1362_);
lean_dec(v___x_1360_);
if (v___x_1364_ == 0)
{
uint8_t v___x_1365_; 
v___x_1365_ = 0;
return v___x_1365_;
}
else
{
uint8_t v___x_1366_; 
v___x_1366_ = 1;
return v___x_1366_;
}
}
else
{
uint8_t v___x_1367_; 
lean_dec(v___x_1362_);
lean_dec(v___x_1360_);
v___x_1367_ = 2;
return v___x_1367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081___boxed(lean_object* v_infos_1368_, lean_object* v_x_1369_, lean_object* v_y_1370_){
_start:
{
uint8_t v_res_1371_; lean_object* v_r_1372_; 
v_res_1371_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_1368_, v_x_1369_, v_y_1370_);
lean_dec(v_y_1370_);
lean_dec(v_x_1369_);
lean_dec_ref(v_infos_1368_);
v_r_1372_ = lean_box(v_res_1371_);
return v_r_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(lean_object* v_info_1373_){
_start:
{
lean_object* v_maxLowerCoeff_1374_; lean_object* v_maxUpperCoeff_1375_; lean_object* v_maxDvdCoeff_1376_; lean_object* v___y_1378_; uint8_t v___x_1380_; 
v_maxLowerCoeff_1374_ = lean_ctor_get(v_info_1373_, 0);
v_maxUpperCoeff_1375_ = lean_ctor_get(v_info_1373_, 1);
v_maxDvdCoeff_1376_ = lean_ctor_get(v_info_1373_, 2);
v___x_1380_ = lean_nat_dec_le(v_maxLowerCoeff_1374_, v_maxUpperCoeff_1375_);
if (v___x_1380_ == 0)
{
v___y_1378_ = v_maxLowerCoeff_1374_;
goto v___jp_1377_;
}
else
{
v___y_1378_ = v_maxUpperCoeff_1375_;
goto v___jp_1377_;
}
v___jp_1377_:
{
uint8_t v___x_1379_; 
v___x_1379_ = lean_nat_dec_le(v_maxDvdCoeff_1376_, v___y_1378_);
if (v___x_1379_ == 0)
{
lean_inc(v_maxDvdCoeff_1376_);
return v_maxDvdCoeff_1376_;
}
else
{
lean_inc(v___y_1378_);
return v___y_1378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082___boxed(lean_object* v_info_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v_info_1381_);
lean_dec_ref(v_info_1381_);
return v_res_1382_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(lean_object* v_infos_1383_, lean_object* v_x_1384_, lean_object* v_y_1385_){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1386_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1387_ = lean_array_get_borrowed(v___x_1386_, v_infos_1383_, v_x_1384_);
v___x_1388_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v___x_1387_);
v___x_1389_ = lean_array_get_borrowed(v___x_1386_, v_infos_1383_, v_y_1385_);
v___x_1390_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v___x_1389_);
v___x_1391_ = lean_nat_dec_lt(v___x_1388_, v___x_1390_);
if (v___x_1391_ == 0)
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_nat_dec_eq(v___x_1388_, v___x_1390_);
lean_dec(v___x_1390_);
lean_dec(v___x_1388_);
if (v___x_1392_ == 0)
{
uint8_t v___x_1393_; 
v___x_1393_ = 0;
return v___x_1393_;
}
else
{
uint8_t v___x_1394_; 
v___x_1394_ = 1;
return v___x_1394_;
}
}
else
{
uint8_t v___x_1395_; 
lean_dec(v___x_1390_);
lean_dec(v___x_1388_);
v___x_1395_ = 2;
return v___x_1395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082___boxed(lean_object* v_infos_1396_, lean_object* v_x_1397_, lean_object* v_y_1398_){
_start:
{
uint8_t v_res_1399_; lean_object* v_r_1400_; 
v_res_1399_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_1396_, v_x_1397_, v_y_1398_);
lean_dec(v_y_1398_);
lean_dec(v_x_1397_);
lean_dec_ref(v_infos_1396_);
v_r_1400_ = lean_box(v_res_1399_);
return v_r_1400_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2083(lean_object* v_infos_1401_, lean_object* v_x_1402_, lean_object* v_y_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v_minCoeff_1406_; lean_object* v___x_1407_; lean_object* v_minCoeff_1408_; uint8_t v___x_1409_; 
v___x_1404_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1405_ = lean_array_get_borrowed(v___x_1404_, v_infos_1401_, v_x_1402_);
v_minCoeff_1406_ = lean_ctor_get(v___x_1405_, 3);
v___x_1407_ = lean_array_get_borrowed(v___x_1404_, v_infos_1401_, v_y_1403_);
v_minCoeff_1408_ = lean_ctor_get(v___x_1407_, 3);
v___x_1409_ = lean_nat_dec_lt(v_minCoeff_1406_, v_minCoeff_1408_);
if (v___x_1409_ == 0)
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_nat_dec_eq(v_minCoeff_1406_, v_minCoeff_1408_);
if (v___x_1410_ == 0)
{
uint8_t v___x_1411_; 
v___x_1411_ = 0;
return v___x_1411_;
}
else
{
uint8_t v___x_1412_; 
v___x_1412_ = 1;
return v___x_1412_;
}
}
else
{
uint8_t v___x_1413_; 
v___x_1413_ = 2;
return v___x_1413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2083___boxed(lean_object* v_infos_1414_, lean_object* v_x_1415_, lean_object* v_y_1416_){
_start:
{
uint8_t v_res_1417_; lean_object* v_r_1418_; 
v_res_1417_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2083(v_infos_1414_, v_x_1415_, v_y_1416_);
lean_dec(v_y_1416_);
lean_dec(v_x_1415_);
lean_dec_ref(v_infos_1414_);
v_r_1418_ = lean_box(v_res_1417_);
return v_r_1418_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmpPenalty(lean_object* v_infos_1419_, lean_object* v_x_1420_, lean_object* v_y_1421_){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v_penalty_1424_; lean_object* v___x_1425_; lean_object* v_penalty_1426_; uint8_t v___x_1427_; 
v___x_1422_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1423_ = lean_array_get_borrowed(v___x_1422_, v_infos_1419_, v_x_1420_);
v_penalty_1424_ = lean_ctor_get(v___x_1423_, 4);
v___x_1425_ = lean_array_get_borrowed(v___x_1422_, v_infos_1419_, v_y_1421_);
v_penalty_1426_ = lean_ctor_get(v___x_1425_, 4);
v___x_1427_ = lean_nat_dec_lt(v_penalty_1424_, v_penalty_1426_);
if (v___x_1427_ == 0)
{
uint8_t v___x_1428_; 
v___x_1428_ = lean_nat_dec_eq(v_penalty_1424_, v_penalty_1426_);
if (v___x_1428_ == 0)
{
uint8_t v___x_1429_; 
v___x_1429_ = 0;
return v___x_1429_;
}
else
{
uint8_t v___x_1430_; 
v___x_1430_ = 1;
return v___x_1430_;
}
}
else
{
uint8_t v___x_1431_; 
v___x_1431_ = 2;
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmpPenalty___boxed(lean_object* v_infos_1432_, lean_object* v_x_1433_, lean_object* v_y_1434_){
_start:
{
uint8_t v_res_1435_; lean_object* v_r_1436_; 
v_res_1435_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmpPenalty(v_infos_1432_, v_x_1433_, v_y_1434_);
lean_dec(v_y_1434_);
lean_dec(v_x_1433_);
lean_dec_ref(v_infos_1432_);
v_r_1436_ = lean_box(v_res_1435_);
return v_r_1436_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(lean_object* v_infos_1437_, lean_object* v_x_1438_, lean_object* v_y_1439_){
_start:
{
uint8_t v___y_1441_; uint8_t v___y_1447_; uint8_t v___y_1450_; uint8_t v___x_1452_; 
v___x_1452_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmpPenalty(v_infos_1437_, v_x_1438_, v_y_1439_);
if (v___x_1452_ == 1)
{
uint8_t v___x_1453_; 
v___x_1453_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_1437_, v_x_1438_, v_y_1439_);
v___y_1450_ = v___x_1453_;
goto v___jp_1449_;
}
else
{
v___y_1450_ = v___x_1452_;
goto v___jp_1449_;
}
v___jp_1440_:
{
if (v___y_1441_ == 1)
{
uint8_t v___x_1442_; 
v___x_1442_ = lean_nat_dec_lt(v_x_1438_, v_y_1439_);
if (v___x_1442_ == 0)
{
uint8_t v___x_1443_; 
v___x_1443_ = lean_nat_dec_eq(v_x_1438_, v_y_1439_);
if (v___x_1443_ == 0)
{
uint8_t v___x_1444_; 
v___x_1444_ = 2;
return v___x_1444_;
}
else
{
return v___y_1441_;
}
}
else
{
uint8_t v___x_1445_; 
v___x_1445_ = 0;
return v___x_1445_;
}
}
else
{
return v___y_1441_;
}
}
v___jp_1446_:
{
if (v___y_1447_ == 1)
{
uint8_t v___x_1448_; 
v___x_1448_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2083(v_infos_1437_, v_x_1438_, v_y_1439_);
v___y_1441_ = v___x_1448_;
goto v___jp_1440_;
}
else
{
v___y_1441_ = v___y_1447_;
goto v___jp_1440_;
}
}
v___jp_1449_:
{
if (v___y_1450_ == 1)
{
uint8_t v___x_1451_; 
v___x_1451_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_1437_, v_x_1438_, v_y_1439_);
v___y_1447_ = v___x_1451_;
goto v___jp_1446_;
}
else
{
v___y_1447_ = v___y_1450_;
goto v___jp_1446_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp___boxed(lean_object* v_infos_1454_, lean_object* v_x_1455_, lean_object* v_y_1456_){
_start:
{
uint8_t v_res_1457_; lean_object* v_r_1458_; 
v_res_1457_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_1454_, v_x_1455_, v_y_1456_);
lean_dec(v_y_1456_);
lean_dec(v_x_1455_);
lean_dec_ref(v_infos_1454_);
v_r_1458_ = lean_box(v_res_1457_);
return v_r_1458_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(lean_object* v_infos_1459_, lean_object* v_x_1460_, lean_object* v_y_1461_){
_start:
{
uint8_t v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v___x_1462_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_1459_, v_x_1460_, v_y_1461_);
v___x_1463_ = lean_box(v___x_1462_);
v___x_1464_ = lean_obj_tag_nat(v___x_1463_);
lean_dec(v___x_1463_);
v___x_1465_ = lean_unsigned_to_nat(0u);
v___x_1466_ = lean_nat_dec_eq(v___x_1464_, v___x_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0___boxed(lean_object* v_infos_1467_, lean_object* v_x_1468_, lean_object* v_y_1469_){
_start:
{
uint8_t v_res_1470_; lean_object* v_r_1471_; 
v_res_1470_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1467_, v_x_1468_, v_y_1469_);
lean_dec(v_y_1469_);
lean_dec(v_x_1468_);
lean_dec_ref(v_infos_1467_);
v_r_1471_ = lean_box(v_res_1470_);
return v_r_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(lean_object* v_infos_1472_, lean_object* v_hi_1473_, lean_object* v_pivot_1474_, lean_object* v_as_1475_, lean_object* v_i_1476_, lean_object* v_k_1477_){
_start:
{
uint8_t v___x_1478_; 
v___x_1478_ = lean_nat_dec_lt(v_k_1477_, v_hi_1473_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_dec(v_k_1477_);
v___x_1479_ = lean_array_fswap(v_as_1475_, v_i_1476_, v_hi_1473_);
v___x_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1480_, 0, v_i_1476_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
return v___x_1480_;
}
else
{
lean_object* v___x_1481_; uint8_t v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1481_ = lean_array_fget_borrowed(v_as_1475_, v_k_1477_);
v___x_1482_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_1472_, v___x_1481_, v_pivot_1474_);
v___x_1483_ = lean_box(v___x_1482_);
v___x_1484_ = lean_obj_tag_nat(v___x_1483_);
lean_dec(v___x_1483_);
v___x_1485_ = lean_unsigned_to_nat(0u);
v___x_1486_ = lean_nat_dec_eq(v___x_1484_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = lean_unsigned_to_nat(1u);
v___x_1488_ = lean_nat_add(v_k_1477_, v___x_1487_);
lean_dec(v_k_1477_);
v_k_1477_ = v___x_1488_;
goto _start;
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1490_ = lean_array_fswap(v_as_1475_, v_i_1476_, v_k_1477_);
v___x_1491_ = lean_unsigned_to_nat(1u);
v___x_1492_ = lean_nat_add(v_i_1476_, v___x_1491_);
lean_dec(v_i_1476_);
v___x_1493_ = lean_nat_add(v_k_1477_, v___x_1491_);
lean_dec(v_k_1477_);
v_as_1475_ = v___x_1490_;
v_i_1476_ = v___x_1492_;
v_k_1477_ = v___x_1493_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg___boxed(lean_object* v_infos_1495_, lean_object* v_hi_1496_, lean_object* v_pivot_1497_, lean_object* v_as_1498_, lean_object* v_i_1499_, lean_object* v_k_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_infos_1495_, v_hi_1496_, v_pivot_1497_, v_as_1498_, v_i_1499_, v_k_1500_);
lean_dec(v_pivot_1497_);
lean_dec(v_hi_1496_);
lean_dec_ref(v_infos_1495_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(lean_object* v_infos_1502_, lean_object* v_n_1503_, lean_object* v_as_1504_, lean_object* v_lo_1505_, lean_object* v_hi_1506_){
_start:
{
lean_object* v___y_1508_; uint8_t v___x_1518_; 
v___x_1518_ = lean_nat_dec_lt(v_lo_1505_, v_hi_1506_);
if (v___x_1518_ == 0)
{
lean_dec(v_lo_1505_);
return v_as_1504_;
}
else
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v_mid_1521_; lean_object* v___y_1523_; lean_object* v___y_1529_; lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1519_ = lean_nat_add(v_lo_1505_, v_hi_1506_);
v___x_1520_ = lean_unsigned_to_nat(1u);
v_mid_1521_ = lean_nat_shiftr(v___x_1519_, v___x_1520_);
lean_dec(v___x_1519_);
v___x_1534_ = lean_array_fget_borrowed(v_as_1504_, v_mid_1521_);
v___x_1535_ = lean_array_fget_borrowed(v_as_1504_, v_lo_1505_);
v___x_1536_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1502_, v___x_1534_, v___x_1535_);
if (v___x_1536_ == 0)
{
v___y_1529_ = v_as_1504_;
goto v___jp_1528_;
}
else
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_array_fswap(v_as_1504_, v_lo_1505_, v_mid_1521_);
v___y_1529_ = v___x_1537_;
goto v___jp_1528_;
}
v___jp_1522_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1524_ = lean_array_fget_borrowed(v___y_1523_, v_mid_1521_);
v___x_1525_ = lean_array_fget_borrowed(v___y_1523_, v_hi_1506_);
v___x_1526_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1502_, v___x_1524_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_dec(v_mid_1521_);
v___y_1508_ = v___y_1523_;
goto v___jp_1507_;
}
else
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_array_fswap(v___y_1523_, v_mid_1521_, v_hi_1506_);
lean_dec(v_mid_1521_);
v___y_1508_ = v___x_1527_;
goto v___jp_1507_;
}
}
v___jp_1528_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1530_ = lean_array_fget_borrowed(v___y_1529_, v_hi_1506_);
v___x_1531_ = lean_array_fget_borrowed(v___y_1529_, v_lo_1505_);
v___x_1532_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1502_, v___x_1530_, v___x_1531_);
if (v___x_1532_ == 0)
{
v___y_1523_ = v___y_1529_;
goto v___jp_1522_;
}
else
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_array_fswap(v___y_1529_, v_lo_1505_, v_hi_1506_);
v___y_1523_ = v___x_1533_;
goto v___jp_1522_;
}
}
}
v___jp_1507_:
{
lean_object* v_pivot_1509_; lean_object* v___x_1510_; lean_object* v_fst_1511_; lean_object* v_snd_1512_; uint8_t v___x_1513_; 
v_pivot_1509_ = lean_array_fget(v___y_1508_, v_hi_1506_);
lean_inc_n(v_lo_1505_, 2);
v___x_1510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_infos_1502_, v_hi_1506_, v_pivot_1509_, v___y_1508_, v_lo_1505_, v_lo_1505_);
lean_dec(v_pivot_1509_);
v_fst_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_fst_1511_);
v_snd_1512_ = lean_ctor_get(v___x_1510_, 1);
lean_inc(v_snd_1512_);
lean_dec_ref(v___x_1510_);
v___x_1513_ = lean_nat_dec_le(v_hi_1506_, v_fst_1511_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1514_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_infos_1502_, v_n_1503_, v_snd_1512_, v_lo_1505_, v_fst_1511_);
v___x_1515_ = lean_unsigned_to_nat(1u);
v___x_1516_ = lean_nat_add(v_fst_1511_, v___x_1515_);
lean_dec(v_fst_1511_);
v_as_1504_ = v___x_1514_;
v_lo_1505_ = v___x_1516_;
goto _start;
}
else
{
lean_dec(v_fst_1511_);
lean_dec(v_lo_1505_);
return v_snd_1512_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___boxed(lean_object* v_infos_1538_, lean_object* v_n_1539_, lean_object* v_as_1540_, lean_object* v_lo_1541_, lean_object* v_hi_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_infos_1538_, v_n_1539_, v_as_1540_, v_lo_1541_, v_hi_1542_);
lean_dec(v_hi_1542_);
lean_dec(v_n_1539_);
lean_dec_ref(v_infos_1538_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(lean_object* v_infos_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1545_, v_a_1546_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1573_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1551_ = v___x_1548_;
v_isShared_1552_ = v_isSharedCheck_1573_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1573_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v_vars_1553_; lean_object* v_size_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v_vars_1553_ = lean_ctor_get(v_a_1549_, 0);
lean_inc_ref(v_vars_1553_);
lean_dec(v_a_1549_);
v_size_1554_ = lean_ctor_get(v_vars_1553_, 2);
lean_inc(v_size_1554_);
lean_dec_ref(v_vars_1553_);
v___x_1555_ = l_Array_range(v_size_1554_);
v___x_1556_ = lean_array_get_size(v___x_1555_);
v___x_1564_ = lean_unsigned_to_nat(0u);
v___x_1565_ = lean_nat_dec_eq(v___x_1556_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___y_1569_; uint8_t v___x_1571_; 
v___x_1566_ = lean_unsigned_to_nat(1u);
v___x_1567_ = lean_nat_sub(v___x_1556_, v___x_1566_);
v___x_1571_ = lean_nat_dec_le(v___x_1564_, v___x_1567_);
if (v___x_1571_ == 0)
{
lean_inc(v___x_1567_);
v___y_1569_ = v___x_1567_;
goto v___jp_1568_;
}
else
{
v___y_1569_ = v___x_1564_;
goto v___jp_1568_;
}
v___jp_1568_:
{
uint8_t v___x_1570_; 
v___x_1570_ = lean_nat_dec_le(v___y_1569_, v___x_1567_);
if (v___x_1570_ == 0)
{
lean_dec(v___x_1567_);
lean_inc(v___y_1569_);
v___y_1558_ = v___y_1569_;
v___y_1559_ = v___y_1569_;
goto v___jp_1557_;
}
else
{
v___y_1558_ = v___y_1569_;
v___y_1559_ = v___x_1567_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v___x_1572_; 
lean_del_object(v___x_1551_);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1555_);
return v___x_1572_;
}
v___jp_1557_:
{
lean_object* v___x_1560_; lean_object* v___x_1562_; 
v___x_1560_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_infos_1544_, v___x_1556_, v___x_1555_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1560_);
v___x_1562_ = v___x_1551_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
v_a_1574_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1548_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1548_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg___boxed(lean_object* v_infos_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(v_infos_1582_, v_a_1583_, v_a_1584_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_infos_1582_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(lean_object* v_infos_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(v_infos_1587_, v_a_1588_, v_a_1596_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___boxed(lean_object* v_infos_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(v_infos_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
lean_dec(v_a_1610_);
lean_dec_ref(v_a_1609_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_infos_1600_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(lean_object* v_infos_1613_, lean_object* v_n_1614_, lean_object* v_as_1615_, lean_object* v_lo_1616_, lean_object* v_hi_1617_, lean_object* v_w_1618_, lean_object* v_hlo_1619_, lean_object* v_hhi_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_infos_1613_, v_n_1614_, v_as_1615_, v_lo_1616_, v_hi_1617_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___boxed(lean_object* v_infos_1622_, lean_object* v_n_1623_, lean_object* v_as_1624_, lean_object* v_lo_1625_, lean_object* v_hi_1626_, lean_object* v_w_1627_, lean_object* v_hlo_1628_, lean_object* v_hhi_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(v_infos_1622_, v_n_1623_, v_as_1624_, v_lo_1625_, v_hi_1626_, v_w_1627_, v_hlo_1628_, v_hhi_1629_);
lean_dec(v_hi_1626_);
lean_dec(v_n_1623_);
lean_dec_ref(v_infos_1622_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0(lean_object* v_infos_1631_, lean_object* v_n_1632_, lean_object* v_lo_1633_, lean_object* v_hi_1634_, lean_object* v_hhi_1635_, lean_object* v_pivot_1636_, lean_object* v_as_1637_, lean_object* v_i_1638_, lean_object* v_k_1639_, lean_object* v_ilo_1640_, lean_object* v_ik_1641_, lean_object* v_w_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_infos_1631_, v_hi_1634_, v_pivot_1636_, v_as_1637_, v_i_1638_, v_k_1639_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___boxed(lean_object* v_infos_1644_, lean_object* v_n_1645_, lean_object* v_lo_1646_, lean_object* v_hi_1647_, lean_object* v_hhi_1648_, lean_object* v_pivot_1649_, lean_object* v_as_1650_, lean_object* v_i_1651_, lean_object* v_k_1652_, lean_object* v_ilo_1653_, lean_object* v_ik_1654_, lean_object* v_w_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0(v_infos_1644_, v_n_1645_, v_lo_1646_, v_hi_1647_, v_hhi_1648_, v_pivot_1649_, v_as_1650_, v_i_1651_, v_k_1652_, v_ilo_1653_, v_ik_1654_, v_w_1655_);
lean_dec(v_pivot_1649_);
lean_dec(v_hi_1647_);
lean_dec(v_lo_1646_);
lean_dec(v_n_1645_);
lean_dec_ref(v_infos_1644_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(lean_object* v_perm_1657_, lean_object* v_range_1658_, lean_object* v_b_1659_, lean_object* v_i_1660_){
_start:
{
lean_object* v_stop_1661_; lean_object* v_step_1662_; uint8_t v___x_1663_; 
v_stop_1661_ = lean_ctor_get(v_range_1658_, 1);
v_step_1662_ = lean_ctor_get(v_range_1658_, 2);
v___x_1663_ = lean_nat_dec_lt(v_i_1660_, v_stop_1661_);
if (v___x_1663_ == 0)
{
lean_dec(v_i_1660_);
return v_b_1659_;
}
else
{
lean_object* v___x_1664_; lean_object* v_inv_1665_; lean_object* v___x_1666_; 
v___x_1664_ = lean_array_fget_borrowed(v_perm_1657_, v_i_1660_);
lean_inc(v_i_1660_);
v_inv_1665_ = lean_array_set(v_b_1659_, v___x_1664_, v_i_1660_);
v___x_1666_ = lean_nat_add(v_i_1660_, v_step_1662_);
lean_dec(v_i_1660_);
v_b_1659_ = v_inv_1665_;
v_i_1660_ = v___x_1666_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg___boxed(lean_object* v_perm_1668_, lean_object* v_range_1669_, lean_object* v_b_1670_, lean_object* v_i_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1668_, v_range_1669_, v_b_1670_, v_i_1671_);
lean_dec_ref(v_range_1669_);
lean_dec_ref(v_perm_1668_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(lean_object* v_perm_1673_){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v_inv_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1674_ = lean_array_get_size(v_perm_1673_);
v___x_1675_ = lean_unsigned_to_nat(0u);
v_inv_1676_ = lean_mk_array(v___x_1674_, v___x_1675_);
v___x_1677_ = lean_unsigned_to_nat(1u);
v___x_1678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1675_);
lean_ctor_set(v___x_1678_, 1, v___x_1674_);
lean_ctor_set(v___x_1678_, 2, v___x_1677_);
v___x_1679_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1673_, v___x_1678_, v_inv_1676_, v___x_1675_);
lean_dec_ref_known(v___x_1678_, 3);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv___boxed(lean_object* v_perm_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_perm_1680_);
lean_dec_ref(v_perm_1680_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(lean_object* v_perm_1682_, lean_object* v_range_1683_, lean_object* v_b_1684_, lean_object* v_i_1685_, lean_object* v_hs_1686_, lean_object* v_hl_1687_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1682_, v_range_1683_, v_b_1684_, v_i_1685_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___boxed(lean_object* v_perm_1689_, lean_object* v_range_1690_, lean_object* v_b_1691_, lean_object* v_i_1692_, lean_object* v_hs_1693_, lean_object* v_hl_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(v_perm_1689_, v_range_1690_, v_b_1691_, v_i_1692_, v_hs_1693_, v_hl_1694_);
lean_dec_ref(v_range_1690_);
lean_dec_ref(v_perm_1689_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_reorder(lean_object* v_p_1696_, lean_object* v_old2new_1697_){
_start:
{
if (lean_obj_tag(v_p_1696_) == 0)
{
return v_p_1696_;
}
else
{
lean_object* v_k_1698_; lean_object* v_v_1699_; lean_object* v_p_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1710_; 
v_k_1698_ = lean_ctor_get(v_p_1696_, 0);
v_v_1699_ = lean_ctor_get(v_p_1696_, 1);
v_p_1700_ = lean_ctor_get(v_p_1696_, 2);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_p_1696_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1702_ = v_p_1696_;
v_isShared_1703_ = v_isSharedCheck_1710_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_p_1700_);
lean_inc(v_v_1699_);
lean_inc(v_k_1698_);
lean_dec(v_p_1696_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1710_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1704_ = lean_unsigned_to_nat(0u);
v___x_1705_ = lean_array_get_borrowed(v___x_1704_, v_old2new_1697_, v_v_1699_);
lean_dec(v_v_1699_);
v___x_1706_ = l_Int_Internal_Linear_Poly_reorder(v_p_1700_, v_old2new_1697_);
lean_inc(v___x_1705_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 2, v___x_1706_);
lean_ctor_set(v___x_1702_, 1, v___x_1705_);
v___x_1708_ = v___x_1702_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_k_1698_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1709_, 2, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_reorder___boxed(lean_object* v_p_1711_, lean_object* v_old2new_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Int_Internal_Linear_Poly_reorder(v_p_1711_, v_old2new_1712_);
lean_dec_ref(v_old2new_1712_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(lean_object* v_c_1714_, lean_object* v_old2new_1715_){
_start:
{
lean_object* v_d_1716_; lean_object* v_p_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_d_1716_ = lean_ctor_get(v_c_1714_, 0);
lean_inc(v_d_1716_);
v_p_1717_ = lean_ctor_get(v_c_1714_, 1);
lean_inc_ref(v_p_1717_);
v___x_1718_ = l_Int_Internal_Linear_Poly_reorder(v_p_1717_, v_old2new_1715_);
v___x_1719_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_1719_, 0, v_c_1714_);
v___x_1720_ = lean_box(0);
v___x_1721_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1721_, 0, v_d_1716_);
lean_ctor_set(v___x_1721_, 1, v___x_1718_);
lean_ctor_set(v___x_1721_, 2, v___x_1719_);
lean_ctor_set(v___x_1721_, 3, v___x_1720_);
v___x_1722_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v___x_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder___boxed(lean_object* v_c_1723_, lean_object* v_old2new_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(v_c_1723_, v_old2new_1724_);
lean_dec_ref(v_old2new_1724_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(lean_object* v_c_1726_, lean_object* v_old2new_1727_){
_start:
{
lean_object* v_p_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_p_1728_ = lean_ctor_get(v_c_1726_, 0);
lean_inc_ref(v_p_1728_);
v___x_1729_ = l_Int_Internal_Linear_Poly_reorder(v_p_1728_, v_old2new_1727_);
v___x_1730_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_c_1726_);
v___x_1731_ = lean_box(0);
v___x_1732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1729_);
lean_ctor_set(v___x_1732_, 1, v___x_1730_);
lean_ctor_set(v___x_1732_, 2, v___x_1731_);
v___x_1733_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_norm(v___x_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder___boxed(lean_object* v_c_1734_, lean_object* v_old2new_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_c_1734_, v_old2new_1735_);
lean_dec_ref(v_old2new_1735_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(lean_object* v_c_1737_, lean_object* v_old2new_1738_){
_start:
{
lean_object* v_p_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_p_1739_ = lean_ctor_get(v_c_1737_, 0);
lean_inc_ref(v_p_1739_);
v___x_1740_ = l_Int_Internal_Linear_Poly_reorder(v_p_1739_, v_old2new_1738_);
v___x_1741_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1741_, 0, v_c_1737_);
v___x_1742_ = lean_box(0);
v___x_1743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1740_);
lean_ctor_set(v___x_1743_, 1, v___x_1741_);
lean_ctor_set(v___x_1743_, 2, v___x_1742_);
v___x_1744_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v___x_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder___boxed(lean_object* v_c_1745_, lean_object* v_old2new_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_c_1745_, v_old2new_1746_);
lean_dec_ref(v_old2new_1746_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(lean_object* v_c_1748_, lean_object* v_old2new_1749_){
_start:
{
lean_object* v_p_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v_p_1750_ = lean_ctor_get(v_c_1748_, 0);
lean_inc_ref(v_p_1750_);
v___x_1751_ = l_Int_Internal_Linear_Poly_reorder(v_p_1750_, v_old2new_1749_);
v___x_1752_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_c_1748_);
v___x_1753_ = lean_box(0);
v___x_1754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1751_);
lean_ctor_set(v___x_1754_, 1, v___x_1752_);
lean_ctor_set(v___x_1754_, 2, v___x_1753_);
v___x_1755_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_norm(v___x_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder___boxed(lean_object* v_c_1756_, lean_object* v_old2new_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(v_c_1756_, v_old2new_1757_);
lean_dec_ref(v_old2new_1757_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(lean_object* v_new2old_1759_, lean_object* v_inst_1760_, lean_object* v_m_1761_, lean_object* v_i_1762_, lean_object* v_h_1763_, lean_object* v_____s_1764_){
_start:
{
lean_object* v_j_1765_; lean_object* v___x_1766_; lean_object* v_r_1767_; lean_object* v___x_1768_; 
v_j_1765_ = lean_array_fget_borrowed(v_new2old_1759_, v_i_1762_);
v___x_1766_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_1760_, v_m_1761_, v_j_1765_);
v_r_1767_ = l_Lean_PersistentArray_push___redArg(v_____s_1764_, v___x_1766_);
v___x_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_r_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed(lean_object* v_new2old_1769_, lean_object* v_inst_1770_, lean_object* v_m_1771_, lean_object* v_i_1772_, lean_object* v_h_1773_, lean_object* v_____s_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(v_new2old_1769_, v_inst_1770_, v_m_1771_, v_i_1772_, v_h_1773_, v_____s_1774_);
lean_dec(v_i_1772_);
lean_dec_ref(v_m_1771_);
lean_dec(v_inst_1770_);
lean_dec_ref(v_new2old_1769_);
return v_res_1775_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1795_ = lean_unsigned_to_nat(32u);
v___x_1796_ = lean_mk_empty_array_with_capacity(v___x_1795_);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
return v___x_1797_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11(void){
_start:
{
size_t v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v_r_1803_; 
v___x_1798_ = ((size_t)5ULL);
v___x_1799_ = lean_unsigned_to_nat(0u);
v___x_1800_ = lean_unsigned_to_nat(32u);
v___x_1801_ = lean_mk_empty_array_with_capacity(v___x_1800_);
v___x_1802_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10);
v_r_1803_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_r_1803_, 0, v___x_1802_);
lean_ctor_set(v_r_1803_, 1, v___x_1801_);
lean_ctor_set(v_r_1803_, 2, v___x_1799_);
lean_ctor_set(v_r_1803_, 3, v___x_1799_);
lean_ctor_set_usize(v_r_1803_, 4, v___x_1798_);
return v_r_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(lean_object* v_inst_1804_, lean_object* v_m_1805_, lean_object* v_new2old_1806_){
_start:
{
lean_object* v___f_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_r_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_inc_ref(v_new2old_1806_);
v___f_1807_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1807_, 0, v_new2old_1806_);
lean_closure_set(v___f_1807_, 1, v_inst_1804_);
lean_closure_set(v___f_1807_, 2, v_m_1805_);
v___x_1808_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9));
v___x_1809_ = lean_unsigned_to_nat(0u);
v_r_1810_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11);
v___x_1811_ = lean_array_get_size(v_new2old_1806_);
lean_dec_ref(v_new2old_1806_);
v___x_1812_ = lean_unsigned_to_nat(1u);
v___x_1813_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1809_);
lean_ctor_set(v___x_1813_, 1, v___x_1811_);
lean_ctor_set(v___x_1813_, 2, v___x_1812_);
v___x_1814_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_box(0), lean_box(0), v___x_1808_, v___x_1813_, v___f_1807_, v_r_1810_, v___x_1809_, lean_box(0), lean_box(0));
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap(lean_object* v_00_u03b1_1815_, lean_object* v_inst_1816_, lean_object* v_m_1817_, lean_object* v_new2old_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v_inst_1816_, v_m_1817_, v_new2old_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_, lean_object* v_x_1823_){
_start:
{
lean_object* v_ks_1824_; lean_object* v_vs_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1849_; 
v_ks_1824_ = lean_ctor_get(v_x_1820_, 0);
v_vs_1825_ = lean_ctor_get(v_x_1820_, 1);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_x_1820_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1827_ = v_x_1820_;
v_isShared_1828_ = v_isSharedCheck_1849_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_vs_1825_);
lean_inc(v_ks_1824_);
lean_dec(v_x_1820_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1849_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1829_ = lean_array_get_size(v_ks_1824_);
v___x_1830_ = lean_nat_dec_lt(v_x_1821_, v___x_1829_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
lean_dec(v_x_1821_);
v___x_1831_ = lean_array_push(v_ks_1824_, v_x_1822_);
v___x_1832_ = lean_array_push(v_vs_1825_, v_x_1823_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 1, v___x_1832_);
lean_ctor_set(v___x_1827_, 0, v___x_1831_);
v___x_1834_ = v___x_1827_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1831_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
else
{
lean_object* v_k_x27_1836_; uint8_t v___x_1837_; 
v_k_x27_1836_ = lean_array_fget_borrowed(v_ks_1824_, v_x_1821_);
v___x_1837_ = l_Int_Internal_Linear_instBEqPoly_beq(v_x_1822_, v_k_x27_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1839_; 
if (v_isShared_1828_ == 0)
{
v___x_1839_ = v___x_1827_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_ks_1824_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_vs_1825_);
v___x_1839_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = lean_unsigned_to_nat(1u);
v___x_1841_ = lean_nat_add(v_x_1821_, v___x_1840_);
lean_dec(v_x_1821_);
v_x_1820_ = v___x_1839_;
v_x_1821_ = v___x_1841_;
goto _start;
}
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1844_ = lean_array_fset(v_ks_1824_, v_x_1821_, v_x_1822_);
v___x_1845_ = lean_array_fset(v_vs_1825_, v_x_1821_, v_x_1823_);
lean_dec(v_x_1821_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 1, v___x_1845_);
lean_ctor_set(v___x_1827_, 0, v___x_1844_);
v___x_1847_ = v___x_1827_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1850_, lean_object* v_k_1851_, lean_object* v_v_1852_){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = lean_unsigned_to_nat(0u);
v___x_1854_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1850_, v___x_1853_, v_k_1851_, v_v_1852_);
return v___x_1854_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(lean_object* v_x_1856_, size_t v_x_1857_, size_t v_x_1858_, lean_object* v_x_1859_, lean_object* v_x_1860_){
_start:
{
if (lean_obj_tag(v_x_1856_) == 0)
{
lean_object* v_es_1861_; size_t v___x_1862_; size_t v___x_1863_; lean_object* v_j_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
v_es_1861_ = lean_ctor_get(v_x_1856_, 0);
v___x_1862_ = ((size_t)31ULL);
v___x_1863_ = lean_usize_land(v_x_1857_, v___x_1862_);
v_j_1864_ = lean_usize_to_nat(v___x_1863_);
v___x_1865_ = lean_array_get_size(v_es_1861_);
v___x_1866_ = lean_nat_dec_lt(v_j_1864_, v___x_1865_);
if (v___x_1866_ == 0)
{
lean_dec(v_j_1864_);
lean_dec(v_x_1860_);
lean_dec_ref(v_x_1859_);
return v_x_1856_;
}
else
{
lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1905_; 
lean_inc_ref(v_es_1861_);
v_isSharedCheck_1905_ = !lean_is_exclusive(v_x_1856_);
if (v_isSharedCheck_1905_ == 0)
{
lean_object* v_unused_1906_; 
v_unused_1906_ = lean_ctor_get(v_x_1856_, 0);
lean_dec(v_unused_1906_);
v___x_1868_ = v_x_1856_;
v_isShared_1869_ = v_isSharedCheck_1905_;
goto v_resetjp_1867_;
}
else
{
lean_dec(v_x_1856_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1905_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v_v_1870_; lean_object* v___x_1871_; lean_object* v_xs_x27_1872_; lean_object* v___y_1874_; 
v_v_1870_ = lean_array_fget(v_es_1861_, v_j_1864_);
v___x_1871_ = lean_box(0);
v_xs_x27_1872_ = lean_array_fset(v_es_1861_, v_j_1864_, v___x_1871_);
switch(lean_obj_tag(v_v_1870_))
{
case 0:
{
lean_object* v_key_1879_; lean_object* v_val_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1890_; 
v_key_1879_ = lean_ctor_get(v_v_1870_, 0);
v_val_1880_ = lean_ctor_get(v_v_1870_, 1);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_v_1870_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1882_ = v_v_1870_;
v_isShared_1883_ = v_isSharedCheck_1890_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_val_1880_);
lean_inc(v_key_1879_);
lean_dec(v_v_1870_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1890_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
uint8_t v___x_1884_; 
v___x_1884_ = l_Int_Internal_Linear_instBEqPoly_beq(v_x_1859_, v_key_1879_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_del_object(v___x_1882_);
v___x_1885_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1879_, v_val_1880_, v_x_1859_, v_x_1860_);
v___x_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
v___y_1874_ = v___x_1886_;
goto v___jp_1873_;
}
else
{
lean_object* v___x_1888_; 
lean_dec(v_val_1880_);
lean_dec(v_key_1879_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 1, v_x_1860_);
lean_ctor_set(v___x_1882_, 0, v_x_1859_);
v___x_1888_ = v___x_1882_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_x_1859_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_x_1860_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
v___y_1874_ = v___x_1888_;
goto v___jp_1873_;
}
}
}
}
case 1:
{
lean_object* v_node_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1903_; 
v_node_1891_ = lean_ctor_get(v_v_1870_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_v_1870_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1893_ = v_v_1870_;
v_isShared_1894_ = v_isSharedCheck_1903_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_node_1891_);
lean_dec(v_v_1870_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1903_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
size_t v___x_1895_; size_t v___x_1896_; size_t v___x_1897_; size_t v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1895_ = ((size_t)5ULL);
v___x_1896_ = lean_usize_shift_right(v_x_1857_, v___x_1895_);
v___x_1897_ = ((size_t)1ULL);
v___x_1898_ = lean_usize_add(v_x_1858_, v___x_1897_);
v___x_1899_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_node_1891_, v___x_1896_, v___x_1898_, v_x_1859_, v_x_1860_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1899_);
v___x_1901_ = v___x_1893_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
v___y_1874_ = v___x_1901_;
goto v___jp_1873_;
}
}
}
default: 
{
lean_object* v___x_1904_; 
v___x_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1904_, 0, v_x_1859_);
lean_ctor_set(v___x_1904_, 1, v_x_1860_);
v___y_1874_ = v___x_1904_;
goto v___jp_1873_;
}
}
v___jp_1873_:
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
v___x_1875_ = lean_array_fset(v_xs_x27_1872_, v_j_1864_, v___y_1874_);
lean_dec(v_j_1864_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v___x_1875_);
v___x_1877_ = v___x_1868_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
}
else
{
lean_object* v_ks_1907_; lean_object* v_vs_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1926_; 
v_ks_1907_ = lean_ctor_get(v_x_1856_, 0);
v_vs_1908_ = lean_ctor_get(v_x_1856_, 1);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_x_1856_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1910_ = v_x_1856_;
v_isShared_1911_ = v_isSharedCheck_1926_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_vs_1908_);
lean_inc(v_ks_1907_);
lean_dec(v_x_1856_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1926_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_ks_1907_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_vs_1908_);
v___x_1913_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v_newNode_1914_; size_t v___x_1915_; uint8_t v___x_1916_; 
v_newNode_1914_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(v___x_1913_, v_x_1859_, v_x_1860_);
v___x_1915_ = ((size_t)7ULL);
v___x_1916_ = lean_usize_dec_le(v___x_1915_, v_x_1858_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1917_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1914_);
v___x_1918_ = lean_unsigned_to_nat(4u);
v___x_1919_ = lean_nat_dec_lt(v___x_1917_, v___x_1918_);
lean_dec(v___x_1917_);
if (v___x_1919_ == 0)
{
lean_object* v_ks_1920_; lean_object* v_vs_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_ks_1920_ = lean_ctor_get(v_newNode_1914_, 0);
lean_inc_ref(v_ks_1920_);
v_vs_1921_ = lean_ctor_get(v_newNode_1914_, 1);
lean_inc_ref(v_vs_1921_);
lean_dec_ref(v_newNode_1914_);
v___x_1922_ = lean_unsigned_to_nat(0u);
v___x_1923_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0);
v___x_1924_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_x_1858_, v_ks_1920_, v_vs_1921_, v___x_1922_, v___x_1923_);
lean_dec_ref(v_vs_1921_);
lean_dec_ref(v_ks_1920_);
return v___x_1924_;
}
else
{
return v_newNode_1914_;
}
}
else
{
return v_newNode_1914_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(size_t v_depth_1927_, lean_object* v_keys_1928_, lean_object* v_vals_1929_, lean_object* v_i_1930_, lean_object* v_entries_1931_){
_start:
{
lean_object* v___x_1932_; uint8_t v___x_1933_; 
v___x_1932_ = lean_array_get_size(v_keys_1928_);
v___x_1933_ = lean_nat_dec_lt(v_i_1930_, v___x_1932_);
if (v___x_1933_ == 0)
{
lean_dec(v_i_1930_);
return v_entries_1931_;
}
else
{
lean_object* v_k_1934_; lean_object* v_v_1935_; uint64_t v___x_1936_; size_t v_h_1937_; size_t v___x_1938_; lean_object* v___x_1939_; size_t v___x_1940_; size_t v___x_1941_; size_t v___x_1942_; size_t v_h_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v_k_1934_ = lean_array_fget_borrowed(v_keys_1928_, v_i_1930_);
v_v_1935_ = lean_array_fget_borrowed(v_vals_1929_, v_i_1930_);
v___x_1936_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_k_1934_);
v_h_1937_ = lean_uint64_to_usize(v___x_1936_);
v___x_1938_ = ((size_t)5ULL);
v___x_1939_ = lean_unsigned_to_nat(1u);
v___x_1940_ = ((size_t)1ULL);
v___x_1941_ = lean_usize_sub(v_depth_1927_, v___x_1940_);
v___x_1942_ = lean_usize_mul(v___x_1938_, v___x_1941_);
v_h_1943_ = lean_usize_shift_right(v_h_1937_, v___x_1942_);
v___x_1944_ = lean_nat_add(v_i_1930_, v___x_1939_);
lean_dec(v_i_1930_);
lean_inc(v_v_1935_);
lean_inc(v_k_1934_);
v___x_1945_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_entries_1931_, v_h_1943_, v_depth_1927_, v_k_1934_, v_v_1935_);
v_i_1930_ = v___x_1944_;
v_entries_1931_ = v___x_1945_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1947_, lean_object* v_keys_1948_, lean_object* v_vals_1949_, lean_object* v_i_1950_, lean_object* v_entries_1951_){
_start:
{
size_t v_depth_boxed_1952_; lean_object* v_res_1953_; 
v_depth_boxed_1952_ = lean_unbox_usize(v_depth_1947_);
lean_dec(v_depth_1947_);
v_res_1953_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1952_, v_keys_1948_, v_vals_1949_, v_i_1950_, v_entries_1951_);
lean_dec_ref(v_vals_1949_);
lean_dec_ref(v_keys_1948_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___boxed(lean_object* v_x_1954_, lean_object* v_x_1955_, lean_object* v_x_1956_, lean_object* v_x_1957_, lean_object* v_x_1958_){
_start:
{
size_t v_x_1760__boxed_1959_; size_t v_x_1761__boxed_1960_; lean_object* v_res_1961_; 
v_x_1760__boxed_1959_ = lean_unbox_usize(v_x_1955_);
lean_dec(v_x_1955_);
v_x_1761__boxed_1960_ = lean_unbox_usize(v_x_1956_);
lean_dec(v_x_1956_);
v_res_1961_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1954_, v_x_1760__boxed_1959_, v_x_1761__boxed_1960_, v_x_1957_, v_x_1958_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(lean_object* v_x_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_){
_start:
{
uint64_t v___x_1965_; size_t v___x_1966_; size_t v___x_1967_; lean_object* v___x_1968_; 
v___x_1965_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_x_1963_);
v___x_1966_ = lean_uint64_to_usize(v___x_1965_);
v___x_1967_ = ((size_t)1ULL);
v___x_1968_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1962_, v___x_1966_, v___x_1967_, v_x_1963_, v_x_1964_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(lean_object* v_old2new_1969_, lean_object* v_x_1970_, lean_object* v_____s_1971_){
_start:
{
lean_object* v_fst_1972_; lean_object* v_snd_1973_; lean_object* v___x_1974_; lean_object* v_m_x27_1975_; lean_object* v___x_1976_; 
v_fst_1972_ = lean_ctor_get(v_x_1970_, 0);
lean_inc(v_fst_1972_);
v_snd_1973_ = lean_ctor_get(v_x_1970_, 1);
lean_inc(v_snd_1973_);
lean_dec_ref(v_x_1970_);
v___x_1974_ = l_Int_Internal_Linear_Poly_reorder(v_fst_1972_, v_old2new_1969_);
v_m_x27_1975_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(v_____s_1971_, v___x_1974_, v_snd_1973_);
v___x_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1976_, 0, v_m_x27_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed(lean_object* v_old2new_1977_, lean_object* v_x_1978_, lean_object* v_____s_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(v_old2new_1977_, v_x_1978_, v_____s_1979_);
lean_dec_ref(v_old2new_1977_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_f_1981_, lean_object* v_keys_1982_, lean_object* v_vals_1983_, lean_object* v_i_1984_, lean_object* v_acc_1985_){
_start:
{
lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1986_ = lean_array_get_size(v_keys_1982_);
v___x_1987_ = lean_nat_dec_lt(v_i_1984_, v___x_1986_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; 
lean_dec(v_i_1984_);
lean_dec_ref(v_f_1981_);
v___x_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1988_, 0, v_acc_1985_);
return v___x_1988_;
}
else
{
lean_object* v_k_1989_; lean_object* v_v_1990_; lean_object* v___x_1991_; 
v_k_1989_ = lean_array_fget_borrowed(v_keys_1982_, v_i_1984_);
v_v_1990_ = lean_array_fget_borrowed(v_vals_1983_, v_i_1984_);
lean_inc_ref(v_f_1981_);
lean_inc(v_v_1990_);
lean_inc(v_k_1989_);
v___x_1991_ = lean_apply_3(v_f_1981_, v_acc_1985_, v_k_1989_, v_v_1990_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_dec(v_i_1984_);
lean_dec_ref(v_f_1981_);
return v___x_1991_;
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v___x_1993_ = lean_unsigned_to_nat(1u);
v___x_1994_ = lean_nat_add(v_i_1984_, v___x_1993_);
lean_dec(v_i_1984_);
v_i_1984_ = v___x_1994_;
v_acc_1985_ = v_a_1992_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_f_1996_, lean_object* v_keys_1997_, lean_object* v_vals_1998_, lean_object* v_i_1999_, lean_object* v_acc_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1996_, v_keys_1997_, v_vals_1998_, v_i_1999_, v_acc_2000_);
lean_dec_ref(v_vals_1998_);
lean_dec_ref(v_keys_1997_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_f_2002_, lean_object* v_as_2003_, size_t v_i_2004_, size_t v_stop_2005_, lean_object* v_b_2006_){
_start:
{
lean_object* v_a_2008_; lean_object* v___y_2013_; uint8_t v___x_2015_; 
v___x_2015_ = lean_usize_dec_eq(v_i_2004_, v_stop_2005_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_array_uget_borrowed(v_as_2003_, v_i_2004_);
switch(lean_obj_tag(v___x_2016_))
{
case 0:
{
lean_object* v_key_2017_; lean_object* v_val_2018_; lean_object* v___x_2019_; 
v_key_2017_ = lean_ctor_get(v___x_2016_, 0);
v_val_2018_ = lean_ctor_get(v___x_2016_, 1);
lean_inc_ref(v_f_2002_);
lean_inc(v_val_2018_);
lean_inc(v_key_2017_);
v___x_2019_ = lean_apply_3(v_f_2002_, v_b_2006_, v_key_2017_, v_val_2018_);
v___y_2013_ = v___x_2019_;
goto v___jp_2012_;
}
case 1:
{
lean_object* v_node_2020_; lean_object* v___x_2021_; 
v_node_2020_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_node_2020_);
lean_inc_ref(v_f_2002_);
v___x_2021_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_2002_, v_node_2020_, v_b_2006_);
v___y_2013_ = v___x_2021_;
goto v___jp_2012_;
}
default: 
{
v_a_2008_ = v_b_2006_;
goto v___jp_2007_;
}
}
}
else
{
lean_object* v___x_2022_; 
lean_dec_ref(v_f_2002_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_b_2006_);
return v___x_2022_;
}
v___jp_2007_:
{
size_t v___x_2009_; size_t v___x_2010_; 
v___x_2009_ = ((size_t)1ULL);
v___x_2010_ = lean_usize_add(v_i_2004_, v___x_2009_);
v_i_2004_ = v___x_2010_;
v_b_2006_ = v_a_2008_;
goto _start;
}
v___jp_2012_:
{
if (lean_obj_tag(v___y_2013_) == 0)
{
lean_dec_ref(v_f_2002_);
return v___y_2013_;
}
else
{
lean_object* v_a_2014_; 
v_a_2014_ = lean_ctor_get(v___y_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___y_2013_, 1);
v_a_2008_ = v_a_2014_;
goto v___jp_2007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(lean_object* v_f_2023_, lean_object* v_x_2024_, lean_object* v_x_2025_){
_start:
{
if (lean_obj_tag(v_x_2024_) == 0)
{
lean_object* v_es_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2039_; 
v_es_2026_ = lean_ctor_get(v_x_2024_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_x_2024_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2028_ = v_x_2024_;
v_isShared_2029_ = v_isSharedCheck_2039_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_es_2026_);
lean_dec(v_x_2024_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2039_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
v___x_2030_ = lean_unsigned_to_nat(0u);
v___x_2031_ = lean_array_get_size(v_es_2026_);
v___x_2032_ = lean_nat_dec_lt(v___x_2030_, v___x_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2034_; 
lean_dec_ref(v_es_2026_);
lean_dec_ref(v_f_2023_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 1);
lean_ctor_set(v___x_2028_, 0, v_x_2025_);
v___x_2034_ = v___x_2028_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_x_2025_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
else
{
size_t v___x_2036_; size_t v___x_2037_; lean_object* v___x_2038_; 
lean_del_object(v___x_2028_);
v___x_2036_ = ((size_t)0ULL);
v___x_2037_ = lean_usize_of_nat(v___x_2031_);
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_2023_, v_es_2026_, v___x_2036_, v___x_2037_, v_x_2025_);
lean_dec_ref(v_es_2026_);
return v___x_2038_;
}
}
}
else
{
lean_object* v_ks_2040_; lean_object* v_vs_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_ks_2040_ = lean_ctor_get(v_x_2024_, 0);
lean_inc_ref(v_ks_2040_);
v_vs_2041_ = lean_ctor_get(v_x_2024_, 1);
lean_inc_ref(v_vs_2041_);
lean_dec_ref_known(v_x_2024_, 2);
v___x_2042_ = lean_unsigned_to_nat(0u);
v___x_2043_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_2023_, v_ks_2040_, v_vs_2041_, v___x_2042_, v_x_2025_);
lean_dec_ref(v_vs_2041_);
lean_dec_ref(v_ks_2040_);
return v___x_2043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_f_2044_, lean_object* v_as_2045_, lean_object* v_i_2046_, lean_object* v_stop_2047_, lean_object* v_b_2048_){
_start:
{
size_t v_i_boxed_2049_; size_t v_stop_boxed_2050_; lean_object* v_res_2051_; 
v_i_boxed_2049_ = lean_unbox_usize(v_i_2046_);
lean_dec(v_i_2046_);
v_stop_boxed_2050_ = lean_unbox_usize(v_stop_2047_);
lean_dec(v_stop_2047_);
v_res_2051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_2044_, v_as_2045_, v_i_boxed_2049_, v_stop_boxed_2050_, v_b_2048_);
lean_dec_ref(v_as_2045_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0(lean_object* v_f_2052_, lean_object* v_s_2053_, lean_object* v_a_2054_, lean_object* v_b_2055_){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2056_, 0, v_a_2054_);
lean_ctor_set(v___x_2056_, 1, v_b_2055_);
v___x_2057_ = lean_apply_2(v_f_2052_, v___x_2056_, v_s_2053_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
v_a_2066_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2057_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2057_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(lean_object* v_map_2074_, lean_object* v_init_2075_, lean_object* v_f_2076_){
_start:
{
lean_object* v___f_2077_; lean_object* v___x_2078_; lean_object* v_a_2079_; 
v___f_2077_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2077_, 0, v_f_2076_);
lean_inc_ref(v_map_2074_);
v___x_2078_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v___f_2077_, v_map_2074_, v_init_2075_);
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref(v___x_2078_);
return v_a_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___boxed(lean_object* v_map_2080_, lean_object* v_init_2081_, lean_object* v_f_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_map_2080_, v_init_2081_, v_f_2082_);
lean_dec_ref(v_map_2080_);
return v_res_2083_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0(void){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2084_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1(void){
_start:
{
lean_object* v___x_2085_; lean_object* v_m_x27_2086_; 
v___x_2085_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0);
v_m_x27_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_m_x27_2086_, 0, v___x_2085_);
return v_m_x27_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(lean_object* v_m_2087_, lean_object* v_old2new_2088_){
_start:
{
lean_object* v___f_2089_; lean_object* v_m_x27_2090_; lean_object* v___x_2091_; 
v___f_2089_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2089_, 0, v_old2new_2088_);
v_m_x27_2090_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1);
v___x_2091_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_m_2087_, v_m_x27_2090_, v___f_2089_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___boxed(lean_object* v_m_2092_, lean_object* v_old2new_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(v_m_2092_, v_old2new_2093_);
lean_dec_ref(v_m_2092_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0(lean_object* v_00_u03b2_2095_, lean_object* v_x_2096_, lean_object* v_x_2097_, lean_object* v_x_2098_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(v_x_2096_, v_x_2097_, v_x_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(lean_object* v_00_u03c3_2100_, lean_object* v_00_u03b2_2101_, lean_object* v_map_2102_, lean_object* v_init_2103_, lean_object* v_f_2104_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_map_2102_, v_init_2103_, v_f_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___boxed(lean_object* v_00_u03c3_2106_, lean_object* v_00_u03b2_2107_, lean_object* v_map_2108_, lean_object* v_init_2109_, lean_object* v_f_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(v_00_u03c3_2106_, v_00_u03b2_2107_, v_map_2108_, v_init_2109_, v_f_2110_);
lean_dec_ref(v_map_2108_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(lean_object* v_00_u03b2_2112_, lean_object* v_x_2113_, size_t v_x_2114_, size_t v_x_2115_, lean_object* v_x_2116_, lean_object* v_x_2117_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_2113_, v_x_2114_, v_x_2115_, v_x_2116_, v_x_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2119_, lean_object* v_x_2120_, lean_object* v_x_2121_, lean_object* v_x_2122_, lean_object* v_x_2123_, lean_object* v_x_2124_){
_start:
{
size_t v_x_2093__boxed_2125_; size_t v_x_2094__boxed_2126_; lean_object* v_res_2127_; 
v_x_2093__boxed_2125_ = lean_unbox_usize(v_x_2121_);
lean_dec(v_x_2121_);
v_x_2094__boxed_2126_ = lean_unbox_usize(v_x_2122_);
lean_dec(v_x_2122_);
v_res_2127_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(v_00_u03b2_2119_, v_x_2120_, v_x_2093__boxed_2125_, v_x_2094__boxed_2126_, v_x_2123_, v_x_2124_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2___redArg(lean_object* v_map_2128_, lean_object* v_f_2129_, lean_object* v_init_2130_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_2129_, v_map_2128_, v_init_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2(lean_object* v_00_u03c3_2132_, lean_object* v_00_u03c3_2133_, lean_object* v_00_u03b2_2134_, lean_object* v_map_2135_, lean_object* v_f_2136_, lean_object* v_init_2137_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_2136_, v_map_2135_, v_init_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2139_, lean_object* v_n_2140_, lean_object* v_k_2141_, lean_object* v_v_2142_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(v_n_2140_, v_k_2141_, v_v_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2144_, size_t v_depth_2145_, lean_object* v_keys_2146_, lean_object* v_vals_2147_, lean_object* v_heq_2148_, lean_object* v_i_2149_, lean_object* v_entries_2150_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_2145_, v_keys_2146_, v_vals_2147_, v_i_2149_, v_entries_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2152_, lean_object* v_depth_2153_, lean_object* v_keys_2154_, lean_object* v_vals_2155_, lean_object* v_heq_2156_, lean_object* v_i_2157_, lean_object* v_entries_2158_){
_start:
{
size_t v_depth_boxed_2159_; lean_object* v_res_2160_; 
v_depth_boxed_2159_ = lean_unbox_usize(v_depth_2153_);
lean_dec(v_depth_2153_);
v_res_2160_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(v_00_u03b2_2152_, v_depth_boxed_2159_, v_keys_2154_, v_vals_2155_, v_heq_2156_, v_i_2157_, v_entries_2158_);
lean_dec_ref(v_vals_2155_);
lean_dec_ref(v_keys_2154_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5(lean_object* v_00_u03c3_2161_, lean_object* v_00_u03c3_2162_, lean_object* v_00_u03b1_2163_, lean_object* v_00_u03b2_2164_, lean_object* v_f_2165_, lean_object* v_x_2166_, lean_object* v_x_2167_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_2165_, v_x_2166_, v_x_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2169_, lean_object* v_x_2170_, lean_object* v_x_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2170_, v_x_2171_, v_x_2172_, v_x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2175_, lean_object* v_00_u03b2_2176_, lean_object* v_00_u03c3_2177_, lean_object* v_00_u03c3_2178_, lean_object* v_f_2179_, lean_object* v_as_2180_, size_t v_i_2181_, size_t v_stop_2182_, lean_object* v_b_2183_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_2179_, v_as_2180_, v_i_2181_, v_stop_2182_, v_b_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2185_, lean_object* v_00_u03b2_2186_, lean_object* v_00_u03c3_2187_, lean_object* v_00_u03c3_2188_, lean_object* v_f_2189_, lean_object* v_as_2190_, lean_object* v_i_2191_, lean_object* v_stop_2192_, lean_object* v_b_2193_){
_start:
{
size_t v_i_boxed_2194_; size_t v_stop_boxed_2195_; lean_object* v_res_2196_; 
v_i_boxed_2194_ = lean_unbox_usize(v_i_2191_);
lean_dec(v_i_2191_);
v_stop_boxed_2195_ = lean_unbox_usize(v_stop_2192_);
lean_dec(v_stop_2192_);
v_res_2196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2185_, v_00_u03b2_2186_, v_00_u03c3_2187_, v_00_u03c3_2188_, v_f_2189_, v_as_2190_, v_i_boxed_2194_, v_stop_boxed_2195_, v_b_2193_);
lean_dec_ref(v_as_2190_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03c3_2197_, lean_object* v_00_u03c3_2198_, lean_object* v_00_u03b1_2199_, lean_object* v_00_u03b2_2200_, lean_object* v_f_2201_, lean_object* v_keys_2202_, lean_object* v_vals_2203_, lean_object* v_heq_2204_, lean_object* v_i_2205_, lean_object* v_acc_2206_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_2201_, v_keys_2202_, v_vals_2203_, v_i_2205_, v_acc_2206_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03c3_2208_, lean_object* v_00_u03c3_2209_, lean_object* v_00_u03b1_2210_, lean_object* v_00_u03b2_2211_, lean_object* v_f_2212_, lean_object* v_keys_2213_, lean_object* v_vals_2214_, lean_object* v_heq_2215_, lean_object* v_i_2216_, lean_object* v_acc_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(v_00_u03c3_2208_, v_00_u03c3_2209_, v_00_u03b1_2210_, v_00_u03b2_2211_, v_f_2212_, v_keys_2213_, v_vals_2214_, v_heq_2215_, v_i_2216_, v_acc_2217_);
lean_dec_ref(v_vals_2214_);
lean_dec_ref(v_keys_2213_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(lean_object* v___x_2219_, lean_object* v___x_2220_, lean_object* v_x_2221_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = lean_array_get_borrowed(v___x_2219_, v___x_2220_, v_x_2221_);
lean_inc(v___x_2222_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed(lean_object* v___x_2223_, lean_object* v___x_2224_, lean_object* v_x_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(v___x_2223_, v___x_2224_, v_x_2225_);
lean_dec(v_x_2225_);
lean_dec_ref(v___x_2224_);
lean_dec(v___x_2223_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__32(size_t v_sz_2227_, size_t v_i_2228_, lean_object* v_bs_2229_){
_start:
{
uint8_t v___x_2230_; 
v___x_2230_ = lean_usize_dec_lt(v_i_2228_, v_sz_2227_);
if (v___x_2230_ == 0)
{
return v_bs_2229_;
}
else
{
lean_object* v___x_2231_; lean_object* v_bs_x27_2232_; lean_object* v___x_2233_; size_t v___x_2234_; size_t v___x_2235_; lean_object* v___x_2236_; 
v___x_2231_ = lean_unsigned_to_nat(0u);
v_bs_x27_2232_ = lean_array_uset(v_bs_2229_, v_i_2228_, v___x_2231_);
v___x_2233_ = lean_box(1);
v___x_2234_ = ((size_t)1ULL);
v___x_2235_ = lean_usize_add(v_i_2228_, v___x_2234_);
v___x_2236_ = lean_array_uset(v_bs_x27_2232_, v_i_2228_, v___x_2233_);
v_i_2228_ = v___x_2235_;
v_bs_2229_ = v___x_2236_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__32___boxed(lean_object* v_sz_2238_, lean_object* v_i_2239_, lean_object* v_bs_2240_){
_start:
{
size_t v_sz_boxed_2241_; size_t v_i_boxed_2242_; lean_object* v_res_2243_; 
v_sz_boxed_2241_ = lean_unbox_usize(v_sz_2238_);
lean_dec(v_sz_2238_);
v_i_boxed_2242_ = lean_unbox_usize(v_i_2239_);
lean_dec(v_i_2239_);
v_res_2243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__32(v_sz_boxed_2241_, v_i_boxed_2242_, v_bs_2240_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__31_spec__40(size_t v_sz_2244_, size_t v_i_2245_, lean_object* v_bs_2246_){
_start:
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_usize_dec_lt(v_i_2245_, v_sz_2244_);
if (v___x_2247_ == 0)
{
return v_bs_2246_;
}
else
{
lean_object* v_v_2248_; lean_object* v___x_2249_; lean_object* v_bs_x27_2250_; lean_object* v___x_2251_; size_t v___x_2252_; size_t v___x_2253_; lean_object* v___x_2254_; 
v_v_2248_ = lean_array_uget(v_bs_2246_, v_i_2245_);
v___x_2249_ = lean_unsigned_to_nat(0u);
v_bs_x27_2250_ = lean_array_uset(v_bs_2246_, v_i_2245_, v___x_2249_);
v___x_2251_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__31(v_v_2248_);
v___x_2252_ = ((size_t)1ULL);
v___x_2253_ = lean_usize_add(v_i_2245_, v___x_2252_);
v___x_2254_ = lean_array_uset(v_bs_x27_2250_, v_i_2245_, v___x_2251_);
v_i_2245_ = v___x_2253_;
v_bs_2246_ = v___x_2254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__31(lean_object* v_x_2256_){
_start:
{
if (lean_obj_tag(v_x_2256_) == 0)
{
lean_object* v_cs_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2267_; 
v_cs_2257_ = lean_ctor_get(v_x_2256_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_x_2256_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2259_ = v_x_2256_;
v_isShared_2260_ = v_isSharedCheck_2267_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_cs_2257_);
lean_dec(v_x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2267_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
size_t v_sz_2261_; size_t v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2265_; 
v_sz_2261_ = lean_array_size(v_cs_2257_);
v___x_2262_ = ((size_t)0ULL);
v___x_2263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__31_spec__40(v_sz_2261_, v___x_2262_, v_cs_2257_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2263_);
v___x_2265_ = v___x_2259_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
else
{
lean_object* v_vs_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2278_; 
v_vs_2268_ = lean_ctor_get(v_x_2256_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_x_2256_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2270_ = v_x_2256_;
v_isShared_2271_ = v_isSharedCheck_2278_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_vs_2268_);
lean_dec(v_x_2256_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2278_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
size_t v_sz_2272_; size_t v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v_sz_2272_ = lean_array_size(v_vs_2268_);
v___x_2273_ = ((size_t)0ULL);
v___x_2274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__32(v_sz_2272_, v___x_2273_, v_vs_2268_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 0, v___x_2274_);
v___x_2276_ = v___x_2270_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__31_spec__40___boxed(lean_object* v_sz_2279_, lean_object* v_i_2280_, lean_object* v_bs_2281_){
_start:
{
size_t v_sz_boxed_2282_; size_t v_i_boxed_2283_; lean_object* v_res_2284_; 
v_sz_boxed_2282_ = lean_unbox_usize(v_sz_2279_);
lean_dec(v_sz_2279_);
v_i_boxed_2283_ = lean_unbox_usize(v_i_2280_);
lean_dec(v_i_2280_);
v_res_2284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__31_spec__40(v_sz_boxed_2282_, v_i_boxed_2283_, v_bs_2281_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(lean_object* v_t_2285_){
_start:
{
lean_object* v_root_2286_; lean_object* v_tail_2287_; lean_object* v_size_2288_; size_t v_shift_2289_; lean_object* v_tailOff_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2301_; 
v_root_2286_ = lean_ctor_get(v_t_2285_, 0);
v_tail_2287_ = lean_ctor_get(v_t_2285_, 1);
v_size_2288_ = lean_ctor_get(v_t_2285_, 2);
v_shift_2289_ = lean_ctor_get_usize(v_t_2285_, 4);
v_tailOff_2290_ = lean_ctor_get(v_t_2285_, 3);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_t_2285_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2292_ = v_t_2285_;
v_isShared_2293_ = v_isSharedCheck_2301_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_tailOff_2290_);
lean_inc(v_size_2288_);
lean_inc(v_tail_2287_);
lean_inc(v_root_2286_);
lean_dec(v_t_2285_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2301_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2294_; size_t v_sz_2295_; size_t v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2294_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__31(v_root_2286_);
v_sz_2295_ = lean_array_size(v_tail_2287_);
v___x_2296_ = ((size_t)0ULL);
v___x_2297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_spec__32(v_sz_2295_, v___x_2296_, v_tail_2287_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 1, v___x_2297_);
lean_ctor_set(v___x_2292_, 0, v___x_2294_);
v___x_2299_ = v___x_2292_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v___x_2297_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_size_2288_);
lean_ctor_set(v_reuseFailAlloc_2300_, 3, v_tailOff_2290_);
lean_ctor_set_usize(v_reuseFailAlloc_2300_, 4, v_shift_2289_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(lean_object* v___x_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
if (lean_obj_tag(v_a_2303_) == 0)
{
lean_object* v___x_2305_; 
v___x_2305_ = l_List_reverse___redArg(v_a_2304_);
return v___x_2305_;
}
else
{
lean_object* v_head_2306_; lean_object* v_tail_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2317_; 
v_head_2306_ = lean_ctor_get(v_a_2303_, 0);
v_tail_2307_ = lean_ctor_get(v_a_2303_, 1);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_a_2303_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2309_ = v_a_2303_;
v_isShared_2310_ = v_isSharedCheck_2317_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_tail_2307_);
lean_inc(v_head_2306_);
lean_dec(v_a_2303_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2317_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2314_; 
v___x_2311_ = lean_unsigned_to_nat(0u);
v___x_2312_ = lean_array_get_borrowed(v___x_2311_, v___x_2302_, v_head_2306_);
lean_dec(v_head_2306_);
lean_inc(v___x_2312_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 1, v_a_2304_);
lean_ctor_set(v___x_2309_, 0, v___x_2312_);
v___x_2314_ = v___x_2309_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_a_2304_);
v___x_2314_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
v_a_2303_ = v_tail_2307_;
v_a_2304_ = v___x_2314_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12___boxed(lean_object* v___x_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v___x_2318_, v_a_2319_, v_a_2320_);
lean_dec_ref(v___x_2318_);
return v_res_2321_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___closed__0(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2322_ = lean_unsigned_to_nat(32u);
v___x_2323_ = lean_mk_empty_array_with_capacity(v___x_2322_);
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
return v___x_2324_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___closed__1(void){
_start:
{
size_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2325_ = ((size_t)5ULL);
v___x_2326_ = lean_unsigned_to_nat(0u);
v___x_2327_ = lean_unsigned_to_nat(32u);
v___x_2328_ = lean_mk_empty_array_with_capacity(v___x_2327_);
v___x_2329_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___closed__0);
v___x_2330_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2330_, 0, v___x_2329_);
lean_ctor_set(v___x_2330_, 1, v___x_2328_);
lean_ctor_set(v___x_2330_, 2, v___x_2326_);
lean_ctor_set(v___x_2330_, 3, v___x_2326_);
lean_ctor_set_usize(v___x_2330_, 4, v___x_2325_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(size_t v_sz_2331_, size_t v_i_2332_, lean_object* v_bs_2333_){
_start:
{
uint8_t v___x_2334_; 
v___x_2334_ = lean_usize_dec_lt(v_i_2332_, v_sz_2331_);
if (v___x_2334_ == 0)
{
return v_bs_2333_;
}
else
{
lean_object* v___x_2335_; lean_object* v_bs_x27_2336_; lean_object* v___x_2337_; size_t v___x_2338_; size_t v___x_2339_; lean_object* v___x_2340_; 
v___x_2335_ = lean_unsigned_to_nat(0u);
v_bs_x27_2336_ = lean_array_uset(v_bs_2333_, v_i_2332_, v___x_2335_);
v___x_2337_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___closed__1);
v___x_2338_ = ((size_t)1ULL);
v___x_2339_ = lean_usize_add(v_i_2332_, v___x_2338_);
v___x_2340_ = lean_array_uset(v_bs_x27_2336_, v_i_2332_, v___x_2337_);
v_i_2332_ = v___x_2339_;
v_bs_2333_ = v___x_2340_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___boxed(lean_object* v_sz_2342_, lean_object* v_i_2343_, lean_object* v_bs_2344_){
_start:
{
size_t v_sz_boxed_2345_; size_t v_i_boxed_2346_; lean_object* v_res_2347_; 
v_sz_boxed_2345_ = lean_unbox_usize(v_sz_2342_);
lean_dec(v_sz_2342_);
v_i_boxed_2346_ = lean_unbox_usize(v_i_2343_);
lean_dec(v_i_2343_);
v_res_2347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_sz_boxed_2345_, v_i_boxed_2346_, v_bs_2344_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__31(size_t v_sz_2348_, size_t v_i_2349_, lean_object* v_bs_2350_){
_start:
{
uint8_t v___x_2351_; 
v___x_2351_ = lean_usize_dec_lt(v_i_2349_, v_sz_2348_);
if (v___x_2351_ == 0)
{
return v_bs_2350_;
}
else
{
lean_object* v_v_2352_; lean_object* v___x_2353_; lean_object* v_bs_x27_2354_; lean_object* v___x_2355_; size_t v___x_2356_; size_t v___x_2357_; lean_object* v___x_2358_; 
v_v_2352_ = lean_array_uget(v_bs_2350_, v_i_2349_);
v___x_2353_ = lean_unsigned_to_nat(0u);
v_bs_x27_2354_ = lean_array_uset(v_bs_2350_, v_i_2349_, v___x_2353_);
v___x_2355_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(v_v_2352_);
v___x_2356_ = ((size_t)1ULL);
v___x_2357_ = lean_usize_add(v_i_2349_, v___x_2356_);
v___x_2358_ = lean_array_uset(v_bs_x27_2354_, v_i_2349_, v___x_2355_);
v_i_2349_ = v___x_2357_;
v_bs_2350_ = v___x_2358_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(lean_object* v_x_2360_){
_start:
{
if (lean_obj_tag(v_x_2360_) == 0)
{
lean_object* v_cs_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2371_; 
v_cs_2361_ = lean_ctor_get(v_x_2360_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v_x_2360_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2363_ = v_x_2360_;
v_isShared_2364_ = v_isSharedCheck_2371_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_cs_2361_);
lean_dec(v_x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2371_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
size_t v_sz_2365_; size_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v_sz_2365_ = lean_array_size(v_cs_2361_);
v___x_2366_ = ((size_t)0ULL);
v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__31(v_sz_2365_, v___x_2366_, v_cs_2361_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2367_);
v___x_2369_ = v___x_2363_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
else
{
lean_object* v_vs_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2382_; 
v_vs_2372_ = lean_ctor_get(v_x_2360_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_x_2360_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2374_ = v_x_2360_;
v_isShared_2375_ = v_isSharedCheck_2382_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_vs_2372_);
lean_dec(v_x_2360_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2382_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
size_t v_sz_2376_; size_t v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2380_; 
v_sz_2376_ = lean_array_size(v_vs_2372_);
v___x_2377_ = ((size_t)0ULL);
v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_sz_2376_, v___x_2377_, v_vs_2372_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v___x_2378_);
v___x_2380_ = v___x_2374_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__31___boxed(lean_object* v_sz_2383_, lean_object* v_i_2384_, lean_object* v_bs_2385_){
_start:
{
size_t v_sz_boxed_2386_; size_t v_i_boxed_2387_; lean_object* v_res_2388_; 
v_sz_boxed_2386_ = lean_unbox_usize(v_sz_2383_);
lean_dec(v_sz_2383_);
v_i_boxed_2387_ = lean_unbox_usize(v_i_2384_);
lean_dec(v_i_2384_);
v_res_2388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__31(v_sz_boxed_2386_, v_i_boxed_2387_, v_bs_2385_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(lean_object* v_t_2389_){
_start:
{
lean_object* v_root_2390_; lean_object* v_tail_2391_; lean_object* v_size_2392_; size_t v_shift_2393_; lean_object* v_tailOff_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2405_; 
v_root_2390_ = lean_ctor_get(v_t_2389_, 0);
v_tail_2391_ = lean_ctor_get(v_t_2389_, 1);
v_size_2392_ = lean_ctor_get(v_t_2389_, 2);
v_shift_2393_ = lean_ctor_get_usize(v_t_2389_, 4);
v_tailOff_2394_ = lean_ctor_get(v_t_2389_, 3);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_t_2389_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2396_ = v_t_2389_;
v_isShared_2397_ = v_isSharedCheck_2405_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_tailOff_2394_);
lean_inc(v_size_2392_);
lean_inc(v_tail_2391_);
lean_inc(v_root_2390_);
lean_dec(v_t_2389_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2405_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; size_t v_sz_2399_; size_t v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2398_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(v_root_2390_);
v_sz_2399_ = lean_array_size(v_tail_2391_);
v___x_2400_ = ((size_t)0ULL);
v___x_2401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_sz_2399_, v___x_2400_, v_tail_2391_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 1, v___x_2401_);
lean_ctor_set(v___x_2396_, 0, v___x_2398_);
v___x_2403_ = v___x_2396_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2404_, 2, v_size_2392_);
lean_ctor_set(v_reuseFailAlloc_2404_, 3, v_tailOff_2394_);
lean_ctor_set_usize(v_reuseFailAlloc_2404_, 4, v_shift_2393_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(size_t v_sz_2406_, size_t v_i_2407_, lean_object* v_bs_2408_){
_start:
{
uint8_t v___x_2409_; 
v___x_2409_ = lean_usize_dec_lt(v_i_2407_, v_sz_2406_);
if (v___x_2409_ == 0)
{
return v_bs_2408_;
}
else
{
lean_object* v___x_2410_; lean_object* v_bs_x27_2411_; lean_object* v___x_2412_; size_t v___x_2413_; size_t v___x_2414_; lean_object* v___x_2415_; 
v___x_2410_ = lean_unsigned_to_nat(0u);
v_bs_x27_2411_ = lean_array_uset(v_bs_2408_, v_i_2407_, v___x_2410_);
v___x_2412_ = lean_box(0);
v___x_2413_ = ((size_t)1ULL);
v___x_2414_ = lean_usize_add(v_i_2407_, v___x_2413_);
v___x_2415_ = lean_array_uset(v_bs_x27_2411_, v_i_2407_, v___x_2412_);
v_i_2407_ = v___x_2414_;
v_bs_2408_ = v___x_2415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___boxed(lean_object* v_sz_2417_, lean_object* v_i_2418_, lean_object* v_bs_2419_){
_start:
{
size_t v_sz_boxed_2420_; size_t v_i_boxed_2421_; lean_object* v_res_2422_; 
v_sz_boxed_2420_ = lean_unbox_usize(v_sz_2417_);
lean_dec(v_sz_2417_);
v_i_boxed_2421_ = lean_unbox_usize(v_i_2418_);
lean_dec(v_i_2418_);
v_res_2422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(v_sz_boxed_2420_, v_i_boxed_2421_, v_bs_2419_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__18_spec__23(size_t v_sz_2423_, size_t v_i_2424_, lean_object* v_bs_2425_){
_start:
{
uint8_t v___x_2426_; 
v___x_2426_ = lean_usize_dec_lt(v_i_2424_, v_sz_2423_);
if (v___x_2426_ == 0)
{
return v_bs_2425_;
}
else
{
lean_object* v_v_2427_; lean_object* v___x_2428_; lean_object* v_bs_x27_2429_; lean_object* v___x_2430_; size_t v___x_2431_; size_t v___x_2432_; lean_object* v___x_2433_; 
v_v_2427_ = lean_array_uget(v_bs_2425_, v_i_2424_);
v___x_2428_ = lean_unsigned_to_nat(0u);
v_bs_x27_2429_ = lean_array_uset(v_bs_2425_, v_i_2424_, v___x_2428_);
v___x_2430_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__18(v_v_2427_);
v___x_2431_ = ((size_t)1ULL);
v___x_2432_ = lean_usize_add(v_i_2424_, v___x_2431_);
v___x_2433_ = lean_array_uset(v_bs_x27_2429_, v_i_2424_, v___x_2430_);
v_i_2424_ = v___x_2432_;
v_bs_2425_ = v___x_2433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__18(lean_object* v_x_2435_){
_start:
{
if (lean_obj_tag(v_x_2435_) == 0)
{
lean_object* v_cs_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2446_; 
v_cs_2436_ = lean_ctor_get(v_x_2435_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v_x_2435_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2438_ = v_x_2435_;
v_isShared_2439_ = v_isSharedCheck_2446_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_cs_2436_);
lean_dec(v_x_2435_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2446_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
size_t v_sz_2440_; size_t v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2444_; 
v_sz_2440_ = lean_array_size(v_cs_2436_);
v___x_2441_ = ((size_t)0ULL);
v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__18_spec__23(v_sz_2440_, v___x_2441_, v_cs_2436_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v___x_2442_);
v___x_2444_ = v___x_2438_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2442_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
else
{
lean_object* v_vs_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2457_; 
v_vs_2447_ = lean_ctor_get(v_x_2435_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_x_2435_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2449_ = v_x_2435_;
v_isShared_2450_ = v_isSharedCheck_2457_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_vs_2447_);
lean_dec(v_x_2435_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2457_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
size_t v_sz_2451_; size_t v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
v_sz_2451_ = lean_array_size(v_vs_2447_);
v___x_2452_ = ((size_t)0ULL);
v___x_2453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(v_sz_2451_, v___x_2452_, v_vs_2447_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2453_);
v___x_2455_ = v___x_2449_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__18_spec__23___boxed(lean_object* v_sz_2458_, lean_object* v_i_2459_, lean_object* v_bs_2460_){
_start:
{
size_t v_sz_boxed_2461_; size_t v_i_boxed_2462_; lean_object* v_res_2463_; 
v_sz_boxed_2461_ = lean_unbox_usize(v_sz_2458_);
lean_dec(v_sz_2458_);
v_i_boxed_2462_ = lean_unbox_usize(v_i_2459_);
lean_dec(v_i_2459_);
v_res_2463_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__18_spec__23(v_sz_boxed_2461_, v_i_boxed_2462_, v_bs_2460_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(lean_object* v_t_2464_){
_start:
{
lean_object* v_root_2465_; lean_object* v_tail_2466_; lean_object* v_size_2467_; size_t v_shift_2468_; lean_object* v_tailOff_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2480_; 
v_root_2465_ = lean_ctor_get(v_t_2464_, 0);
v_tail_2466_ = lean_ctor_get(v_t_2464_, 1);
v_size_2467_ = lean_ctor_get(v_t_2464_, 2);
v_shift_2468_ = lean_ctor_get_usize(v_t_2464_, 4);
v_tailOff_2469_ = lean_ctor_get(v_t_2464_, 3);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_t_2464_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2471_ = v_t_2464_;
v_isShared_2472_ = v_isSharedCheck_2480_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_tailOff_2469_);
lean_inc(v_size_2467_);
lean_inc(v_tail_2466_);
lean_inc(v_root_2465_);
lean_dec(v_t_2464_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2480_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; size_t v_sz_2474_; size_t v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2473_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__18(v_root_2465_);
v_sz_2474_ = lean_array_size(v_tail_2466_);
v___x_2475_ = ((size_t)0ULL);
v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(v_sz_2474_, v___x_2475_, v_tail_2466_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 1, v___x_2476_);
lean_ctor_set(v___x_2471_, 0, v___x_2473_);
v___x_2478_ = v___x_2471_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2476_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v_size_2467_);
lean_ctor_set(v_reuseFailAlloc_2479_, 3, v_tailOff_2469_);
lean_ctor_set_usize(v_reuseFailAlloc_2479_, 4, v_shift_2468_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__28(lean_object* v___x_2481_, lean_object* v_a_2482_, size_t v_sz_2483_, size_t v_i_2484_, lean_object* v_bs_2485_){
_start:
{
uint8_t v___x_2486_; 
v___x_2486_ = lean_usize_dec_lt(v_i_2484_, v_sz_2483_);
if (v___x_2486_ == 0)
{
lean_dec(v_a_2482_);
return v_bs_2485_;
}
else
{
lean_object* v_v_2487_; lean_object* v___x_2488_; lean_object* v_bs_x27_2489_; lean_object* v___y_2491_; 
v_v_2487_ = lean_array_uget(v_bs_2485_, v_i_2484_);
v___x_2488_ = lean_unsigned_to_nat(0u);
v_bs_x27_2489_ = lean_array_uset(v_bs_2485_, v_i_2484_, v___x_2488_);
if (lean_obj_tag(v_v_2487_) == 0)
{
v___y_2491_ = v_v_2487_;
goto v___jp_2490_;
}
else
{
lean_object* v_val_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2515_; 
v_val_2496_ = lean_ctor_get(v_v_2487_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v_v_2487_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2498_ = v_v_2487_;
v_isShared_2499_ = v_isSharedCheck_2515_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_val_2496_);
lean_dec(v_v_2487_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2515_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v_p_2501_; lean_object* v_h_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2513_; 
v___x_2500_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_val_2496_, v___x_2481_);
v_p_2501_ = lean_ctor_get(v___x_2500_, 0);
v_h_2502_ = lean_ctor_get(v___x_2500_, 1);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2513_ == 0)
{
lean_object* v_unused_2514_; 
v_unused_2514_ = lean_ctor_get(v___x_2500_, 2);
lean_dec(v_unused_2514_);
v___x_2504_ = v___x_2500_;
v_isShared_2505_ = v_isSharedCheck_2513_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_h_2502_);
lean_inc(v_p_2501_);
lean_dec(v___x_2500_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2513_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
lean_inc(v_a_2482_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v_a_2482_);
v___x_2507_ = v___x_2498_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2482_);
v___x_2507_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2509_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 2, v___x_2507_);
v___x_2509_ = v___x_2504_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_p_2501_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_h_2502_);
lean_ctor_set(v_reuseFailAlloc_2511_, 2, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
v___y_2491_ = v___x_2510_;
goto v___jp_2490_;
}
}
}
}
}
v___jp_2490_:
{
size_t v___x_2492_; size_t v___x_2493_; lean_object* v___x_2494_; 
v___x_2492_ = ((size_t)1ULL);
v___x_2493_ = lean_usize_add(v_i_2484_, v___x_2492_);
v___x_2494_ = lean_array_uset(v_bs_x27_2489_, v_i_2484_, v___y_2491_);
v_i_2484_ = v___x_2493_;
v_bs_2485_ = v___x_2494_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__28___boxed(lean_object* v___x_2516_, lean_object* v_a_2517_, lean_object* v_sz_2518_, lean_object* v_i_2519_, lean_object* v_bs_2520_){
_start:
{
size_t v_sz_boxed_2521_; size_t v_i_boxed_2522_; lean_object* v_res_2523_; 
v_sz_boxed_2521_ = lean_unbox_usize(v_sz_2518_);
lean_dec(v_sz_2518_);
v_i_boxed_2522_ = lean_unbox_usize(v_i_2519_);
lean_dec(v_i_2519_);
v_res_2523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__28(v___x_2516_, v_a_2517_, v_sz_boxed_2521_, v_i_boxed_2522_, v_bs_2520_);
lean_dec_ref(v___x_2516_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__27_spec__35(lean_object* v___x_2524_, lean_object* v_a_2525_, size_t v_sz_2526_, size_t v_i_2527_, lean_object* v_bs_2528_){
_start:
{
uint8_t v___x_2529_; 
v___x_2529_ = lean_usize_dec_lt(v_i_2527_, v_sz_2526_);
if (v___x_2529_ == 0)
{
lean_dec(v_a_2525_);
return v_bs_2528_;
}
else
{
lean_object* v_v_2530_; lean_object* v___x_2531_; lean_object* v_bs_x27_2532_; lean_object* v___x_2533_; size_t v___x_2534_; size_t v___x_2535_; lean_object* v___x_2536_; 
v_v_2530_ = lean_array_uget(v_bs_2528_, v_i_2527_);
v___x_2531_ = lean_unsigned_to_nat(0u);
v_bs_x27_2532_ = lean_array_uset(v_bs_2528_, v_i_2527_, v___x_2531_);
lean_inc(v_a_2525_);
v___x_2533_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__27(v___x_2524_, v_a_2525_, v_v_2530_);
v___x_2534_ = ((size_t)1ULL);
v___x_2535_ = lean_usize_add(v_i_2527_, v___x_2534_);
v___x_2536_ = lean_array_uset(v_bs_x27_2532_, v_i_2527_, v___x_2533_);
v_i_2527_ = v___x_2535_;
v_bs_2528_ = v___x_2536_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__27(lean_object* v___x_2538_, lean_object* v_a_2539_, lean_object* v_x_2540_){
_start:
{
if (lean_obj_tag(v_x_2540_) == 0)
{
lean_object* v_cs_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2551_; 
v_cs_2541_ = lean_ctor_get(v_x_2540_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_x_2540_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2543_ = v_x_2540_;
v_isShared_2544_ = v_isSharedCheck_2551_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_cs_2541_);
lean_dec(v_x_2540_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2551_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
size_t v_sz_2545_; size_t v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2549_; 
v_sz_2545_ = lean_array_size(v_cs_2541_);
v___x_2546_ = ((size_t)0ULL);
v___x_2547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__27_spec__35(v___x_2538_, v_a_2539_, v_sz_2545_, v___x_2546_, v_cs_2541_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2547_);
v___x_2549_ = v___x_2543_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
else
{
lean_object* v_vs_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2562_; 
v_vs_2552_ = lean_ctor_get(v_x_2540_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_x_2540_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2554_ = v_x_2540_;
v_isShared_2555_ = v_isSharedCheck_2562_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_vs_2552_);
lean_dec(v_x_2540_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2562_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
size_t v_sz_2556_; size_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2560_; 
v_sz_2556_ = lean_array_size(v_vs_2552_);
v___x_2557_ = ((size_t)0ULL);
v___x_2558_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__28(v___x_2538_, v_a_2539_, v_sz_2556_, v___x_2557_, v_vs_2552_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v___x_2558_);
v___x_2560_ = v___x_2554_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__27___boxed(lean_object* v___x_2563_, lean_object* v_a_2564_, lean_object* v_x_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__27(v___x_2563_, v_a_2564_, v_x_2565_);
lean_dec_ref(v___x_2563_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__27_spec__35___boxed(lean_object* v___x_2567_, lean_object* v_a_2568_, lean_object* v_sz_2569_, lean_object* v_i_2570_, lean_object* v_bs_2571_){
_start:
{
size_t v_sz_boxed_2572_; size_t v_i_boxed_2573_; lean_object* v_res_2574_; 
v_sz_boxed_2572_ = lean_unbox_usize(v_sz_2569_);
lean_dec(v_sz_2569_);
v_i_boxed_2573_ = lean_unbox_usize(v_i_2570_);
lean_dec(v_i_2570_);
v_res_2574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__27_spec__35(v___x_2567_, v_a_2568_, v_sz_boxed_2572_, v_i_boxed_2573_, v_bs_2571_);
lean_dec_ref(v___x_2567_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(lean_object* v___x_2575_, lean_object* v_a_2576_, lean_object* v_t_2577_){
_start:
{
lean_object* v_root_2578_; lean_object* v_tail_2579_; lean_object* v_size_2580_; size_t v_shift_2581_; lean_object* v_tailOff_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2593_; 
v_root_2578_ = lean_ctor_get(v_t_2577_, 0);
v_tail_2579_ = lean_ctor_get(v_t_2577_, 1);
v_size_2580_ = lean_ctor_get(v_t_2577_, 2);
v_shift_2581_ = lean_ctor_get_usize(v_t_2577_, 4);
v_tailOff_2582_ = lean_ctor_get(v_t_2577_, 3);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_t_2577_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2584_ = v_t_2577_;
v_isShared_2585_ = v_isSharedCheck_2593_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_tailOff_2582_);
lean_inc(v_size_2580_);
lean_inc(v_tail_2579_);
lean_inc(v_root_2578_);
lean_dec(v_t_2577_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2593_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; size_t v_sz_2587_; size_t v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2591_; 
lean_inc(v_a_2576_);
v___x_2586_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__27(v___x_2575_, v_a_2576_, v_root_2578_);
v_sz_2587_ = lean_array_size(v_tail_2579_);
v___x_2588_ = ((size_t)0ULL);
v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_spec__28(v___x_2575_, v_a_2576_, v_sz_2587_, v___x_2588_, v_tail_2579_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 1, v___x_2589_);
lean_ctor_set(v___x_2584_, 0, v___x_2586_);
v___x_2591_ = v___x_2584_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2586_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v___x_2589_);
lean_ctor_set(v_reuseFailAlloc_2592_, 2, v_size_2580_);
lean_ctor_set(v_reuseFailAlloc_2592_, 3, v_tailOff_2582_);
lean_ctor_set_usize(v_reuseFailAlloc_2592_, 4, v_shift_2581_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11___boxed(lean_object* v___x_2594_, lean_object* v_a_2595_, lean_object* v_t_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v___x_2594_, v_a_2595_, v_t_2596_);
lean_dec_ref(v___x_2594_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34_spec__45___redArg(lean_object* v_f_2598_, lean_object* v_as_2599_, lean_object* v_i_2600_, lean_object* v_acc_2601_){
_start:
{
lean_object* v___x_2602_; uint8_t v___x_2603_; 
v___x_2602_ = lean_array_get_size(v_as_2599_);
v___x_2603_ = lean_nat_dec_eq(v_i_2600_, v___x_2602_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2604_ = lean_array_fget_borrowed(v_as_2599_, v_i_2600_);
lean_inc(v_f_2598_);
lean_inc(v___x_2604_);
v___x_2605_ = lean_apply_1(v_f_2598_, v___x_2604_);
v___x_2606_ = lean_unsigned_to_nat(1u);
v___x_2607_ = lean_nat_add(v_i_2600_, v___x_2606_);
lean_dec(v_i_2600_);
v___x_2608_ = lean_array_push(v_acc_2601_, v___x_2605_);
v_i_2600_ = v___x_2607_;
v_acc_2601_ = v___x_2608_;
goto _start;
}
else
{
lean_dec(v_i_2600_);
lean_dec(v_f_2598_);
return v_acc_2601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34_spec__45___redArg___boxed(lean_object* v_f_2610_, lean_object* v_as_2611_, lean_object* v_i_2612_, lean_object* v_acc_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34_spec__45___redArg(v_f_2610_, v_as_2611_, v_i_2612_, v_acc_2613_);
lean_dec_ref(v_as_2611_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34___redArg(lean_object* v_f_2615_, lean_object* v_as_2616_){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2617_ = lean_unsigned_to_nat(0u);
v___x_2618_ = lean_array_get_size(v_as_2616_);
v___x_2619_ = lean_mk_empty_array_with_capacity(v___x_2618_);
v___x_2620_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34_spec__45___redArg(v_f_2615_, v_as_2616_, v___x_2617_, v___x_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34___redArg___boxed(lean_object* v_f_2621_, lean_object* v_as_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34___redArg(v_f_2621_, v_as_2622_);
lean_dec_ref(v_as_2622_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__33___redArg(lean_object* v_f_2624_, size_t v_sz_2625_, size_t v_i_2626_, lean_object* v_bs_2627_){
_start:
{
uint8_t v___x_2628_; 
v___x_2628_ = lean_usize_dec_lt(v_i_2626_, v_sz_2625_);
if (v___x_2628_ == 0)
{
lean_dec(v_f_2624_);
return v_bs_2627_;
}
else
{
lean_object* v_v_2629_; lean_object* v___x_2630_; lean_object* v_bs_x27_2631_; lean_object* v___y_2633_; 
v_v_2629_ = lean_array_uget(v_bs_2627_, v_i_2626_);
v___x_2630_ = lean_unsigned_to_nat(0u);
v_bs_x27_2631_ = lean_array_uset(v_bs_2627_, v_i_2626_, v___x_2630_);
switch(lean_obj_tag(v_v_2629_))
{
case 0:
{
lean_object* v_key_2638_; lean_object* v_val_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2647_; 
v_key_2638_ = lean_ctor_get(v_v_2629_, 0);
v_val_2639_ = lean_ctor_get(v_v_2629_, 1);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_v_2629_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2641_ = v_v_2629_;
v_isShared_2642_ = v_isSharedCheck_2647_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_val_2639_);
lean_inc(v_key_2638_);
lean_dec(v_v_2629_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2647_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
lean_inc(v_f_2624_);
v___x_2643_ = lean_apply_1(v_f_2624_, v_val_2639_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 1, v___x_2643_);
v___x_2645_ = v___x_2641_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_key_2638_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
v___y_2633_ = v___x_2645_;
goto v___jp_2632_;
}
}
}
case 1:
{
lean_object* v_node_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2656_; 
v_node_2648_ = lean_ctor_get(v_v_2629_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_v_2629_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2650_ = v_v_2629_;
v_isShared_2651_ = v_isSharedCheck_2656_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_node_2648_);
lean_dec(v_v_2629_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2656_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2652_; lean_object* v___x_2654_; 
lean_inc(v_f_2624_);
v___x_2652_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20___redArg(v_f_2624_, v_node_2648_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 0, v___x_2652_);
v___x_2654_ = v___x_2650_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
v___y_2633_ = v___x_2654_;
goto v___jp_2632_;
}
}
}
default: 
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_box(2);
v___y_2633_ = v___x_2657_;
goto v___jp_2632_;
}
}
v___jp_2632_:
{
size_t v___x_2634_; size_t v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = ((size_t)1ULL);
v___x_2635_ = lean_usize_add(v_i_2626_, v___x_2634_);
v___x_2636_ = lean_array_uset(v_bs_x27_2631_, v_i_2626_, v___y_2633_);
v_i_2626_ = v___x_2635_;
v_bs_2627_ = v___x_2636_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20___redArg(lean_object* v_f_2658_, lean_object* v_n_2659_){
_start:
{
if (lean_obj_tag(v_n_2659_) == 0)
{
lean_object* v_es_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2670_; 
v_es_2660_ = lean_ctor_get(v_n_2659_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v_n_2659_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2662_ = v_n_2659_;
v_isShared_2663_ = v_isSharedCheck_2670_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_es_2660_);
lean_dec(v_n_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2670_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
size_t v_sz_2664_; size_t v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2668_; 
v_sz_2664_ = lean_array_size(v_es_2660_);
v___x_2665_ = ((size_t)0ULL);
v___x_2666_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__33___redArg(v_f_2658_, v_sz_2664_, v___x_2665_, v_es_2660_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v___x_2666_);
v___x_2668_ = v___x_2662_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2666_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
else
{
lean_object* v_ks_2671_; lean_object* v_vs_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2680_; 
v_ks_2671_ = lean_ctor_get(v_n_2659_, 0);
v_vs_2672_ = lean_ctor_get(v_n_2659_, 1);
v_isSharedCheck_2680_ = !lean_is_exclusive(v_n_2659_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2674_ = v_n_2659_;
v_isShared_2675_ = v_isSharedCheck_2680_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_vs_2672_);
lean_inc(v_ks_2671_);
lean_dec(v_n_2659_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2680_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v_val_2676_; lean_object* v___x_2678_; 
v_val_2676_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34___redArg(v_f_2658_, v_vs_2672_);
lean_dec_ref(v_vs_2672_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 1, v_val_2676_);
v___x_2678_ = v___x_2674_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_ks_2671_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_val_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__33___redArg___boxed(lean_object* v_f_2681_, lean_object* v_sz_2682_, lean_object* v_i_2683_, lean_object* v_bs_2684_){
_start:
{
size_t v_sz_boxed_2685_; size_t v_i_boxed_2686_; lean_object* v_res_2687_; 
v_sz_boxed_2685_ = lean_unbox_usize(v_sz_2682_);
lean_dec(v_sz_2682_);
v_i_boxed_2686_ = lean_unbox_usize(v_i_2683_);
lean_dec(v_i_2683_);
v_res_2687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__33___redArg(v_f_2681_, v_sz_boxed_2685_, v_i_boxed_2686_, v_bs_2684_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7___redArg___lam__0(lean_object* v_f_2688_, lean_object* v_x_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = lean_apply_1(v_f_2688_, v_x_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7___redArg(lean_object* v_pm_2691_, lean_object* v_f_2692_){
_start:
{
lean_object* v___f_2693_; lean_object* v___x_2694_; 
v___f_2693_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2693_, 0, v_f_2692_);
v___x_2694_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20___redArg(v___f_2693_, v_pm_2691_);
return v___x_2694_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22___closed__0(void){
_start:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2695_ = lean_unsigned_to_nat(32u);
v___x_2696_ = lean_mk_empty_array_with_capacity(v___x_2695_);
v___x_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
return v___x_2697_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22___closed__1(void){
_start:
{
size_t v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2698_ = ((size_t)5ULL);
v___x_2699_ = lean_unsigned_to_nat(0u);
v___x_2700_ = lean_unsigned_to_nat(32u);
v___x_2701_ = lean_mk_empty_array_with_capacity(v___x_2700_);
v___x_2702_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22___closed__0);
v___x_2703_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
lean_ctor_set(v___x_2703_, 1, v___x_2701_);
lean_ctor_set(v___x_2703_, 2, v___x_2699_);
lean_ctor_set(v___x_2703_, 3, v___x_2699_);
lean_ctor_set_usize(v___x_2703_, 4, v___x_2698_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22(size_t v_sz_2704_, size_t v_i_2705_, lean_object* v_bs_2706_){
_start:
{
uint8_t v___x_2707_; 
v___x_2707_ = lean_usize_dec_lt(v_i_2705_, v_sz_2704_);
if (v___x_2707_ == 0)
{
return v_bs_2706_;
}
else
{
lean_object* v___x_2708_; lean_object* v_bs_x27_2709_; lean_object* v___x_2710_; size_t v___x_2711_; size_t v___x_2712_; lean_object* v___x_2713_; 
v___x_2708_ = lean_unsigned_to_nat(0u);
v_bs_x27_2709_ = lean_array_uset(v_bs_2706_, v_i_2705_, v___x_2708_);
v___x_2710_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22___closed__1);
v___x_2711_ = ((size_t)1ULL);
v___x_2712_ = lean_usize_add(v_i_2705_, v___x_2711_);
v___x_2713_ = lean_array_uset(v_bs_x27_2709_, v_i_2705_, v___x_2710_);
v_i_2705_ = v___x_2712_;
v_bs_2706_ = v___x_2713_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22___boxed(lean_object* v_sz_2715_, lean_object* v_i_2716_, lean_object* v_bs_2717_){
_start:
{
size_t v_sz_boxed_2718_; size_t v_i_boxed_2719_; lean_object* v_res_2720_; 
v_sz_boxed_2718_ = lean_unbox_usize(v_sz_2715_);
lean_dec(v_sz_2715_);
v_i_boxed_2719_ = lean_unbox_usize(v_i_2716_);
lean_dec(v_i_2716_);
v_res_2720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22(v_sz_boxed_2718_, v_i_boxed_2719_, v_bs_2717_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__21_spec__27(size_t v_sz_2721_, size_t v_i_2722_, lean_object* v_bs_2723_){
_start:
{
uint8_t v___x_2724_; 
v___x_2724_ = lean_usize_dec_lt(v_i_2722_, v_sz_2721_);
if (v___x_2724_ == 0)
{
return v_bs_2723_;
}
else
{
lean_object* v_v_2725_; lean_object* v___x_2726_; lean_object* v_bs_x27_2727_; lean_object* v___x_2728_; size_t v___x_2729_; size_t v___x_2730_; lean_object* v___x_2731_; 
v_v_2725_ = lean_array_uget(v_bs_2723_, v_i_2722_);
v___x_2726_ = lean_unsigned_to_nat(0u);
v_bs_x27_2727_ = lean_array_uset(v_bs_2723_, v_i_2722_, v___x_2726_);
v___x_2728_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__21(v_v_2725_);
v___x_2729_ = ((size_t)1ULL);
v___x_2730_ = lean_usize_add(v_i_2722_, v___x_2729_);
v___x_2731_ = lean_array_uset(v_bs_x27_2727_, v_i_2722_, v___x_2728_);
v_i_2722_ = v___x_2730_;
v_bs_2723_ = v___x_2731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__21(lean_object* v_x_2733_){
_start:
{
if (lean_obj_tag(v_x_2733_) == 0)
{
lean_object* v_cs_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2744_; 
v_cs_2734_ = lean_ctor_get(v_x_2733_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_x_2733_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2736_ = v_x_2733_;
v_isShared_2737_ = v_isSharedCheck_2744_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_cs_2734_);
lean_dec(v_x_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2744_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
size_t v_sz_2738_; size_t v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
v_sz_2738_ = lean_array_size(v_cs_2734_);
v___x_2739_ = ((size_t)0ULL);
v___x_2740_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__21_spec__27(v_sz_2738_, v___x_2739_, v_cs_2734_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v___x_2740_);
v___x_2742_ = v___x_2736_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
else
{
lean_object* v_vs_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2755_; 
v_vs_2745_ = lean_ctor_get(v_x_2733_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_x_2733_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2747_ = v_x_2733_;
v_isShared_2748_ = v_isSharedCheck_2755_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_vs_2745_);
lean_dec(v_x_2733_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2755_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
size_t v_sz_2749_; size_t v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; 
v_sz_2749_ = lean_array_size(v_vs_2745_);
v___x_2750_ = ((size_t)0ULL);
v___x_2751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22(v_sz_2749_, v___x_2750_, v_vs_2745_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v___x_2751_);
v___x_2753_ = v___x_2747_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__21_spec__27___boxed(lean_object* v_sz_2756_, lean_object* v_i_2757_, lean_object* v_bs_2758_){
_start:
{
size_t v_sz_boxed_2759_; size_t v_i_boxed_2760_; lean_object* v_res_2761_; 
v_sz_boxed_2759_ = lean_unbox_usize(v_sz_2756_);
lean_dec(v_sz_2756_);
v_i_boxed_2760_ = lean_unbox_usize(v_i_2757_);
lean_dec(v_i_2757_);
v_res_2761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__21_spec__27(v_sz_boxed_2759_, v_i_boxed_2760_, v_bs_2758_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(lean_object* v_t_2762_){
_start:
{
lean_object* v_root_2763_; lean_object* v_tail_2764_; lean_object* v_size_2765_; size_t v_shift_2766_; lean_object* v_tailOff_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2778_; 
v_root_2763_ = lean_ctor_get(v_t_2762_, 0);
v_tail_2764_ = lean_ctor_get(v_t_2762_, 1);
v_size_2765_ = lean_ctor_get(v_t_2762_, 2);
v_shift_2766_ = lean_ctor_get_usize(v_t_2762_, 4);
v_tailOff_2767_ = lean_ctor_get(v_t_2762_, 3);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_t_2762_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2769_ = v_t_2762_;
v_isShared_2770_ = v_isSharedCheck_2778_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_tailOff_2767_);
lean_inc(v_size_2765_);
lean_inc(v_tail_2764_);
lean_inc(v_root_2763_);
lean_dec(v_t_2762_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2778_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; size_t v_sz_2772_; size_t v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2771_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__21(v_root_2763_);
v_sz_2772_ = lean_array_size(v_tail_2764_);
v___x_2773_ = ((size_t)0ULL);
v___x_2774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__22(v_sz_2772_, v___x_2773_, v_tail_2764_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v___x_2774_);
lean_ctor_set(v___x_2769_, 0, v___x_2771_);
v___x_2776_ = v___x_2769_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2777_, 2, v_size_2765_);
lean_ctor_set(v_reuseFailAlloc_2777_, 3, v_tailOff_2767_);
lean_ctor_set_usize(v_reuseFailAlloc_2777_, 4, v_shift_2766_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(lean_object* v___x_2779_, lean_object* v_a_2780_, lean_object* v___f_2781_, lean_object* v___x_2782_, lean_object* v___x_2783_, lean_object* v_a_2784_, uint8_t v___x_2785_, lean_object* v_s_2786_){
_start:
{
lean_object* v_vars_2787_; lean_object* v_varMap_2788_; lean_object* v_varsHistory_2789_; lean_object* v_natToIntMap_2790_; lean_object* v_natDef_2791_; lean_object* v_dvds_2792_; lean_object* v_lowers_2793_; lean_object* v_uppers_2794_; lean_object* v_diseqs_2795_; lean_object* v_elimEqs_2796_; lean_object* v_active_2797_; lean_object* v_elimStack_2798_; lean_object* v_occurs_2799_; lean_object* v_assignment_2800_; lean_object* v_nextCnstrId_2801_; uint8_t v_caseSplits_2802_; lean_object* v_steps_2803_; lean_object* v_penalties_2804_; lean_object* v_numReorderRequests_2805_; lean_object* v_conflict_x3f_2806_; lean_object* v_divMod_2807_; uint8_t v_usedCommRing_2808_; lean_object* v_nonlinearOccs_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2833_; 
v_vars_2787_ = lean_ctor_get(v_s_2786_, 0);
v_varMap_2788_ = lean_ctor_get(v_s_2786_, 1);
v_varsHistory_2789_ = lean_ctor_get(v_s_2786_, 2);
v_natToIntMap_2790_ = lean_ctor_get(v_s_2786_, 3);
v_natDef_2791_ = lean_ctor_get(v_s_2786_, 4);
v_dvds_2792_ = lean_ctor_get(v_s_2786_, 5);
v_lowers_2793_ = lean_ctor_get(v_s_2786_, 6);
v_uppers_2794_ = lean_ctor_get(v_s_2786_, 7);
v_diseqs_2795_ = lean_ctor_get(v_s_2786_, 8);
v_elimEqs_2796_ = lean_ctor_get(v_s_2786_, 9);
v_active_2797_ = lean_ctor_get(v_s_2786_, 10);
v_elimStack_2798_ = lean_ctor_get(v_s_2786_, 11);
v_occurs_2799_ = lean_ctor_get(v_s_2786_, 12);
v_assignment_2800_ = lean_ctor_get(v_s_2786_, 13);
v_nextCnstrId_2801_ = lean_ctor_get(v_s_2786_, 14);
v_caseSplits_2802_ = lean_ctor_get_uint8(v_s_2786_, sizeof(void*)*22);
v_steps_2803_ = lean_ctor_get(v_s_2786_, 15);
v_penalties_2804_ = lean_ctor_get(v_s_2786_, 16);
v_numReorderRequests_2805_ = lean_ctor_get(v_s_2786_, 17);
v_conflict_x3f_2806_ = lean_ctor_get(v_s_2786_, 18);
v_divMod_2807_ = lean_ctor_get(v_s_2786_, 20);
v_usedCommRing_2808_ = lean_ctor_get_uint8(v_s_2786_, sizeof(void*)*22 + 1);
v_nonlinearOccs_2809_ = lean_ctor_get(v_s_2786_, 21);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_s_2786_);
if (v_isSharedCheck_2833_ == 0)
{
lean_object* v_unused_2834_; 
v_unused_2834_ = lean_ctor_get(v_s_2786_, 19);
lean_dec(v_unused_2834_);
v___x_2811_ = v_s_2786_;
v_isShared_2812_ = v_isSharedCheck_2833_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_nonlinearOccs_2809_);
lean_inc(v_divMod_2807_);
lean_inc(v_conflict_x3f_2806_);
lean_inc(v_numReorderRequests_2805_);
lean_inc(v_penalties_2804_);
lean_inc(v_steps_2803_);
lean_inc(v_nextCnstrId_2801_);
lean_inc(v_assignment_2800_);
lean_inc(v_occurs_2799_);
lean_inc(v_elimStack_2798_);
lean_inc(v_active_2797_);
lean_inc(v_elimEqs_2796_);
lean_inc(v_diseqs_2795_);
lean_inc(v_uppers_2794_);
lean_inc(v_lowers_2793_);
lean_inc(v_dvds_2792_);
lean_inc(v_natDef_2791_);
lean_inc(v_natToIntMap_2790_);
lean_inc(v_varsHistory_2789_);
lean_inc(v_varMap_2788_);
lean_inc(v_vars_2787_);
lean_dec(v_s_2786_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2833_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2831_; 
lean_inc_ref_n(v_a_2780_, 2);
lean_inc_ref(v_vars_2787_);
v___x_2813_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2779_, v_vars_2787_, v_a_2780_);
lean_inc_ref(v___f_2781_);
lean_inc_ref(v_varMap_2788_);
v___x_2814_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7___redArg(v_varMap_2788_, v___f_2781_);
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v_vars_2787_);
lean_ctor_set(v___x_2815_, 1, v_varMap_2788_);
v___x_2816_ = l_Lean_PersistentArray_push___redArg(v_varsHistory_2789_, v___x_2815_);
v___x_2817_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7___redArg(v_natDef_2791_, v___f_2781_);
v___x_2818_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_dvds_2792_);
v___x_2819_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v_lowers_2793_);
v___x_2820_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v_uppers_2794_);
v___x_2821_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v_diseqs_2795_);
v___x_2822_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2782_, v_elimEqs_2796_, v_a_2780_);
v___x_2823_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v___x_2783_, v_a_2784_, v___x_2822_);
v___x_2824_ = lean_box(v___x_2785_);
v___x_2825_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2824_, v_active_2797_, v_a_2780_);
v___x_2826_ = lean_box(0);
v___x_2827_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v___x_2783_, v_elimStack_2798_, v___x_2826_);
v___x_2828_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v_occurs_2799_);
v___x_2829_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1);
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 19, v___x_2829_);
lean_ctor_set(v___x_2811_, 12, v___x_2828_);
lean_ctor_set(v___x_2811_, 11, v___x_2827_);
lean_ctor_set(v___x_2811_, 10, v___x_2825_);
lean_ctor_set(v___x_2811_, 9, v___x_2823_);
lean_ctor_set(v___x_2811_, 8, v___x_2821_);
lean_ctor_set(v___x_2811_, 7, v___x_2820_);
lean_ctor_set(v___x_2811_, 6, v___x_2819_);
lean_ctor_set(v___x_2811_, 5, v___x_2818_);
lean_ctor_set(v___x_2811_, 4, v___x_2817_);
lean_ctor_set(v___x_2811_, 2, v___x_2816_);
lean_ctor_set(v___x_2811_, 1, v___x_2814_);
lean_ctor_set(v___x_2811_, 0, v___x_2813_);
v___x_2831_ = v___x_2811_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2813_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v___x_2814_);
lean_ctor_set(v_reuseFailAlloc_2832_, 2, v___x_2816_);
lean_ctor_set(v_reuseFailAlloc_2832_, 3, v_natToIntMap_2790_);
lean_ctor_set(v_reuseFailAlloc_2832_, 4, v___x_2817_);
lean_ctor_set(v_reuseFailAlloc_2832_, 5, v___x_2818_);
lean_ctor_set(v_reuseFailAlloc_2832_, 6, v___x_2819_);
lean_ctor_set(v_reuseFailAlloc_2832_, 7, v___x_2820_);
lean_ctor_set(v_reuseFailAlloc_2832_, 8, v___x_2821_);
lean_ctor_set(v_reuseFailAlloc_2832_, 9, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2832_, 10, v___x_2825_);
lean_ctor_set(v_reuseFailAlloc_2832_, 11, v___x_2827_);
lean_ctor_set(v_reuseFailAlloc_2832_, 12, v___x_2828_);
lean_ctor_set(v_reuseFailAlloc_2832_, 13, v_assignment_2800_);
lean_ctor_set(v_reuseFailAlloc_2832_, 14, v_nextCnstrId_2801_);
lean_ctor_set(v_reuseFailAlloc_2832_, 15, v_steps_2803_);
lean_ctor_set(v_reuseFailAlloc_2832_, 16, v_penalties_2804_);
lean_ctor_set(v_reuseFailAlloc_2832_, 17, v_numReorderRequests_2805_);
lean_ctor_set(v_reuseFailAlloc_2832_, 18, v_conflict_x3f_2806_);
lean_ctor_set(v_reuseFailAlloc_2832_, 19, v___x_2829_);
lean_ctor_set(v_reuseFailAlloc_2832_, 20, v_divMod_2807_);
lean_ctor_set(v_reuseFailAlloc_2832_, 21, v_nonlinearOccs_2809_);
lean_ctor_set_uint8(v_reuseFailAlloc_2832_, sizeof(void*)*22, v_caseSplits_2802_);
lean_ctor_set_uint8(v_reuseFailAlloc_2832_, sizeof(void*)*22 + 1, v_usedCommRing_2808_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed(lean_object* v___x_2835_, lean_object* v_a_2836_, lean_object* v___f_2837_, lean_object* v___x_2838_, lean_object* v___x_2839_, lean_object* v_a_2840_, lean_object* v___x_2841_, lean_object* v_s_2842_){
_start:
{
uint8_t v___x_105965__boxed_2843_; lean_object* v_res_2844_; 
v___x_105965__boxed_2843_ = lean_unbox(v___x_2841_);
v_res_2844_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(v___x_2835_, v_a_2836_, v___f_2837_, v___x_2838_, v___x_2839_, v_a_2840_, v___x_105965__boxed_2843_, v_s_2842_);
lean_dec_ref(v___x_2839_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(lean_object* v___x_2845_, size_t v_sz_2846_, size_t v_i_2847_, lean_object* v_bs_2848_){
_start:
{
uint8_t v___x_2849_; 
v___x_2849_ = lean_usize_dec_lt(v_i_2847_, v_sz_2846_);
if (v___x_2849_ == 0)
{
return v_bs_2848_;
}
else
{
lean_object* v_v_2850_; lean_object* v___x_2851_; lean_object* v_bs_x27_2852_; lean_object* v___x_2853_; size_t v___x_2854_; size_t v___x_2855_; lean_object* v___x_2856_; 
v_v_2850_ = lean_array_uget(v_bs_2848_, v_i_2847_);
v___x_2851_ = lean_unsigned_to_nat(0u);
v_bs_x27_2852_ = lean_array_uset(v_bs_2848_, v_i_2847_, v___x_2851_);
v___x_2853_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_v_2850_, v___x_2845_);
v___x_2854_ = ((size_t)1ULL);
v___x_2855_ = lean_usize_add(v_i_2847_, v___x_2854_);
v___x_2856_ = lean_array_uset(v_bs_x27_2852_, v_i_2847_, v___x_2853_);
v_i_2847_ = v___x_2855_;
v_bs_2848_ = v___x_2856_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4___boxed(lean_object* v___x_2858_, lean_object* v_sz_2859_, lean_object* v_i_2860_, lean_object* v_bs_2861_){
_start:
{
size_t v_sz_boxed_2862_; size_t v_i_boxed_2863_; lean_object* v_res_2864_; 
v_sz_boxed_2862_ = lean_unbox_usize(v_sz_2859_);
lean_dec(v_sz_2859_);
v_i_boxed_2863_ = lean_unbox_usize(v_i_2860_);
lean_dec(v_i_2860_);
v_res_2864_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(v___x_2858_, v_sz_boxed_2862_, v_i_boxed_2863_, v_bs_2861_);
lean_dec_ref(v___x_2858_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(lean_object* v___x_2865_, size_t v_sz_2866_, size_t v_i_2867_, lean_object* v_bs_2868_){
_start:
{
uint8_t v___x_2869_; 
v___x_2869_ = lean_usize_dec_lt(v_i_2867_, v_sz_2866_);
if (v___x_2869_ == 0)
{
return v_bs_2868_;
}
else
{
lean_object* v_v_2870_; lean_object* v___x_2871_; lean_object* v_bs_x27_2872_; lean_object* v___x_2873_; size_t v___x_2874_; size_t v___x_2875_; lean_object* v___x_2876_; 
v_v_2870_ = lean_array_uget(v_bs_2868_, v_i_2867_);
v___x_2871_ = lean_unsigned_to_nat(0u);
v_bs_x27_2872_ = lean_array_uset(v_bs_2868_, v_i_2867_, v___x_2871_);
v___x_2873_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(v_v_2870_, v___x_2865_);
v___x_2874_ = ((size_t)1ULL);
v___x_2875_ = lean_usize_add(v_i_2867_, v___x_2874_);
v___x_2876_ = lean_array_uset(v_bs_x27_2872_, v_i_2867_, v___x_2873_);
v_i_2867_ = v___x_2875_;
v_bs_2868_ = v___x_2876_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2___boxed(lean_object* v___x_2878_, lean_object* v_sz_2879_, lean_object* v_i_2880_, lean_object* v_bs_2881_){
_start:
{
size_t v_sz_boxed_2882_; size_t v_i_boxed_2883_; lean_object* v_res_2884_; 
v_sz_boxed_2882_ = lean_unbox_usize(v_sz_2879_);
lean_dec(v_sz_2879_);
v_i_boxed_2883_ = lean_unbox_usize(v_i_2880_);
lean_dec(v_i_2880_);
v_res_2884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(v___x_2878_, v_sz_boxed_2882_, v_i_boxed_2883_, v_bs_2881_);
lean_dec_ref(v___x_2878_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(lean_object* v___x_2885_, size_t v_sz_2886_, size_t v_i_2887_, lean_object* v_bs_2888_){
_start:
{
uint8_t v___x_2889_; 
v___x_2889_ = lean_usize_dec_lt(v_i_2887_, v_sz_2886_);
if (v___x_2889_ == 0)
{
return v_bs_2888_;
}
else
{
lean_object* v_v_2890_; lean_object* v___x_2891_; lean_object* v_bs_x27_2892_; lean_object* v___x_2893_; size_t v___x_2894_; size_t v___x_2895_; lean_object* v___x_2896_; 
v_v_2890_ = lean_array_uget(v_bs_2888_, v_i_2887_);
v___x_2891_ = lean_unsigned_to_nat(0u);
v_bs_x27_2892_ = lean_array_uset(v_bs_2888_, v_i_2887_, v___x_2891_);
v___x_2893_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(v_v_2890_, v___x_2885_);
v___x_2894_ = ((size_t)1ULL);
v___x_2895_ = lean_usize_add(v_i_2887_, v___x_2894_);
v___x_2896_ = lean_array_uset(v_bs_x27_2892_, v_i_2887_, v___x_2893_);
v_i_2887_ = v___x_2895_;
v_bs_2888_ = v___x_2896_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6___boxed(lean_object* v___x_2898_, lean_object* v_sz_2899_, lean_object* v_i_2900_, lean_object* v_bs_2901_){
_start:
{
size_t v_sz_boxed_2902_; size_t v_i_boxed_2903_; lean_object* v_res_2904_; 
v_sz_boxed_2902_ = lean_unbox_usize(v_sz_2899_);
lean_dec(v_sz_2899_);
v_i_boxed_2903_ = lean_unbox_usize(v_i_2900_);
lean_dec(v_i_2900_);
v_res_2904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(v___x_2898_, v_sz_boxed_2902_, v_i_boxed_2903_, v_bs_2901_);
lean_dec_ref(v___x_2898_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(lean_object* v_as_2905_, size_t v_i_2906_, size_t v_stop_2907_, lean_object* v_b_2908_){
_start:
{
lean_object* v___y_2910_; uint8_t v___x_2914_; 
v___x_2914_ = lean_usize_dec_eq(v_i_2906_, v_stop_2907_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; 
v___x_2915_ = lean_array_uget_borrowed(v_as_2905_, v_i_2906_);
if (lean_obj_tag(v___x_2915_) == 0)
{
v___y_2910_ = v_b_2908_;
goto v___jp_2909_;
}
else
{
lean_object* v_val_2916_; lean_object* v___x_2917_; 
v_val_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_val_2916_);
v___x_2917_ = lean_array_push(v_b_2908_, v_val_2916_);
v___y_2910_ = v___x_2917_;
goto v___jp_2909_;
}
}
else
{
return v_b_2908_;
}
v___jp_2909_:
{
size_t v___x_2911_; size_t v___x_2912_; 
v___x_2911_ = ((size_t)1ULL);
v___x_2912_ = lean_usize_add(v_i_2906_, v___x_2911_);
v_i_2906_ = v___x_2912_;
v_b_2908_ = v___y_2910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2___boxed(lean_object* v_as_2918_, lean_object* v_i_2919_, lean_object* v_stop_2920_, lean_object* v_b_2921_){
_start:
{
size_t v_i_boxed_2922_; size_t v_stop_boxed_2923_; lean_object* v_res_2924_; 
v_i_boxed_2922_ = lean_unbox_usize(v_i_2919_);
lean_dec(v_i_2919_);
v_stop_boxed_2923_ = lean_unbox_usize(v_stop_2920_);
lean_dec(v_stop_2920_);
v_res_2924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(v_as_2918_, v_i_boxed_2922_, v_stop_boxed_2923_, v_b_2921_);
lean_dec_ref(v_as_2918_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(lean_object* v_x_2925_, lean_object* v_x_2926_){
_start:
{
if (lean_obj_tag(v_x_2925_) == 0)
{
lean_object* v_cs_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; uint8_t v___x_2930_; 
v_cs_2927_ = lean_ctor_get(v_x_2925_, 0);
v___x_2928_ = lean_unsigned_to_nat(0u);
v___x_2929_ = lean_array_get_size(v_cs_2927_);
v___x_2930_ = lean_nat_dec_lt(v___x_2928_, v___x_2929_);
if (v___x_2930_ == 0)
{
return v_x_2926_;
}
else
{
size_t v___x_2931_; size_t v___x_2932_; lean_object* v___x_2933_; 
v___x_2931_ = ((size_t)0ULL);
v___x_2932_ = lean_usize_of_nat(v___x_2929_);
v___x_2933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2(v_cs_2927_, v___x_2931_, v___x_2932_, v_x_2926_);
return v___x_2933_;
}
}
else
{
lean_object* v_vs_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; 
v_vs_2934_ = lean_ctor_get(v_x_2925_, 0);
v___x_2935_ = lean_unsigned_to_nat(0u);
v___x_2936_ = lean_array_get_size(v_vs_2934_);
v___x_2937_ = lean_nat_dec_lt(v___x_2935_, v___x_2936_);
if (v___x_2937_ == 0)
{
return v_x_2926_;
}
else
{
size_t v___x_2938_; size_t v___x_2939_; lean_object* v___x_2940_; 
v___x_2938_ = ((size_t)0ULL);
v___x_2939_ = lean_usize_of_nat(v___x_2936_);
v___x_2940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(v_vs_2934_, v___x_2938_, v___x_2939_, v_x_2926_);
return v___x_2940_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2(lean_object* v_as_2941_, size_t v_i_2942_, size_t v_stop_2943_, lean_object* v_b_2944_){
_start:
{
uint8_t v___x_2945_; 
v___x_2945_ = lean_usize_dec_eq(v_i_2942_, v_stop_2943_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; lean_object* v___x_2947_; size_t v___x_2948_; size_t v___x_2949_; 
v___x_2946_ = lean_array_uget_borrowed(v_as_2941_, v_i_2942_);
v___x_2947_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v___x_2946_, v_b_2944_);
v___x_2948_ = ((size_t)1ULL);
v___x_2949_ = lean_usize_add(v_i_2942_, v___x_2948_);
v_i_2942_ = v___x_2949_;
v_b_2944_ = v___x_2947_;
goto _start;
}
else
{
return v_b_2944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___boxed(lean_object* v_as_2951_, lean_object* v_i_2952_, lean_object* v_stop_2953_, lean_object* v_b_2954_){
_start:
{
size_t v_i_boxed_2955_; size_t v_stop_boxed_2956_; lean_object* v_res_2957_; 
v_i_boxed_2955_ = lean_unbox_usize(v_i_2952_);
lean_dec(v_i_2952_);
v_stop_boxed_2956_ = lean_unbox_usize(v_stop_2953_);
lean_dec(v_stop_2953_);
v_res_2957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2(v_as_2951_, v_i_boxed_2955_, v_stop_boxed_2956_, v_b_2954_);
lean_dec_ref(v_as_2951_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3___boxed(lean_object* v_x_2958_, lean_object* v_x_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_x_2958_, v_x_2959_);
lean_dec_ref(v_x_2958_);
return v_res_2960_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1(lean_object* v_x_2962_, size_t v_x_2963_, size_t v_x_2964_, lean_object* v_x_2965_){
_start:
{
if (lean_obj_tag(v_x_2962_) == 0)
{
lean_object* v_cs_2966_; lean_object* v___x_2967_; size_t v___x_2968_; lean_object* v_j_2969_; lean_object* v___x_2970_; size_t v___x_2971_; size_t v___x_2972_; size_t v___x_2973_; size_t v___x_2974_; size_t v___x_2975_; size_t v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v_cs_2966_ = lean_ctor_get(v_x_2962_, 0);
v___x_2967_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___closed__0);
v___x_2968_ = lean_usize_shift_right(v_x_2963_, v_x_2964_);
v_j_2969_ = lean_usize_to_nat(v___x_2968_);
v___x_2970_ = lean_array_get_borrowed(v___x_2967_, v_cs_2966_, v_j_2969_);
v___x_2971_ = ((size_t)1ULL);
v___x_2972_ = lean_usize_shift_left(v___x_2971_, v_x_2964_);
v___x_2973_ = lean_usize_sub(v___x_2972_, v___x_2971_);
v___x_2974_ = lean_usize_land(v_x_2963_, v___x_2973_);
v___x_2975_ = ((size_t)5ULL);
v___x_2976_ = lean_usize_sub(v_x_2964_, v___x_2975_);
v___x_2977_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1(v___x_2970_, v___x_2974_, v___x_2976_, v_x_2965_);
v___x_2978_ = lean_unsigned_to_nat(1u);
v___x_2979_ = lean_nat_add(v_j_2969_, v___x_2978_);
lean_dec(v_j_2969_);
v___x_2980_ = lean_array_get_size(v_cs_2966_);
v___x_2981_ = lean_nat_dec_lt(v___x_2979_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_dec(v___x_2979_);
return v___x_2977_;
}
else
{
size_t v___x_2982_; size_t v___x_2983_; lean_object* v___x_2984_; 
v___x_2982_ = lean_usize_of_nat(v___x_2979_);
lean_dec(v___x_2979_);
v___x_2983_ = lean_usize_of_nat(v___x_2980_);
v___x_2984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2(v_cs_2966_, v___x_2982_, v___x_2983_, v___x_2977_);
return v___x_2984_;
}
}
else
{
lean_object* v_vs_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; 
v_vs_2985_ = lean_ctor_get(v_x_2962_, 0);
v___x_2986_ = lean_usize_to_nat(v_x_2963_);
v___x_2987_ = lean_array_get_size(v_vs_2985_);
v___x_2988_ = lean_nat_dec_lt(v___x_2986_, v___x_2987_);
if (v___x_2988_ == 0)
{
lean_dec(v___x_2986_);
return v_x_2965_;
}
else
{
size_t v___x_2989_; size_t v___x_2990_; lean_object* v___x_2991_; 
v___x_2989_ = lean_usize_of_nat(v___x_2986_);
lean_dec(v___x_2986_);
v___x_2990_ = lean_usize_of_nat(v___x_2987_);
v___x_2991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(v_vs_2985_, v___x_2989_, v___x_2990_, v_x_2965_);
return v___x_2991_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___boxed(lean_object* v_x_2992_, lean_object* v_x_2993_, lean_object* v_x_2994_, lean_object* v_x_2995_){
_start:
{
size_t v_x_106149__boxed_2996_; size_t v_x_106150__boxed_2997_; lean_object* v_res_2998_; 
v_x_106149__boxed_2996_ = lean_unbox_usize(v_x_2993_);
lean_dec(v_x_2993_);
v_x_106150__boxed_2997_ = lean_unbox_usize(v_x_2994_);
lean_dec(v_x_2994_);
v_res_2998_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1(v_x_2992_, v_x_106149__boxed_2996_, v_x_106150__boxed_2997_, v_x_2995_);
lean_dec_ref(v_x_2992_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(lean_object* v_t_2999_, lean_object* v_init_3000_, lean_object* v_start_3001_){
_start:
{
lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_3002_ = lean_unsigned_to_nat(0u);
v___x_3003_ = lean_nat_dec_eq(v_start_3001_, v___x_3002_);
if (v___x_3003_ == 0)
{
lean_object* v_root_3004_; lean_object* v_tail_3005_; size_t v_shift_3006_; lean_object* v_tailOff_3007_; uint8_t v___x_3008_; 
v_root_3004_ = lean_ctor_get(v_t_2999_, 0);
v_tail_3005_ = lean_ctor_get(v_t_2999_, 1);
v_shift_3006_ = lean_ctor_get_usize(v_t_2999_, 4);
v_tailOff_3007_ = lean_ctor_get(v_t_2999_, 3);
v___x_3008_ = lean_nat_dec_le(v_tailOff_3007_, v_start_3001_);
if (v___x_3008_ == 0)
{
size_t v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3009_ = lean_usize_of_nat(v_start_3001_);
v___x_3010_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1(v_root_3004_, v___x_3009_, v_shift_3006_, v_init_3000_);
v___x_3011_ = lean_array_get_size(v_tail_3005_);
v___x_3012_ = lean_nat_dec_lt(v___x_3002_, v___x_3011_);
if (v___x_3012_ == 0)
{
return v___x_3010_;
}
else
{
size_t v___x_3013_; size_t v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = ((size_t)0ULL);
v___x_3014_ = lean_usize_of_nat(v___x_3011_);
v___x_3015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(v_tail_3005_, v___x_3013_, v___x_3014_, v___x_3010_);
return v___x_3015_;
}
}
else
{
lean_object* v___x_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; 
v___x_3016_ = lean_nat_sub(v_start_3001_, v_tailOff_3007_);
v___x_3017_ = lean_array_get_size(v_tail_3005_);
v___x_3018_ = lean_nat_dec_lt(v___x_3016_, v___x_3017_);
if (v___x_3018_ == 0)
{
lean_dec(v___x_3016_);
return v_init_3000_;
}
else
{
size_t v___x_3019_; size_t v___x_3020_; lean_object* v___x_3021_; 
v___x_3019_ = lean_usize_of_nat(v___x_3016_);
lean_dec(v___x_3016_);
v___x_3020_ = lean_usize_of_nat(v___x_3017_);
v___x_3021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(v_tail_3005_, v___x_3019_, v___x_3020_, v_init_3000_);
return v___x_3021_;
}
}
}
else
{
lean_object* v_root_3022_; lean_object* v_tail_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; uint8_t v___x_3026_; 
v_root_3022_ = lean_ctor_get(v_t_2999_, 0);
v_tail_3023_ = lean_ctor_get(v_t_2999_, 1);
v___x_3024_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_root_3022_, v_init_3000_);
v___x_3025_ = lean_array_get_size(v_tail_3023_);
v___x_3026_ = lean_nat_dec_lt(v___x_3002_, v___x_3025_);
if (v___x_3026_ == 0)
{
return v___x_3024_;
}
else
{
size_t v___x_3027_; size_t v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = ((size_t)0ULL);
v___x_3028_ = lean_usize_of_nat(v___x_3025_);
v___x_3029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(v_tail_3023_, v___x_3027_, v___x_3028_, v___x_3024_);
return v___x_3029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___boxed(lean_object* v_t_3030_, lean_object* v_init_3031_, lean_object* v_start_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(v_t_3030_, v_init_3031_, v_start_3032_);
lean_dec(v_start_3032_);
lean_dec_ref(v_t_3030_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(lean_object* v_as_3034_, size_t v_i_3035_, size_t v_stop_3036_, lean_object* v_b_3037_){
_start:
{
uint8_t v___x_3038_; 
v___x_3038_ = lean_usize_dec_eq(v_i_3035_, v_stop_3036_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; size_t v___x_3042_; size_t v___x_3043_; 
v___x_3039_ = lean_array_uget_borrowed(v_as_3034_, v_i_3035_);
v___x_3040_ = l_Lean_PersistentArray_toArray___redArg(v___x_3039_);
v___x_3041_ = l_Array_append___redArg(v_b_3037_, v___x_3040_);
lean_dec_ref(v___x_3040_);
v___x_3042_ = ((size_t)1ULL);
v___x_3043_ = lean_usize_add(v_i_3035_, v___x_3042_);
v_i_3035_ = v___x_3043_;
v_b_3037_ = v___x_3041_;
goto _start;
}
else
{
return v_b_3037_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12___boxed(lean_object* v_as_3045_, lean_object* v_i_3046_, lean_object* v_stop_3047_, lean_object* v_b_3048_){
_start:
{
size_t v_i_boxed_3049_; size_t v_stop_boxed_3050_; lean_object* v_res_3051_; 
v_i_boxed_3049_ = lean_unbox_usize(v_i_3046_);
lean_dec(v_i_3046_);
v_stop_boxed_3050_ = lean_unbox_usize(v_stop_3047_);
lean_dec(v_stop_3047_);
v_res_3051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(v_as_3045_, v_i_boxed_3049_, v_stop_boxed_3050_, v_b_3048_);
lean_dec_ref(v_as_3045_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(lean_object* v_x_3052_, lean_object* v_x_3053_){
_start:
{
if (lean_obj_tag(v_x_3052_) == 0)
{
lean_object* v_cs_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; uint8_t v___x_3057_; 
v_cs_3054_ = lean_ctor_get(v_x_3052_, 0);
v___x_3055_ = lean_unsigned_to_nat(0u);
v___x_3056_ = lean_array_get_size(v_cs_3054_);
v___x_3057_ = lean_nat_dec_lt(v___x_3055_, v___x_3056_);
if (v___x_3057_ == 0)
{
return v_x_3053_;
}
else
{
size_t v___x_3058_; size_t v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = ((size_t)0ULL);
v___x_3059_ = lean_usize_of_nat(v___x_3056_);
v___x_3060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__11_spec__14(v_cs_3054_, v___x_3058_, v___x_3059_, v_x_3053_);
return v___x_3060_;
}
}
else
{
lean_object* v_vs_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; 
v_vs_3061_ = lean_ctor_get(v_x_3052_, 0);
v___x_3062_ = lean_unsigned_to_nat(0u);
v___x_3063_ = lean_array_get_size(v_vs_3061_);
v___x_3064_ = lean_nat_dec_lt(v___x_3062_, v___x_3063_);
if (v___x_3064_ == 0)
{
return v_x_3053_;
}
else
{
size_t v___x_3065_; size_t v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = ((size_t)0ULL);
v___x_3066_ = lean_usize_of_nat(v___x_3063_);
v___x_3067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(v_vs_3061_, v___x_3065_, v___x_3066_, v_x_3053_);
return v___x_3067_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__11_spec__14(lean_object* v_as_3068_, size_t v_i_3069_, size_t v_stop_3070_, lean_object* v_b_3071_){
_start:
{
uint8_t v___x_3072_; 
v___x_3072_ = lean_usize_dec_eq(v_i_3069_, v_stop_3070_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; lean_object* v___x_3074_; size_t v___x_3075_; size_t v___x_3076_; 
v___x_3073_ = lean_array_uget_borrowed(v_as_3068_, v_i_3069_);
v___x_3074_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(v___x_3073_, v_b_3071_);
v___x_3075_ = ((size_t)1ULL);
v___x_3076_ = lean_usize_add(v_i_3069_, v___x_3075_);
v_i_3069_ = v___x_3076_;
v_b_3071_ = v___x_3074_;
goto _start;
}
else
{
return v_b_3071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__11_spec__14___boxed(lean_object* v_as_3078_, lean_object* v_i_3079_, lean_object* v_stop_3080_, lean_object* v_b_3081_){
_start:
{
size_t v_i_boxed_3082_; size_t v_stop_boxed_3083_; lean_object* v_res_3084_; 
v_i_boxed_3082_ = lean_unbox_usize(v_i_3079_);
lean_dec(v_i_3079_);
v_stop_boxed_3083_ = lean_unbox_usize(v_stop_3080_);
lean_dec(v_stop_3080_);
v_res_3084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__11_spec__14(v_as_3078_, v_i_boxed_3082_, v_stop_boxed_3083_, v_b_3081_);
lean_dec_ref(v_as_3078_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13___boxed(lean_object* v_x_3085_, lean_object* v_x_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(v_x_3085_, v_x_3086_);
lean_dec_ref(v_x_3085_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__11(lean_object* v_x_3088_, size_t v_x_3089_, size_t v_x_3090_, lean_object* v_x_3091_){
_start:
{
if (lean_obj_tag(v_x_3088_) == 0)
{
lean_object* v_cs_3092_; lean_object* v___x_3093_; size_t v___x_3094_; lean_object* v_j_3095_; lean_object* v___x_3096_; size_t v___x_3097_; size_t v___x_3098_; size_t v___x_3099_; size_t v___x_3100_; size_t v___x_3101_; size_t v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; uint8_t v___x_3107_; 
v_cs_3092_ = lean_ctor_get(v_x_3088_, 0);
v___x_3093_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___closed__0);
v___x_3094_ = lean_usize_shift_right(v_x_3089_, v_x_3090_);
v_j_3095_ = lean_usize_to_nat(v___x_3094_);
v___x_3096_ = lean_array_get_borrowed(v___x_3093_, v_cs_3092_, v_j_3095_);
v___x_3097_ = ((size_t)1ULL);
v___x_3098_ = lean_usize_shift_left(v___x_3097_, v_x_3090_);
v___x_3099_ = lean_usize_sub(v___x_3098_, v___x_3097_);
v___x_3100_ = lean_usize_land(v_x_3089_, v___x_3099_);
v___x_3101_ = ((size_t)5ULL);
v___x_3102_ = lean_usize_sub(v_x_3090_, v___x_3101_);
v___x_3103_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__11(v___x_3096_, v___x_3100_, v___x_3102_, v_x_3091_);
v___x_3104_ = lean_unsigned_to_nat(1u);
v___x_3105_ = lean_nat_add(v_j_3095_, v___x_3104_);
lean_dec(v_j_3095_);
v___x_3106_ = lean_array_get_size(v_cs_3092_);
v___x_3107_ = lean_nat_dec_lt(v___x_3105_, v___x_3106_);
if (v___x_3107_ == 0)
{
lean_dec(v___x_3105_);
return v___x_3103_;
}
else
{
size_t v___x_3108_; size_t v___x_3109_; lean_object* v___x_3110_; 
v___x_3108_ = lean_usize_of_nat(v___x_3105_);
lean_dec(v___x_3105_);
v___x_3109_ = lean_usize_of_nat(v___x_3106_);
v___x_3110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__11_spec__14(v_cs_3092_, v___x_3108_, v___x_3109_, v___x_3103_);
return v___x_3110_;
}
}
else
{
lean_object* v_vs_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; uint8_t v___x_3114_; 
v_vs_3111_ = lean_ctor_get(v_x_3088_, 0);
v___x_3112_ = lean_usize_to_nat(v_x_3089_);
v___x_3113_ = lean_array_get_size(v_vs_3111_);
v___x_3114_ = lean_nat_dec_lt(v___x_3112_, v___x_3113_);
if (v___x_3114_ == 0)
{
lean_dec(v___x_3112_);
return v_x_3091_;
}
else
{
size_t v___x_3115_; size_t v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = lean_usize_of_nat(v___x_3112_);
lean_dec(v___x_3112_);
v___x_3116_ = lean_usize_of_nat(v___x_3113_);
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(v_vs_3111_, v___x_3115_, v___x_3116_, v_x_3091_);
return v___x_3117_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__11___boxed(lean_object* v_x_3118_, lean_object* v_x_3119_, lean_object* v_x_3120_, lean_object* v_x_3121_){
_start:
{
size_t v_x_106317__boxed_3122_; size_t v_x_106318__boxed_3123_; lean_object* v_res_3124_; 
v_x_106317__boxed_3122_ = lean_unbox_usize(v_x_3119_);
lean_dec(v_x_3119_);
v_x_106318__boxed_3123_ = lean_unbox_usize(v_x_3120_);
lean_dec(v_x_3120_);
v_res_3124_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__11(v_x_3118_, v_x_106317__boxed_3122_, v_x_106318__boxed_3123_, v_x_3121_);
lean_dec_ref(v_x_3118_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(lean_object* v_t_3125_, lean_object* v_init_3126_, lean_object* v_start_3127_){
_start:
{
lean_object* v___x_3128_; uint8_t v___x_3129_; 
v___x_3128_ = lean_unsigned_to_nat(0u);
v___x_3129_ = lean_nat_dec_eq(v_start_3127_, v___x_3128_);
if (v___x_3129_ == 0)
{
lean_object* v_root_3130_; lean_object* v_tail_3131_; size_t v_shift_3132_; lean_object* v_tailOff_3133_; uint8_t v___x_3134_; 
v_root_3130_ = lean_ctor_get(v_t_3125_, 0);
v_tail_3131_ = lean_ctor_get(v_t_3125_, 1);
v_shift_3132_ = lean_ctor_get_usize(v_t_3125_, 4);
v_tailOff_3133_ = lean_ctor_get(v_t_3125_, 3);
v___x_3134_ = lean_nat_dec_le(v_tailOff_3133_, v_start_3127_);
if (v___x_3134_ == 0)
{
size_t v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; uint8_t v___x_3138_; 
v___x_3135_ = lean_usize_of_nat(v_start_3127_);
v___x_3136_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__11(v_root_3130_, v___x_3135_, v_shift_3132_, v_init_3126_);
v___x_3137_ = lean_array_get_size(v_tail_3131_);
v___x_3138_ = lean_nat_dec_lt(v___x_3128_, v___x_3137_);
if (v___x_3138_ == 0)
{
return v___x_3136_;
}
else
{
size_t v___x_3139_; size_t v___x_3140_; lean_object* v___x_3141_; 
v___x_3139_ = ((size_t)0ULL);
v___x_3140_ = lean_usize_of_nat(v___x_3137_);
v___x_3141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(v_tail_3131_, v___x_3139_, v___x_3140_, v___x_3136_);
return v___x_3141_;
}
}
else
{
lean_object* v___x_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; 
v___x_3142_ = lean_nat_sub(v_start_3127_, v_tailOff_3133_);
v___x_3143_ = lean_array_get_size(v_tail_3131_);
v___x_3144_ = lean_nat_dec_lt(v___x_3142_, v___x_3143_);
if (v___x_3144_ == 0)
{
lean_dec(v___x_3142_);
return v_init_3126_;
}
else
{
size_t v___x_3145_; size_t v___x_3146_; lean_object* v___x_3147_; 
v___x_3145_ = lean_usize_of_nat(v___x_3142_);
lean_dec(v___x_3142_);
v___x_3146_ = lean_usize_of_nat(v___x_3143_);
v___x_3147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(v_tail_3131_, v___x_3145_, v___x_3146_, v_init_3126_);
return v___x_3147_;
}
}
}
else
{
lean_object* v_root_3148_; lean_object* v_tail_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; 
v_root_3148_ = lean_ctor_get(v_t_3125_, 0);
v_tail_3149_ = lean_ctor_get(v_t_3125_, 1);
v___x_3150_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(v_root_3148_, v_init_3126_);
v___x_3151_ = lean_array_get_size(v_tail_3149_);
v___x_3152_ = lean_nat_dec_lt(v___x_3128_, v___x_3151_);
if (v___x_3152_ == 0)
{
return v___x_3150_;
}
else
{
size_t v___x_3153_; size_t v___x_3154_; lean_object* v___x_3155_; 
v___x_3153_ = ((size_t)0ULL);
v___x_3154_ = lean_usize_of_nat(v___x_3151_);
v___x_3155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(v_tail_3149_, v___x_3153_, v___x_3154_, v___x_3150_);
return v___x_3155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5___boxed(lean_object* v_t_3156_, lean_object* v_init_3157_, lean_object* v_start_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(v_t_3156_, v_init_3157_, v_start_3158_);
lean_dec(v_start_3158_);
lean_dec_ref(v_t_3156_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(lean_object* v_as_3160_, size_t v_sz_3161_, size_t v_i_3162_, lean_object* v_b_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
uint8_t v___x_3175_; 
v___x_3175_ = lean_usize_dec_lt(v_i_3162_, v_sz_3161_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; 
v___x_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3176_, 0, v_b_3163_);
return v___x_3176_;
}
else
{
lean_object* v___x_3177_; lean_object* v_a_3178_; lean_object* v___x_3179_; 
v___x_3177_ = lean_box(0);
v_a_3178_ = lean_array_uget_borrowed(v_as_3160_, v_i_3162_);
lean_inc_ref(v___y_3172_);
lean_inc(v_a_3178_);
v___x_3179_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_a_3178_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3179_) == 0)
{
size_t v___x_3180_; size_t v___x_3181_; 
lean_dec_ref_known(v___x_3179_, 1);
v___x_3180_ = ((size_t)1ULL);
v___x_3181_ = lean_usize_add(v_i_3162_, v___x_3180_);
v_i_3162_ = v___x_3181_;
v_b_3163_ = v___x_3177_;
goto _start;
}
else
{
return v___x_3179_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14___boxed(lean_object* v_as_3183_, lean_object* v_sz_3184_, lean_object* v_i_3185_, lean_object* v_b_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
size_t v_sz_boxed_3198_; size_t v_i_boxed_3199_; lean_object* v_res_3200_; 
v_sz_boxed_3198_ = lean_unbox_usize(v_sz_3184_);
lean_dec(v_sz_3184_);
v_i_boxed_3199_ = lean_unbox_usize(v_i_3185_);
lean_dec(v_i_3185_);
v_res_3200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v_as_3183_, v_sz_boxed_3198_, v_i_boxed_3199_, v_b_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v_as_3183_);
return v_res_3200_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(lean_object* v___x_3201_, uint8_t v_force_3202_, uint8_t v___x_3203_, lean_object* v_a_3204_, uint8_t v___x_3205_, lean_object* v_x_3206_){
_start:
{
if (lean_obj_tag(v_x_3206_) == 0)
{
uint8_t v___x_3207_; 
v___x_3207_ = 0;
return v___x_3207_;
}
else
{
lean_object* v_head_3208_; lean_object* v_tail_3209_; uint8_t v___y_3211_; lean_object* v___x_3213_; lean_object* v___x_3214_; uint8_t v___x_3215_; 
v_head_3208_ = lean_ctor_get(v_x_3206_, 0);
v_tail_3209_ = lean_ctor_get(v_x_3206_, 1);
v___x_3213_ = lean_unsigned_to_nat(0u);
v___x_3214_ = lean_array_get_borrowed(v___x_3213_, v___x_3201_, v_head_3208_);
v___x_3215_ = lean_nat_dec_eq(v___x_3214_, v_head_3208_);
if (v___x_3215_ == 0)
{
uint8_t v___x_3216_; 
v___x_3216_ = 1;
if (v_force_3202_ == 0)
{
if (v___x_3203_ == 0)
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; 
v___x_3217_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_3218_ = lean_unsigned_to_nat(1u);
v___x_3219_ = lean_array_get_borrowed(v___x_3217_, v_a_3204_, v_head_3208_);
v___x_3220_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_3219_);
v___x_3221_ = lean_nat_dec_lt(v___x_3218_, v___x_3220_);
lean_dec(v___x_3220_);
v___y_3211_ = v___x_3221_;
goto v___jp_3210_;
}
else
{
return v___x_3216_;
}
}
else
{
return v___x_3216_;
}
}
else
{
v___y_3211_ = v___x_3205_;
goto v___jp_3210_;
}
v___jp_3210_:
{
if (v___y_3211_ == 0)
{
v_x_3206_ = v_tail_3209_;
goto _start;
}
else
{
return v___y_3211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___boxed(lean_object* v___x_3222_, lean_object* v_force_3223_, lean_object* v___x_3224_, lean_object* v_a_3225_, lean_object* v___x_3226_, lean_object* v_x_3227_){
_start:
{
uint8_t v_force_boxed_3228_; uint8_t v___x_106472__boxed_3229_; uint8_t v___x_106474__boxed_3230_; uint8_t v_res_3231_; lean_object* v_r_3232_; 
v_force_boxed_3228_ = lean_unbox(v_force_3223_);
v___x_106472__boxed_3229_ = lean_unbox(v___x_3224_);
v___x_106474__boxed_3230_ = lean_unbox(v___x_3226_);
v_res_3231_ = l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(v___x_3222_, v_force_boxed_3228_, v___x_106472__boxed_3229_, v_a_3225_, v___x_106474__boxed_3230_, v_x_3227_);
lean_dec(v_x_3227_);
lean_dec_ref(v_a_3225_);
lean_dec_ref(v___x_3222_);
v_r_3232_ = lean_box(v_res_3231_);
return v_r_3232_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(lean_object* v_a_3233_, lean_object* v_a_3234_){
_start:
{
if (lean_obj_tag(v_a_3233_) == 0)
{
lean_object* v___x_3235_; 
v___x_3235_ = l_List_reverse___redArg(v_a_3234_);
return v___x_3235_;
}
else
{
lean_object* v_head_3236_; lean_object* v_tail_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3248_; 
v_head_3236_ = lean_ctor_get(v_a_3233_, 0);
v_tail_3237_ = lean_ctor_get(v_a_3233_, 1);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_a_3233_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3239_ = v_a_3233_;
v_isShared_3240_ = v_isSharedCheck_3248_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_tail_3237_);
lean_inc(v_head_3236_);
lean_dec(v_a_3233_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3248_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3245_; 
v___x_3241_ = l_Nat_reprFast(v_head_3236_);
v___x_3242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
v___x_3243_ = l_Lean_MessageData_ofFormat(v___x_3242_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 1, v_a_3234_);
lean_ctor_set(v___x_3239_, 0, v___x_3243_);
v___x_3245_ = v___x_3239_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_a_3234_);
v___x_3245_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
v_a_3233_ = v_tail_3237_;
v_a_3234_ = v___x_3245_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(lean_object* v_as_3249_, size_t v_sz_3250_, size_t v_i_3251_, lean_object* v_b_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
uint8_t v___x_3264_; 
v___x_3264_ = lean_usize_dec_lt(v_i_3251_, v_sz_3250_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; 
v___x_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3265_, 0, v_b_3252_);
return v___x_3265_;
}
else
{
lean_object* v___x_3266_; lean_object* v_a_3267_; lean_object* v___x_3268_; 
v___x_3266_ = lean_box(0);
v_a_3267_ = lean_array_uget_borrowed(v_as_3249_, v_i_3251_);
lean_inc(v_a_3267_);
v___x_3268_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_assert(v_a_3267_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
if (lean_obj_tag(v___x_3268_) == 0)
{
size_t v___x_3269_; size_t v___x_3270_; 
lean_dec_ref_known(v___x_3268_, 1);
v___x_3269_ = ((size_t)1ULL);
v___x_3270_ = lean_usize_add(v_i_3251_, v___x_3269_);
v_i_3251_ = v___x_3270_;
v_b_3252_ = v___x_3266_;
goto _start;
}
else
{
return v___x_3268_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___boxed(lean_object* v_as_3272_, lean_object* v_sz_3273_, lean_object* v_i_3274_, lean_object* v_b_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
size_t v_sz_boxed_3287_; size_t v_i_boxed_3288_; lean_object* v_res_3289_; 
v_sz_boxed_3287_ = lean_unbox_usize(v_sz_3273_);
lean_dec(v_sz_3273_);
v_i_boxed_3288_ = lean_unbox_usize(v_i_3274_);
lean_dec(v_i_3274_);
v_res_3289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v_as_3272_, v_sz_boxed_3287_, v_i_boxed_3288_, v_b_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v_as_3272_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(lean_object* v_as_3290_, size_t v_sz_3291_, size_t v_i_3292_, lean_object* v_b_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
uint8_t v___x_3305_; 
v___x_3305_ = lean_usize_dec_lt(v_i_3292_, v_sz_3291_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; 
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v_b_3293_);
return v___x_3306_;
}
else
{
lean_object* v___x_3307_; lean_object* v_a_3308_; lean_object* v___x_3309_; 
v___x_3307_ = lean_box(0);
v_a_3308_ = lean_array_uget_borrowed(v_as_3290_, v_i_3292_);
lean_inc(v___y_3303_);
lean_inc_ref(v___y_3302_);
lean_inc(v___y_3301_);
lean_inc_ref(v___y_3300_);
lean_inc(v___y_3299_);
lean_inc_ref(v___y_3298_);
lean_inc(v___y_3297_);
lean_inc_ref(v___y_3296_);
lean_inc(v___y_3295_);
lean_inc(v___y_3294_);
lean_inc(v_a_3308_);
v___x_3309_ = lean_grind_cutsat_assert_le(v_a_3308_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
if (lean_obj_tag(v___x_3309_) == 0)
{
size_t v___x_3310_; size_t v___x_3311_; 
lean_dec_ref_known(v___x_3309_, 1);
v___x_3310_ = ((size_t)1ULL);
v___x_3311_ = lean_usize_add(v_i_3292_, v___x_3310_);
v_i_3292_ = v___x_3311_;
v_b_3293_ = v___x_3307_;
goto _start;
}
else
{
return v___x_3309_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15___boxed(lean_object* v_as_3313_, lean_object* v_sz_3314_, lean_object* v_i_3315_, lean_object* v_b_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
size_t v_sz_boxed_3328_; size_t v_i_boxed_3329_; lean_object* v_res_3330_; 
v_sz_boxed_3328_ = lean_unbox_usize(v_sz_3314_);
lean_dec(v_sz_3314_);
v_i_boxed_3329_ = lean_unbox_usize(v_i_3315_);
lean_dec(v_i_3315_);
v_res_3330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v_as_3313_, v_sz_boxed_3328_, v_i_boxed_3329_, v_b_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v_as_3313_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(lean_object* v_msgData_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v___x_3337_; lean_object* v_env_3338_; uint8_t v___x_3339_; lean_object* v_env_3340_; lean_object* v___x_3341_; lean_object* v_toCold_3342_; lean_object* v_mctx_3343_; lean_object* v_lctx_3344_; lean_object* v_options_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3337_ = lean_st_ref_get(v___y_3335_);
v_env_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc_ref(v_env_3338_);
lean_dec(v___x_3337_);
v___x_3339_ = 0;
v_env_3340_ = l_Lean_Environment_setRecordingDeps(v_env_3338_, v___x_3339_);
v___x_3341_ = lean_st_ref_get(v___y_3333_);
v_toCold_3342_ = lean_ctor_get(v___y_3334_, 0);
v_mctx_3343_ = lean_ctor_get(v___x_3341_, 0);
lean_inc_ref(v_mctx_3343_);
lean_dec(v___x_3341_);
v_lctx_3344_ = lean_ctor_get(v___y_3332_, 2);
v_options_3345_ = lean_ctor_get(v_toCold_3342_, 2);
lean_inc_ref(v_options_3345_);
lean_inc_ref(v_lctx_3344_);
v___x_3346_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3346_, 0, v_env_3340_);
lean_ctor_set(v___x_3346_, 1, v_mctx_3343_);
lean_ctor_set(v___x_3346_, 2, v_lctx_3344_);
lean_ctor_set(v___x_3346_, 3, v_options_3345_);
v___x_3347_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
lean_ctor_set(v___x_3347_, 1, v_msgData_3331_);
v___x_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38___boxed(lean_object* v_msgData_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(v_msgData_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
return v_res_3355_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0(void){
_start:
{
lean_object* v___x_3356_; double v___x_3357_; 
v___x_3356_ = lean_unsigned_to_nat(0u);
v___x_3357_ = lean_float_of_nat(v___x_3356_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(lean_object* v_cls_3361_, lean_object* v_msg_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v_ref_3368_; lean_object* v___x_3369_; lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3415_; 
v_ref_3368_ = lean_ctor_get(v___y_3365_, 2);
v___x_3369_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(v_msg_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3372_ = v___x_3369_;
v_isShared_3373_ = v_isSharedCheck_3415_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3369_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3415_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3374_; lean_object* v_traceState_3375_; lean_object* v_env_3376_; lean_object* v_nextMacroScope_3377_; lean_object* v_ngen_3378_; lean_object* v_auxDeclNGen_3379_; lean_object* v_cache_3380_; lean_object* v_recordedDeps_3381_; lean_object* v_messages_3382_; lean_object* v_infoState_3383_; lean_object* v_snapshotTasks_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3414_; 
v___x_3374_ = lean_st_ref_take(v___y_3366_);
v_traceState_3375_ = lean_ctor_get(v___x_3374_, 4);
v_env_3376_ = lean_ctor_get(v___x_3374_, 0);
v_nextMacroScope_3377_ = lean_ctor_get(v___x_3374_, 1);
v_ngen_3378_ = lean_ctor_get(v___x_3374_, 2);
v_auxDeclNGen_3379_ = lean_ctor_get(v___x_3374_, 3);
v_cache_3380_ = lean_ctor_get(v___x_3374_, 5);
v_recordedDeps_3381_ = lean_ctor_get(v___x_3374_, 6);
v_messages_3382_ = lean_ctor_get(v___x_3374_, 7);
v_infoState_3383_ = lean_ctor_get(v___x_3374_, 8);
v_snapshotTasks_3384_ = lean_ctor_get(v___x_3374_, 9);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3386_ = v___x_3374_;
v_isShared_3387_ = v_isSharedCheck_3414_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_snapshotTasks_3384_);
lean_inc(v_infoState_3383_);
lean_inc(v_messages_3382_);
lean_inc(v_recordedDeps_3381_);
lean_inc(v_cache_3380_);
lean_inc(v_traceState_3375_);
lean_inc(v_auxDeclNGen_3379_);
lean_inc(v_ngen_3378_);
lean_inc(v_nextMacroScope_3377_);
lean_inc(v_env_3376_);
lean_dec(v___x_3374_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3414_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
uint64_t v_tid_3388_; lean_object* v_traces_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3413_; 
v_tid_3388_ = lean_ctor_get_uint64(v_traceState_3375_, sizeof(void*)*1);
v_traces_3389_ = lean_ctor_get(v_traceState_3375_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v_traceState_3375_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3391_ = v_traceState_3375_;
v_isShared_3392_ = v_isSharedCheck_3413_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_traces_3389_);
lean_dec(v_traceState_3375_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3413_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; double v___x_3395_; uint8_t v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3404_; 
v___x_3393_ = lean_box(0);
v___x_3394_ = lean_box(0);
v___x_3395_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0);
v___x_3396_ = 0;
v___x_3397_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__1));
v___x_3398_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3398_, 0, v_cls_3361_);
lean_ctor_set(v___x_3398_, 1, v___x_3394_);
lean_ctor_set(v___x_3398_, 2, v___x_3397_);
lean_ctor_set_float(v___x_3398_, sizeof(void*)*3, v___x_3395_);
lean_ctor_set_float(v___x_3398_, sizeof(void*)*3 + 8, v___x_3395_);
lean_ctor_set_uint8(v___x_3398_, sizeof(void*)*3 + 16, v___x_3396_);
v___x_3399_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__2));
v___x_3400_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3398_);
lean_ctor_set(v___x_3400_, 1, v_a_3370_);
lean_ctor_set(v___x_3400_, 2, v___x_3399_);
lean_inc(v_ref_3368_);
v___x_3401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3401_, 0, v_ref_3368_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = l_Lean_PersistentArray_push___redArg(v_traces_3389_, v___x_3401_);
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 0, v___x_3402_);
v___x_3404_ = v___x_3391_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3402_);
lean_ctor_set_uint64(v_reuseFailAlloc_3412_, sizeof(void*)*1, v_tid_3388_);
v___x_3404_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3406_; 
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 4, v___x_3404_);
v___x_3406_ = v___x_3386_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_env_3376_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_nextMacroScope_3377_);
lean_ctor_set(v_reuseFailAlloc_3411_, 2, v_ngen_3378_);
lean_ctor_set(v_reuseFailAlloc_3411_, 3, v_auxDeclNGen_3379_);
lean_ctor_set(v_reuseFailAlloc_3411_, 4, v___x_3404_);
lean_ctor_set(v_reuseFailAlloc_3411_, 5, v_cache_3380_);
lean_ctor_set(v_reuseFailAlloc_3411_, 6, v_recordedDeps_3381_);
lean_ctor_set(v_reuseFailAlloc_3411_, 7, v_messages_3382_);
lean_ctor_set(v_reuseFailAlloc_3411_, 8, v_infoState_3383_);
lean_ctor_set(v_reuseFailAlloc_3411_, 9, v_snapshotTasks_3384_);
v___x_3406_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
lean_object* v___x_3407_; lean_object* v___x_3409_; 
v___x_3407_ = lean_st_ref_put(v___y_3366_, v___x_3406_);
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 0, v___x_3393_);
v___x_3409_ = v___x_3372_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3393_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___boxed(lean_object* v_cls_3416_, lean_object* v_msg_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v_cls_3416_, v_msg_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(lean_object* v_as_3424_, size_t v_i_3425_, size_t v_stop_3426_, lean_object* v_b_3427_){
_start:
{
uint8_t v___x_3428_; 
v___x_3428_ = lean_usize_dec_eq(v_i_3425_, v_stop_3426_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; size_t v___x_3432_; size_t v___x_3433_; 
v___x_3429_ = lean_array_uget_borrowed(v_as_3424_, v_i_3425_);
v___x_3430_ = l_Lean_PersistentArray_toArray___redArg(v___x_3429_);
v___x_3431_ = l_Array_append___redArg(v_b_3427_, v___x_3430_);
lean_dec_ref(v___x_3430_);
v___x_3432_ = ((size_t)1ULL);
v___x_3433_ = lean_usize_add(v_i_3425_, v___x_3432_);
v_i_3425_ = v___x_3433_;
v_b_3427_ = v___x_3431_;
goto _start;
}
else
{
return v_b_3427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___boxed(lean_object* v_as_3435_, lean_object* v_i_3436_, lean_object* v_stop_3437_, lean_object* v_b_3438_){
_start:
{
size_t v_i_boxed_3439_; size_t v_stop_boxed_3440_; lean_object* v_res_3441_; 
v_i_boxed_3439_ = lean_unbox_usize(v_i_3436_);
lean_dec(v_i_3436_);
v_stop_boxed_3440_ = lean_unbox_usize(v_stop_3437_);
lean_dec(v_stop_3437_);
v_res_3441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(v_as_3435_, v_i_boxed_3439_, v_stop_boxed_3440_, v_b_3438_);
lean_dec_ref(v_as_3435_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(lean_object* v_x_3442_, lean_object* v_x_3443_){
_start:
{
if (lean_obj_tag(v_x_3442_) == 0)
{
lean_object* v_cs_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; 
v_cs_3444_ = lean_ctor_get(v_x_3442_, 0);
v___x_3445_ = lean_unsigned_to_nat(0u);
v___x_3446_ = lean_array_get_size(v_cs_3444_);
v___x_3447_ = lean_nat_dec_lt(v___x_3445_, v___x_3446_);
if (v___x_3447_ == 0)
{
return v_x_3443_;
}
else
{
size_t v___x_3448_; size_t v___x_3449_; lean_object* v___x_3450_; 
v___x_3448_ = ((size_t)0ULL);
v___x_3449_ = lean_usize_of_nat(v___x_3446_);
v___x_3450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__8(v_cs_3444_, v___x_3448_, v___x_3449_, v_x_3443_);
return v___x_3450_;
}
}
else
{
lean_object* v_vs_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; uint8_t v___x_3454_; 
v_vs_3451_ = lean_ctor_get(v_x_3442_, 0);
v___x_3452_ = lean_unsigned_to_nat(0u);
v___x_3453_ = lean_array_get_size(v_vs_3451_);
v___x_3454_ = lean_nat_dec_lt(v___x_3452_, v___x_3453_);
if (v___x_3454_ == 0)
{
return v_x_3443_;
}
else
{
size_t v___x_3455_; size_t v___x_3456_; lean_object* v___x_3457_; 
v___x_3455_ = ((size_t)0ULL);
v___x_3456_ = lean_usize_of_nat(v___x_3453_);
v___x_3457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(v_vs_3451_, v___x_3455_, v___x_3456_, v_x_3443_);
return v___x_3457_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__8(lean_object* v_as_3458_, size_t v_i_3459_, size_t v_stop_3460_, lean_object* v_b_3461_){
_start:
{
uint8_t v___x_3462_; 
v___x_3462_ = lean_usize_dec_eq(v_i_3459_, v_stop_3460_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; size_t v___x_3465_; size_t v___x_3466_; 
v___x_3463_ = lean_array_uget_borrowed(v_as_3458_, v_i_3459_);
v___x_3464_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(v___x_3463_, v_b_3461_);
v___x_3465_ = ((size_t)1ULL);
v___x_3466_ = lean_usize_add(v_i_3459_, v___x_3465_);
v_i_3459_ = v___x_3466_;
v_b_3461_ = v___x_3464_;
goto _start;
}
else
{
return v_b_3461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__8___boxed(lean_object* v_as_3468_, lean_object* v_i_3469_, lean_object* v_stop_3470_, lean_object* v_b_3471_){
_start:
{
size_t v_i_boxed_3472_; size_t v_stop_boxed_3473_; lean_object* v_res_3474_; 
v_i_boxed_3472_ = lean_unbox_usize(v_i_3469_);
lean_dec(v_i_3469_);
v_stop_boxed_3473_ = lean_unbox_usize(v_stop_3470_);
lean_dec(v_stop_3470_);
v_res_3474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__8(v_as_3468_, v_i_boxed_3472_, v_stop_boxed_3473_, v_b_3471_);
lean_dec_ref(v_as_3468_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8___boxed(lean_object* v_x_3475_, lean_object* v_x_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(v_x_3475_, v_x_3476_);
lean_dec_ref(v_x_3475_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6(lean_object* v_x_3478_, size_t v_x_3479_, size_t v_x_3480_, lean_object* v_x_3481_){
_start:
{
if (lean_obj_tag(v_x_3478_) == 0)
{
lean_object* v_cs_3482_; lean_object* v___x_3483_; size_t v___x_3484_; lean_object* v_j_3485_; lean_object* v___x_3486_; size_t v___x_3487_; size_t v___x_3488_; size_t v___x_3489_; size_t v___x_3490_; size_t v___x_3491_; size_t v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; 
v_cs_3482_ = lean_ctor_get(v_x_3478_, 0);
v___x_3483_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___closed__0);
v___x_3484_ = lean_usize_shift_right(v_x_3479_, v_x_3480_);
v_j_3485_ = lean_usize_to_nat(v___x_3484_);
v___x_3486_ = lean_array_get_borrowed(v___x_3483_, v_cs_3482_, v_j_3485_);
v___x_3487_ = ((size_t)1ULL);
v___x_3488_ = lean_usize_shift_left(v___x_3487_, v_x_3480_);
v___x_3489_ = lean_usize_sub(v___x_3488_, v___x_3487_);
v___x_3490_ = lean_usize_land(v_x_3479_, v___x_3489_);
v___x_3491_ = ((size_t)5ULL);
v___x_3492_ = lean_usize_sub(v_x_3480_, v___x_3491_);
v___x_3493_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6(v___x_3486_, v___x_3490_, v___x_3492_, v_x_3481_);
v___x_3494_ = lean_unsigned_to_nat(1u);
v___x_3495_ = lean_nat_add(v_j_3485_, v___x_3494_);
lean_dec(v_j_3485_);
v___x_3496_ = lean_array_get_size(v_cs_3482_);
v___x_3497_ = lean_nat_dec_lt(v___x_3495_, v___x_3496_);
if (v___x_3497_ == 0)
{
lean_dec(v___x_3495_);
return v___x_3493_;
}
else
{
size_t v___x_3498_; size_t v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = lean_usize_of_nat(v___x_3495_);
lean_dec(v___x_3495_);
v___x_3499_ = lean_usize_of_nat(v___x_3496_);
v___x_3500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__8(v_cs_3482_, v___x_3498_, v___x_3499_, v___x_3493_);
return v___x_3500_;
}
}
else
{
lean_object* v_vs_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v_vs_3501_ = lean_ctor_get(v_x_3478_, 0);
v___x_3502_ = lean_usize_to_nat(v_x_3479_);
v___x_3503_ = lean_array_get_size(v_vs_3501_);
v___x_3504_ = lean_nat_dec_lt(v___x_3502_, v___x_3503_);
if (v___x_3504_ == 0)
{
lean_dec(v___x_3502_);
return v_x_3481_;
}
else
{
size_t v___x_3505_; size_t v___x_3506_; lean_object* v___x_3507_; 
v___x_3505_ = lean_usize_of_nat(v___x_3502_);
lean_dec(v___x_3502_);
v___x_3506_ = lean_usize_of_nat(v___x_3503_);
v___x_3507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(v_vs_3501_, v___x_3505_, v___x_3506_, v_x_3481_);
return v___x_3507_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6___boxed(lean_object* v_x_3508_, lean_object* v_x_3509_, lean_object* v_x_3510_, lean_object* v_x_3511_){
_start:
{
size_t v_x_106836__boxed_3512_; size_t v_x_106837__boxed_3513_; lean_object* v_res_3514_; 
v_x_106836__boxed_3512_ = lean_unbox_usize(v_x_3509_);
lean_dec(v_x_3509_);
v_x_106837__boxed_3513_ = lean_unbox_usize(v_x_3510_);
lean_dec(v_x_3510_);
v_res_3514_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6(v_x_3508_, v_x_106836__boxed_3512_, v_x_106837__boxed_3513_, v_x_3511_);
lean_dec_ref(v_x_3508_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(lean_object* v_t_3515_, lean_object* v_init_3516_, lean_object* v_start_3517_){
_start:
{
lean_object* v___x_3518_; uint8_t v___x_3519_; 
v___x_3518_ = lean_unsigned_to_nat(0u);
v___x_3519_ = lean_nat_dec_eq(v_start_3517_, v___x_3518_);
if (v___x_3519_ == 0)
{
lean_object* v_root_3520_; lean_object* v_tail_3521_; size_t v_shift_3522_; lean_object* v_tailOff_3523_; uint8_t v___x_3524_; 
v_root_3520_ = lean_ctor_get(v_t_3515_, 0);
v_tail_3521_ = lean_ctor_get(v_t_3515_, 1);
v_shift_3522_ = lean_ctor_get_usize(v_t_3515_, 4);
v_tailOff_3523_ = lean_ctor_get(v_t_3515_, 3);
v___x_3524_ = lean_nat_dec_le(v_tailOff_3523_, v_start_3517_);
if (v___x_3524_ == 0)
{
size_t v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; uint8_t v___x_3528_; 
v___x_3525_ = lean_usize_of_nat(v_start_3517_);
v___x_3526_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6(v_root_3520_, v___x_3525_, v_shift_3522_, v_init_3516_);
v___x_3527_ = lean_array_get_size(v_tail_3521_);
v___x_3528_ = lean_nat_dec_lt(v___x_3518_, v___x_3527_);
if (v___x_3528_ == 0)
{
return v___x_3526_;
}
else
{
size_t v___x_3529_; size_t v___x_3530_; lean_object* v___x_3531_; 
v___x_3529_ = ((size_t)0ULL);
v___x_3530_ = lean_usize_of_nat(v___x_3527_);
v___x_3531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(v_tail_3521_, v___x_3529_, v___x_3530_, v___x_3526_);
return v___x_3531_;
}
}
else
{
lean_object* v___x_3532_; lean_object* v___x_3533_; uint8_t v___x_3534_; 
v___x_3532_ = lean_nat_sub(v_start_3517_, v_tailOff_3523_);
v___x_3533_ = lean_array_get_size(v_tail_3521_);
v___x_3534_ = lean_nat_dec_lt(v___x_3532_, v___x_3533_);
if (v___x_3534_ == 0)
{
lean_dec(v___x_3532_);
return v_init_3516_;
}
else
{
size_t v___x_3535_; size_t v___x_3536_; lean_object* v___x_3537_; 
v___x_3535_ = lean_usize_of_nat(v___x_3532_);
lean_dec(v___x_3532_);
v___x_3536_ = lean_usize_of_nat(v___x_3533_);
v___x_3537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(v_tail_3521_, v___x_3535_, v___x_3536_, v_init_3516_);
return v___x_3537_;
}
}
}
else
{
lean_object* v_root_3538_; lean_object* v_tail_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v_root_3538_ = lean_ctor_get(v_t_3515_, 0);
v_tail_3539_ = lean_ctor_get(v_t_3515_, 1);
v___x_3540_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(v_root_3538_, v_init_3516_);
v___x_3541_ = lean_array_get_size(v_tail_3539_);
v___x_3542_ = lean_nat_dec_lt(v___x_3518_, v___x_3541_);
if (v___x_3542_ == 0)
{
return v___x_3540_;
}
else
{
size_t v___x_3543_; size_t v___x_3544_; lean_object* v___x_3545_; 
v___x_3543_ = ((size_t)0ULL);
v___x_3544_ = lean_usize_of_nat(v___x_3541_);
v___x_3545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(v_tail_3539_, v___x_3543_, v___x_3544_, v___x_3540_);
return v___x_3545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3___boxed(lean_object* v_t_3546_, lean_object* v_init_3547_, lean_object* v_start_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(v_t_3546_, v_init_3547_, v_start_3548_);
lean_dec(v_start_3548_);
lean_dec_ref(v_t_3546_);
return v_res_3549_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2));
v___x_3555_ = l_Lean_stringToMessageData(v___x_3554_);
return v___x_3555_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3569_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10));
v___x_3570_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1));
v___x_3571_ = l_Lean_Name_append(v___x_3570_, v___x_3569_);
return v___x_3571_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12));
v___x_3574_ = l_Lean_stringToMessageData(v___x_3573_);
return v___x_3574_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15(void){
_start:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3579_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14));
v___x_3580_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1));
v___x_3581_ = l_Lean_Name_append(v___x_3580_, v___x_3579_);
return v___x_3581_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17(void){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3583_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__16));
v___x_3584_ = l_Lean_stringToMessageData(v___x_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(uint8_t v_force_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; uint8_t v___x_3600_; lean_object* v___x_3601_; 
v___x_3597_ = lean_unsigned_to_nat(0u);
v___x_3598_ = l_Lean_instInhabitedExpr;
v___x_3599_ = lean_box(0);
v___x_3600_ = 0;
v___x_3601_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3586_, v_a_3594_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3753_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3604_ = v___x_3601_;
v_isShared_3605_ = v_isSharedCheck_3753_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3601_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3753_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v_vars_3606_; lean_object* v_varsHistory_3607_; lean_object* v_dvds_3608_; lean_object* v_lowers_3609_; lean_object* v_uppers_3610_; lean_object* v_diseqs_3611_; uint8_t v___x_3612_; 
v_vars_3606_ = lean_ctor_get(v_a_3602_, 0);
lean_inc_ref(v_vars_3606_);
v_varsHistory_3607_ = lean_ctor_get(v_a_3602_, 2);
lean_inc_ref(v_varsHistory_3607_);
v_dvds_3608_ = lean_ctor_get(v_a_3602_, 5);
lean_inc_ref(v_dvds_3608_);
v_lowers_3609_ = lean_ctor_get(v_a_3602_, 6);
lean_inc_ref(v_lowers_3609_);
v_uppers_3610_ = lean_ctor_get(v_a_3602_, 7);
lean_inc_ref(v_uppers_3610_);
v_diseqs_3611_ = lean_ctor_get(v_a_3602_, 8);
lean_inc_ref(v_diseqs_3611_);
lean_dec(v_a_3602_);
v___x_3612_ = l_Lean_PersistentArray_isEmpty___redArg(v_vars_3606_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; 
lean_del_object(v___x_3604_);
v___x_3613_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3615_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3613_, 1);
v___x_3615_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(v_a_3614_, v_a_3586_, v_a_3594_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3732_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3618_ = v___x_3615_;
v_isShared_3619_ = v_isSharedCheck_3732_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3615_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3732_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v_size_3620_; lean_object* v___x_3621_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v_options_3633_; lean_object* v_inheritedTraceOptions_3634_; lean_object* v___y_3635_; uint8_t v___x_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v_size_3620_ = lean_ctor_get(v_vars_3606_, 2);
lean_inc(v_size_3620_);
lean_dec_ref(v_vars_3606_);
v___x_3621_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_a_3616_);
v___x_3648_ = l_Lean_PersistentArray_isEmpty___redArg(v_varsHistory_3607_);
v___x_3649_ = l_List_range(v_size_3620_);
v___x_3650_ = l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(v___x_3621_, v_force_3585_, v___x_3648_, v_a_3614_, v___x_3612_, v___x_3649_);
lean_dec(v___x_3649_);
lean_dec(v_a_3614_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; lean_object* v___x_3653_; 
lean_dec_ref(v___x_3621_);
lean_dec(v_a_3616_);
lean_dec_ref(v_diseqs_3611_);
lean_dec_ref(v_uppers_3610_);
lean_dec_ref(v_lowers_3609_);
lean_dec_ref(v_dvds_3608_);
lean_dec_ref(v_varsHistory_3607_);
v___x_3651_ = lean_box(0);
if (v_isShared_3619_ == 0)
{
lean_ctor_set(v___x_3618_, 0, v___x_3651_);
v___x_3653_ = v___x_3618_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3651_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
else
{
lean_object* v_toCold_3655_; lean_object* v_options_3656_; lean_object* v_inheritedTraceOptions_3657_; uint8_t v_hasTrace_3658_; lean_object* v___f_3659_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; 
lean_del_object(v___x_3618_);
v_toCold_3655_ = lean_ctor_get(v_a_3594_, 0);
v_options_3656_ = lean_ctor_get(v_toCold_3655_, 2);
v_inheritedTraceOptions_3657_ = lean_ctor_get(v_toCold_3655_, 11);
v_hasTrace_3658_ = lean_ctor_get_uint8(v_options_3656_, sizeof(void*)*1);
lean_inc_ref(v___x_3621_);
v___f_3659_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3659_, 0, v___x_3597_);
lean_closure_set(v___f_3659_, 1, v___x_3621_);
if (v_hasTrace_3658_ == 0)
{
lean_dec_ref(v_varsHistory_3607_);
v___y_3661_ = v_a_3586_;
v___y_3662_ = v_a_3587_;
v___y_3663_ = v_a_3588_;
v___y_3664_ = v_a_3589_;
v___y_3665_ = v_a_3590_;
v___y_3666_ = v_a_3591_;
v___y_3667_ = v_a_3592_;
v___y_3668_ = v_a_3593_;
v___y_3669_ = v_a_3594_;
v___y_3670_ = v_a_3595_;
goto v___jp_3660_;
}
else
{
lean_object* v___x_3720_; lean_object* v___x_3721_; uint8_t v___x_3722_; 
v___x_3720_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14));
v___x_3721_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15);
v___x_3722_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3657_, v_options_3656_, v___x_3721_);
if (v___x_3722_ == 0)
{
lean_dec_ref(v_varsHistory_3607_);
v___y_3661_ = v_a_3586_;
v___y_3662_ = v_a_3587_;
v___y_3663_ = v_a_3588_;
v___y_3664_ = v_a_3589_;
v___y_3665_ = v_a_3590_;
v___y_3666_ = v_a_3591_;
v___y_3667_ = v_a_3592_;
v___y_3668_ = v_a_3593_;
v___y_3669_ = v_a_3594_;
v___y_3670_ = v_a_3595_;
goto v___jp_3660_;
}
else
{
lean_object* v_size_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_size_3723_ = lean_ctor_get(v_varsHistory_3607_, 2);
lean_inc(v_size_3723_);
lean_dec_ref(v_varsHistory_3607_);
v___x_3724_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17);
v___x_3725_ = lean_unsigned_to_nat(1u);
v___x_3726_ = lean_nat_add(v_size_3723_, v___x_3725_);
lean_dec(v_size_3723_);
v___x_3727_ = l_Nat_reprFast(v___x_3726_);
v___x_3728_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3727_);
v___x_3729_ = l_Lean_MessageData_ofFormat(v___x_3728_);
v___x_3730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3724_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v___x_3720_, v___x_3730_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_dec_ref_known(v___x_3731_, 1);
v___y_3661_ = v_a_3586_;
v___y_3662_ = v_a_3587_;
v___y_3663_ = v_a_3588_;
v___y_3664_ = v_a_3589_;
v___y_3665_ = v_a_3590_;
v___y_3666_ = v_a_3591_;
v___y_3667_ = v_a_3592_;
v___y_3668_ = v_a_3593_;
v___y_3669_ = v_a_3594_;
v___y_3670_ = v_a_3595_;
goto v___jp_3660_;
}
else
{
lean_dec_ref(v___f_3659_);
lean_dec_ref(v___x_3621_);
lean_dec(v_a_3616_);
lean_dec_ref(v_diseqs_3611_);
lean_dec_ref(v_uppers_3610_);
lean_dec_ref(v_lowers_3609_);
lean_dec_ref(v_dvds_3608_);
return v___x_3731_;
}
}
}
v___jp_3660_:
{
lean_object* v___x_3671_; 
v___x_3671_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v___x_3672_; lean_object* v___x_3673_; size_t v_sz_3674_; size_t v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; size_t v_sz_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; size_t v_sz_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
lean_dec_ref_known(v___x_3671_, 1);
v___x_3672_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7));
v___x_3673_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(v_dvds_3608_, v___x_3672_, v___x_3597_);
lean_dec_ref(v_dvds_3608_);
v_sz_3674_ = lean_array_size(v___x_3673_);
v___x_3675_ = ((size_t)0ULL);
v___x_3676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(v___x_3621_, v_sz_3674_, v___x_3675_, v___x_3673_);
v___x_3677_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(v_lowers_3609_, v___x_3672_, v___x_3597_);
lean_dec_ref(v_lowers_3609_);
v___x_3678_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(v_uppers_3610_, v___x_3677_, v___x_3597_);
lean_dec_ref(v_uppers_3610_);
v_sz_3679_ = lean_array_size(v___x_3678_);
v___x_3680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(v___x_3621_, v_sz_3679_, v___x_3675_, v___x_3678_);
v___x_3681_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(v_diseqs_3611_, v___x_3672_, v___x_3597_);
lean_dec_ref(v_diseqs_3611_);
v_sz_3682_ = lean_array_size(v___x_3681_);
v___x_3683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(v___x_3621_, v_sz_3682_, v___x_3675_, v___x_3681_);
v___x_3684_ = l_Lean_Meta_Grind_getGoalStackDepth___redArg(v___y_3661_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3685_; lean_object* v___x_3686_; lean_object* v___f_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
lean_inc(v_a_3685_);
lean_dec_ref_known(v___x_3684_, 1);
v___x_3686_ = lean_box(v___x_3600_);
lean_inc_ref(v___x_3621_);
lean_inc(v_a_3616_);
v___f_3687_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed), 8, 7);
lean_closure_set(v___f_3687_, 0, v___x_3598_);
lean_closure_set(v___f_3687_, 1, v_a_3616_);
lean_closure_set(v___f_3687_, 2, v___f_3659_);
lean_closure_set(v___f_3687_, 3, v___x_3599_);
lean_closure_set(v___f_3687_, 4, v___x_3621_);
lean_closure_set(v___f_3687_, 5, v_a_3685_);
lean_closure_set(v___f_3687_, 6, v___x_3686_);
v___x_3688_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3689_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3688_, v___f_3687_, v___y_3661_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v___x_3690_; size_t v_sz_3691_; lean_object* v___x_3692_; 
lean_dec_ref_known(v___x_3689_, 1);
v___x_3690_ = lean_box(0);
v_sz_3691_ = lean_array_size(v___x_3676_);
v___x_3692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v___x_3676_, v_sz_3691_, v___x_3675_, v___x_3690_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
lean_dec_ref(v___x_3676_);
if (lean_obj_tag(v___x_3692_) == 0)
{
size_t v_sz_3693_; lean_object* v___x_3694_; 
lean_dec_ref_known(v___x_3692_, 1);
v_sz_3693_ = lean_array_size(v___x_3680_);
v___x_3694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v___x_3680_, v_sz_3693_, v___x_3675_, v___x_3690_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
lean_dec_ref(v___x_3680_);
if (lean_obj_tag(v___x_3694_) == 0)
{
size_t v_sz_3695_; lean_object* v___x_3696_; 
lean_dec_ref_known(v___x_3694_, 1);
v_sz_3695_ = lean_array_size(v___x_3683_);
v___x_3696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v___x_3683_, v_sz_3695_, v___x_3675_, v___x_3690_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
lean_dec_ref(v___x_3683_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_toCold_3697_; lean_object* v_options_3698_; uint8_t v_hasTrace_3699_; 
lean_dec_ref_known(v___x_3696_, 1);
v_toCold_3697_ = lean_ctor_get(v___y_3669_, 0);
v_options_3698_ = lean_ctor_get(v_toCold_3697_, 2);
v_hasTrace_3699_ = lean_ctor_get_uint8(v_options_3698_, sizeof(void*)*1);
if (v_hasTrace_3699_ == 0)
{
lean_object* v___x_3700_; 
lean_dec_ref(v___x_3621_);
lean_dec(v_a_3616_);
v___x_3700_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
return v___x_3700_;
}
else
{
lean_object* v_inheritedTraceOptions_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; 
v_inheritedTraceOptions_3701_ = lean_ctor_get(v_toCold_3697_, 11);
v___x_3702_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10));
v___x_3703_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11);
v___x_3704_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3701_, v_options_3698_, v___x_3703_);
if (v___x_3704_ == 0)
{
lean_dec(v_a_3616_);
v___y_3623_ = v___x_3702_;
v___y_3624_ = v___y_3661_;
v___y_3625_ = v___y_3662_;
v___y_3626_ = v___y_3663_;
v___y_3627_ = v___y_3664_;
v___y_3628_ = v___y_3665_;
v___y_3629_ = v___y_3666_;
v___y_3630_ = v___y_3667_;
v___y_3631_ = v___y_3668_;
v___y_3632_ = v___y_3669_;
v_options_3633_ = v_options_3698_;
v_inheritedTraceOptions_3634_ = v_inheritedTraceOptions_3701_;
v___y_3635_ = v___y_3670_;
goto v___jp_3622_;
}
else
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3705_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13);
v___x_3706_ = lean_array_to_list(v_a_3616_);
v___x_3707_ = lean_box(0);
v___x_3708_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(v___x_3706_, v___x_3707_);
v___x_3709_ = l_Lean_MessageData_ofList(v___x_3708_);
v___x_3710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3705_);
lean_ctor_set(v___x_3710_, 1, v___x_3709_);
v___x_3711_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v___x_3702_, v___x_3710_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_dec_ref_known(v___x_3711_, 1);
v___y_3623_ = v___x_3702_;
v___y_3624_ = v___y_3661_;
v___y_3625_ = v___y_3662_;
v___y_3626_ = v___y_3663_;
v___y_3627_ = v___y_3664_;
v___y_3628_ = v___y_3665_;
v___y_3629_ = v___y_3666_;
v___y_3630_ = v___y_3667_;
v___y_3631_ = v___y_3668_;
v___y_3632_ = v___y_3669_;
v_options_3633_ = v_options_3698_;
v_inheritedTraceOptions_3634_ = v_inheritedTraceOptions_3701_;
v___y_3635_ = v___y_3670_;
goto v___jp_3622_;
}
else
{
lean_dec_ref(v___x_3621_);
return v___x_3711_;
}
}
}
}
else
{
lean_dec_ref(v___x_3621_);
lean_dec(v_a_3616_);
return v___x_3696_;
}
}
else
{
lean_dec_ref(v___x_3683_);
lean_dec_ref(v___x_3621_);
lean_dec(v_a_3616_);
return v___x_3694_;
}
}
else
{
lean_dec_ref(v___x_3683_);
lean_dec_ref(v___x_3680_);
lean_dec_ref(v___x_3621_);
lean_dec(v_a_3616_);
return v___x_3692_;
}
}
else
{
lean_dec_ref(v___x_3683_);
lean_dec_ref(v___x_3680_);
lean_dec_ref(v___x_3676_);
lean_dec_ref(v___x_3621_);
lean_dec(v_a_3616_);
return v___x_3689_;
}
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_dec_ref(v___x_3683_);
lean_dec_ref(v___x_3680_);
lean_dec_ref(v___x_3676_);
lean_dec_ref(v___f_3659_);
lean_dec_ref(v___x_3621_);
lean_dec(v_a_3616_);
v_a_3712_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3684_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3684_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
else
{
lean_dec_ref(v___f_3659_);
lean_dec_ref(v___x_3621_);
lean_dec(v_a_3616_);
lean_dec_ref(v_diseqs_3611_);
lean_dec_ref(v_uppers_3610_);
lean_dec_ref(v_lowers_3609_);
lean_dec_ref(v_dvds_3608_);
return v___x_3671_;
}
}
}
v___jp_3622_:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; 
v___x_3636_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1));
lean_inc(v___y_3623_);
v___x_3637_ = l_Lean_Name_append(v___x_3636_, v___y_3623_);
v___x_3638_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3634_, v_options_3633_, v___x_3637_);
lean_dec(v___x_3637_);
if (v___x_3638_ == 0)
{
lean_object* v___x_3639_; 
lean_dec(v___y_3623_);
lean_dec_ref(v___x_3621_);
v___x_3639_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3635_);
return v___x_3639_;
}
else
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3640_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3);
v___x_3641_ = lean_array_to_list(v___x_3621_);
v___x_3642_ = lean_box(0);
v___x_3643_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(v___x_3641_, v___x_3642_);
v___x_3644_ = l_Lean_MessageData_ofList(v___x_3643_);
v___x_3645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3640_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v___y_3623_, v___x_3645_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3635_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v___x_3647_; 
lean_dec_ref_known(v___x_3646_, 1);
v___x_3647_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3635_);
return v___x_3647_;
}
else
{
return v___x_3646_;
}
}
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec(v_a_3614_);
lean_dec_ref(v_diseqs_3611_);
lean_dec_ref(v_uppers_3610_);
lean_dec_ref(v_lowers_3609_);
lean_dec_ref(v_dvds_3608_);
lean_dec_ref(v_varsHistory_3607_);
lean_dec_ref(v_vars_3606_);
v_a_3733_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3615_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3615_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec_ref(v_diseqs_3611_);
lean_dec_ref(v_uppers_3610_);
lean_dec_ref(v_lowers_3609_);
lean_dec_ref(v_dvds_3608_);
lean_dec_ref(v_varsHistory_3607_);
lean_dec_ref(v_vars_3606_);
v_a_3741_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3613_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3613_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
else
{
lean_object* v___x_3749_; lean_object* v___x_3751_; 
lean_dec_ref(v_diseqs_3611_);
lean_dec_ref(v_uppers_3610_);
lean_dec_ref(v_lowers_3609_);
lean_dec_ref(v_dvds_3608_);
lean_dec_ref(v_varsHistory_3607_);
lean_dec_ref(v_vars_3606_);
v___x_3749_ = lean_box(0);
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 0, v___x_3749_);
v___x_3751_ = v___x_3604_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
v_a_3754_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3601_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3601_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___boxed(lean_object* v_force_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_){
_start:
{
uint8_t v_force_boxed_3774_; lean_object* v_res_3775_; 
v_force_boxed_3774_ = lean_unbox(v_force_3762_);
v_res_3775_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(v_force_boxed_3774_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
lean_dec_ref(v_a_3769_);
lean_dec(v_a_3768_);
lean_dec_ref(v_a_3767_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec(v_a_3763_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(lean_object* v_00_u03b2_3776_, lean_object* v_00_u03c3_3777_, lean_object* v_pm_3778_, lean_object* v_f_3779_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7___redArg(v_pm_3778_, v_f_3779_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18(lean_object* v_cls_3781_, lean_object* v_msg_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v_cls_3781_, v_msg_3782_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___boxed(lean_object* v_cls_3795_, lean_object* v_msg_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18(v_cls_3795_, v_msg_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec(v___y_3797_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16___redArg(lean_object* v_pm_3809_, lean_object* v_f_3810_){
_start:
{
lean_object* v___x_3811_; 
v___x_3811_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20___redArg(v_f_3810_, v_pm_3809_);
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16(lean_object* v_00_u03b2_3812_, lean_object* v_00_u03c3_3813_, lean_object* v_pm_3814_, lean_object* v_f_3815_){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20___redArg(v_f_3815_, v_pm_3814_);
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20(lean_object* v_00_u03b1_3817_, lean_object* v_00_u03b2_3818_, lean_object* v_00_u03c3_3819_, lean_object* v_f_3820_, lean_object* v_n_3821_){
_start:
{
lean_object* v___x_3822_; 
v___x_3822_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20___redArg(v_f_3820_, v_n_3821_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__33(lean_object* v_00_u03b1_3823_, lean_object* v_00_u03b2_3824_, lean_object* v_00_u03c3_3825_, lean_object* v_f_3826_, size_t v_sz_3827_, size_t v_i_3828_, lean_object* v_bs_3829_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__33___redArg(v_f_3826_, v_sz_3827_, v_i_3828_, v_bs_3829_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__33___boxed(lean_object* v_00_u03b1_3831_, lean_object* v_00_u03b2_3832_, lean_object* v_00_u03c3_3833_, lean_object* v_f_3834_, lean_object* v_sz_3835_, lean_object* v_i_3836_, lean_object* v_bs_3837_){
_start:
{
size_t v_sz_boxed_3838_; size_t v_i_boxed_3839_; lean_object* v_res_3840_; 
v_sz_boxed_3838_ = lean_unbox_usize(v_sz_3835_);
lean_dec(v_sz_3835_);
v_i_boxed_3839_ = lean_unbox_usize(v_i_3836_);
lean_dec(v_i_3836_);
v_res_3840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__33(v_00_u03b1_3831_, v_00_u03b2_3832_, v_00_u03c3_3833_, v_f_3834_, v_sz_boxed_3838_, v_i_boxed_3839_, v_bs_3837_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34(lean_object* v_00_u03b1_3841_, lean_object* v_00_u03b2_3842_, lean_object* v_f_3843_, lean_object* v_as_3844_){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34___redArg(v_f_3843_, v_as_3844_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34___boxed(lean_object* v_00_u03b1_3846_, lean_object* v_00_u03b2_3847_, lean_object* v_f_3848_, lean_object* v_as_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34(v_00_u03b1_3846_, v_00_u03b2_3847_, v_f_3848_, v_as_3849_);
lean_dec_ref(v_as_3849_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34_spec__45(lean_object* v_00_u03b1_3851_, lean_object* v_00_u03b2_3852_, lean_object* v_f_3853_, lean_object* v_as_3854_, lean_object* v_i_3855_, lean_object* v_acc_3856_, lean_object* v_hle_3857_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34_spec__45___redArg(v_f_3853_, v_as_3854_, v_i_3855_, v_acc_3856_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34_spec__45___boxed(lean_object* v_00_u03b1_3859_, lean_object* v_00_u03b2_3860_, lean_object* v_f_3861_, lean_object* v_as_3862_, lean_object* v_i_3863_, lean_object* v_acc_3864_, lean_object* v_hle_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__20_spec__34_spec__45(v_00_u03b1_3859_, v_00_u03b2_3860_, v_f_3861_, v_as_3862_, v_i_3863_, v_acc_3864_, v_hle_3865_);
lean_dec_ref(v_as_3862_);
return v_res_3866_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(builtin);
}
#ifdef __cplusplus
}
#endif
