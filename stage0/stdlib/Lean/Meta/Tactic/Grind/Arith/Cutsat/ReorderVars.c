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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default___redArg();
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_norm(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_norm(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Internal_Linear_instBEqPoly_beq(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_v_16_; lean_object* v_maxLowerCoeff_17_; lean_object* v_maxUpperCoeff_18_; lean_object* v_maxDvdCoeff_19_; lean_object* v_minCoeff_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_32_; 
v_v_16_ = lean_array_fget(v_a_7_, v_x_6_);
v_maxLowerCoeff_17_ = lean_ctor_get(v_v_16_, 0);
v_maxUpperCoeff_18_ = lean_ctor_get(v_v_16_, 1);
v_maxDvdCoeff_19_ = lean_ctor_get(v_v_16_, 2);
v_minCoeff_20_ = lean_ctor_get(v_v_16_, 3);
v_isSharedCheck_32_ = !lean_is_exclusive(v_v_16_);
if (v_isSharedCheck_32_ == 0)
{
v___x_22_ = v_v_16_;
v_isShared_23_ = v_isSharedCheck_32_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_minCoeff_20_);
lean_inc(v_maxDvdCoeff_19_);
lean_inc(v_maxUpperCoeff_18_);
lean_inc(v_maxLowerCoeff_17_);
lean_dec(v_v_16_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_32_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v_xs_x27_24_; lean_object* v___y_26_; uint8_t v___x_31_; 
v_xs_x27_24_ = lean_array_fset(v_a_7_, v_x_6_, v___x_9_);
v___x_31_ = lean_nat_dec_le(v_a_5_, v_maxLowerCoeff_17_);
if (v___x_31_ == 0)
{
lean_dec(v_maxLowerCoeff_17_);
v___y_26_ = v_a_5_;
goto v___jp_25_;
}
else
{
lean_dec(v_a_5_);
v___y_26_ = v_maxLowerCoeff_17_;
goto v___jp_25_;
}
v___jp_25_:
{
lean_object* v___x_28_; 
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v___y_26_);
v___x_28_ = v___x_22_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v___y_26_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v_maxUpperCoeff_18_);
lean_ctor_set(v_reuseFailAlloc_30_, 2, v_maxDvdCoeff_19_);
lean_ctor_set(v_reuseFailAlloc_30_, 3, v_minCoeff_20_);
v___x_28_ = v_reuseFailAlloc_30_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_object* v___x_29_; 
v___x_29_ = lean_array_fset(v_xs_x27_24_, v_x_6_, v___x_28_);
v___y_11_ = v___x_29_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg___boxed(lean_object* v_a_33_, lean_object* v_x_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v_a_33_, v_x_34_, v_a_35_);
lean_dec(v_x_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(lean_object* v_a_38_, lean_object* v_x_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v_a_38_, v_x_39_, v_a_40_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___boxed(lean_object* v_a_53_, lean_object* v_x_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(v_a_53_, v_x_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
lean_dec(v_a_57_);
lean_dec(v_a_56_);
lean_dec(v_x_54_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(lean_object* v_a_68_, lean_object* v_x_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_72_; lean_object* v___y_74_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_72_ = lean_box(0);
v___x_77_ = lean_array_get_size(v_a_70_);
v___x_78_ = lean_nat_dec_lt(v_x_69_, v___x_77_);
if (v___x_78_ == 0)
{
lean_dec(v_a_68_);
v___y_74_ = v_a_70_;
goto v___jp_73_;
}
else
{
lean_object* v_v_79_; lean_object* v_maxLowerCoeff_80_; lean_object* v_maxUpperCoeff_81_; lean_object* v_maxDvdCoeff_82_; lean_object* v_minCoeff_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_95_; 
v_v_79_ = lean_array_fget(v_a_70_, v_x_69_);
v_maxLowerCoeff_80_ = lean_ctor_get(v_v_79_, 0);
v_maxUpperCoeff_81_ = lean_ctor_get(v_v_79_, 1);
v_maxDvdCoeff_82_ = lean_ctor_get(v_v_79_, 2);
v_minCoeff_83_ = lean_ctor_get(v_v_79_, 3);
v_isSharedCheck_95_ = !lean_is_exclusive(v_v_79_);
if (v_isSharedCheck_95_ == 0)
{
v___x_85_ = v_v_79_;
v_isShared_86_ = v_isSharedCheck_95_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_minCoeff_83_);
lean_inc(v_maxDvdCoeff_82_);
lean_inc(v_maxUpperCoeff_81_);
lean_inc(v_maxLowerCoeff_80_);
lean_dec(v_v_79_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_95_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v_xs_x27_87_; lean_object* v___y_89_; uint8_t v___x_94_; 
v_xs_x27_87_ = lean_array_fset(v_a_70_, v_x_69_, v___x_72_);
v___x_94_ = lean_nat_dec_le(v_a_68_, v_maxUpperCoeff_81_);
if (v___x_94_ == 0)
{
lean_dec(v_maxUpperCoeff_81_);
v___y_89_ = v_a_68_;
goto v___jp_88_;
}
else
{
lean_dec(v_a_68_);
v___y_89_ = v_maxUpperCoeff_81_;
goto v___jp_88_;
}
v___jp_88_:
{
lean_object* v___x_91_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 1, v___y_89_);
v___x_91_ = v___x_85_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_maxLowerCoeff_80_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v___y_89_);
lean_ctor_set(v_reuseFailAlloc_93_, 2, v_maxDvdCoeff_82_);
lean_ctor_set(v_reuseFailAlloc_93_, 3, v_minCoeff_83_);
v___x_91_ = v_reuseFailAlloc_93_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_92_; 
v___x_92_ = lean_array_fset(v_xs_x27_87_, v_x_69_, v___x_91_);
v___y_74_ = v___x_92_;
goto v___jp_73_;
}
}
}
}
v___jp_73_:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_72_);
lean_ctor_set(v___x_75_, 1, v___y_74_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg___boxed(lean_object* v_a_96_, lean_object* v_x_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_96_, v_x_97_, v_a_98_);
lean_dec(v_x_97_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(lean_object* v_a_101_, lean_object* v_x_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_101_, v_x_102_, v_a_103_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___boxed(lean_object* v_a_116_, lean_object* v_x_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(v_a_116_, v_x_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec(v_a_119_);
lean_dec(v_x_117_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin___redArg(lean_object* v_a_131_, lean_object* v_x_132_, lean_object* v_a_133_){
_start:
{
lean_object* v___x_135_; lean_object* v___y_137_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_135_ = lean_box(0);
v___x_140_ = lean_array_get_size(v_a_133_);
v___x_141_ = lean_nat_dec_lt(v_x_132_, v___x_140_);
if (v___x_141_ == 0)
{
lean_dec(v_a_131_);
v___y_137_ = v_a_133_;
goto v___jp_136_;
}
else
{
lean_object* v_v_142_; lean_object* v_maxLowerCoeff_143_; lean_object* v_maxUpperCoeff_144_; lean_object* v_maxDvdCoeff_145_; lean_object* v_minCoeff_146_; lean_object* v_xs_x27_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v_v_142_ = lean_array_fget(v_a_133_, v_x_132_);
v_maxLowerCoeff_143_ = lean_ctor_get(v_v_142_, 0);
v_maxUpperCoeff_144_ = lean_ctor_get(v_v_142_, 1);
v_maxDvdCoeff_145_ = lean_ctor_get(v_v_142_, 2);
v_minCoeff_146_ = lean_ctor_get(v_v_142_, 3);
v_xs_x27_147_ = lean_array_fset(v_a_133_, v_x_132_, v___x_135_);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = lean_nat_dec_eq(v_minCoeff_146_, v___x_148_);
if (v___x_149_ == 0)
{
uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_le(v_a_131_, v_minCoeff_146_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
lean_dec(v_a_131_);
v___x_151_ = lean_array_fset(v_xs_x27_147_, v_x_132_, v_v_142_);
v___y_137_ = v___x_151_;
goto v___jp_136_;
}
else
{
lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_159_; 
lean_inc(v_maxDvdCoeff_145_);
lean_inc(v_maxUpperCoeff_144_);
lean_inc(v_maxLowerCoeff_143_);
v_isSharedCheck_159_ = !lean_is_exclusive(v_v_142_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; lean_object* v_unused_161_; lean_object* v_unused_162_; lean_object* v_unused_163_; 
v_unused_160_ = lean_ctor_get(v_v_142_, 3);
lean_dec(v_unused_160_);
v_unused_161_ = lean_ctor_get(v_v_142_, 2);
lean_dec(v_unused_161_);
v_unused_162_ = lean_ctor_get(v_v_142_, 1);
lean_dec(v_unused_162_);
v_unused_163_ = lean_ctor_get(v_v_142_, 0);
lean_dec(v_unused_163_);
v___x_153_ = v_v_142_;
v_isShared_154_ = v_isSharedCheck_159_;
goto v_resetjp_152_;
}
else
{
lean_dec(v_v_142_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_159_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 3, v_a_131_);
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_maxLowerCoeff_143_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_maxUpperCoeff_144_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v_maxDvdCoeff_145_);
lean_ctor_set(v_reuseFailAlloc_158_, 3, v_a_131_);
v___x_156_ = v_reuseFailAlloc_158_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; 
v___x_157_ = lean_array_fset(v_xs_x27_147_, v_x_132_, v___x_156_);
v___y_137_ = v___x_157_;
goto v___jp_136_;
}
}
}
}
else
{
lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_171_; 
lean_inc(v_maxDvdCoeff_145_);
lean_inc(v_maxUpperCoeff_144_);
lean_inc(v_maxLowerCoeff_143_);
v_isSharedCheck_171_ = !lean_is_exclusive(v_v_142_);
if (v_isSharedCheck_171_ == 0)
{
lean_object* v_unused_172_; lean_object* v_unused_173_; lean_object* v_unused_174_; lean_object* v_unused_175_; 
v_unused_172_ = lean_ctor_get(v_v_142_, 3);
lean_dec(v_unused_172_);
v_unused_173_ = lean_ctor_get(v_v_142_, 2);
lean_dec(v_unused_173_);
v_unused_174_ = lean_ctor_get(v_v_142_, 1);
lean_dec(v_unused_174_);
v_unused_175_ = lean_ctor_get(v_v_142_, 0);
lean_dec(v_unused_175_);
v___x_165_ = v_v_142_;
v_isShared_166_ = v_isSharedCheck_171_;
goto v_resetjp_164_;
}
else
{
lean_dec(v_v_142_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_171_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 3, v_a_131_);
v___x_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_maxLowerCoeff_143_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_maxUpperCoeff_144_);
lean_ctor_set(v_reuseFailAlloc_170_, 2, v_maxDvdCoeff_145_);
lean_ctor_set(v_reuseFailAlloc_170_, 3, v_a_131_);
v___x_168_ = v_reuseFailAlloc_170_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_169_; 
v___x_169_ = lean_array_fset(v_xs_x27_147_, v_x_132_, v___x_168_);
v___y_137_ = v___x_169_;
goto v___jp_136_;
}
}
}
}
v___jp_136_:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_135_);
lean_ctor_set(v___x_138_, 1, v___y_137_);
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin___redArg___boxed(lean_object* v_a_176_, lean_object* v_x_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin___redArg(v_a_176_, v_x_177_, v_a_178_);
lean_dec(v_x_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin(lean_object* v_a_181_, lean_object* v_x_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin___redArg(v_a_181_, v_x_182_, v_a_183_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin___boxed(lean_object* v_a_196_, lean_object* v_x_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin(v_a_196_, v_x_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
lean_dec(v_a_199_);
lean_dec(v_x_197_);
return v_res_210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_nat_to_int(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(lean_object* v_a_213_, lean_object* v_x_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v_a_219_; lean_object* v_snd_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_217_ = lean_nat_abs(v_a_213_);
lean_inc(v___x_217_);
v___x_218_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateMin___redArg(v___x_217_, v_x_214_, v_a_215_);
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref(v___x_218_);
v_snd_220_ = lean_ctor_get(v_a_219_, 1);
lean_inc(v_snd_220_);
lean_dec(v_a_219_);
v___x_221_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0);
v___x_222_ = lean_int_dec_lt(v_a_213_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
v___x_223_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v___x_217_, v_x_214_, v_snd_220_);
return v___x_223_;
}
else
{
lean_object* v___x_224_; 
v___x_224_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v___x_217_, v_x_214_, v_snd_220_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___boxed(lean_object* v_a_225_, lean_object* v_x_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_225_, v_x_226_, v_a_227_);
lean_dec(v_x_226_);
lean_dec(v_a_225_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(lean_object* v_a_230_, lean_object* v_x_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_230_, v_x_231_, v_a_232_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___boxed(lean_object* v_a_245_, lean_object* v_x_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(v_a_245_, v_x_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec(v_a_248_);
lean_dec(v_x_246_);
lean_dec(v_a_245_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(lean_object* v_a_260_, lean_object* v_x_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_264_; lean_object* v___y_266_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_264_ = lean_box(0);
v___x_269_ = lean_array_get_size(v_a_262_);
v___x_270_ = lean_nat_dec_lt(v_x_261_, v___x_269_);
if (v___x_270_ == 0)
{
lean_dec(v_a_260_);
v___y_266_ = v_a_262_;
goto v___jp_265_;
}
else
{
lean_object* v_v_271_; lean_object* v_maxLowerCoeff_272_; lean_object* v_maxUpperCoeff_273_; lean_object* v_maxDvdCoeff_274_; lean_object* v_minCoeff_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_287_; 
v_v_271_ = lean_array_fget(v_a_262_, v_x_261_);
v_maxLowerCoeff_272_ = lean_ctor_get(v_v_271_, 0);
v_maxUpperCoeff_273_ = lean_ctor_get(v_v_271_, 1);
v_maxDvdCoeff_274_ = lean_ctor_get(v_v_271_, 2);
v_minCoeff_275_ = lean_ctor_get(v_v_271_, 3);
v_isSharedCheck_287_ = !lean_is_exclusive(v_v_271_);
if (v_isSharedCheck_287_ == 0)
{
v___x_277_ = v_v_271_;
v_isShared_278_ = v_isSharedCheck_287_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_minCoeff_275_);
lean_inc(v_maxDvdCoeff_274_);
lean_inc(v_maxUpperCoeff_273_);
lean_inc(v_maxLowerCoeff_272_);
lean_dec(v_v_271_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_287_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v_xs_x27_279_; lean_object* v___y_281_; uint8_t v___x_286_; 
v_xs_x27_279_ = lean_array_fset(v_a_262_, v_x_261_, v___x_264_);
v___x_286_ = lean_nat_dec_le(v_a_260_, v_maxDvdCoeff_274_);
if (v___x_286_ == 0)
{
lean_dec(v_maxDvdCoeff_274_);
v___y_281_ = v_a_260_;
goto v___jp_280_;
}
else
{
lean_dec(v_a_260_);
v___y_281_ = v_maxDvdCoeff_274_;
goto v___jp_280_;
}
v___jp_280_:
{
lean_object* v___x_283_; 
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 2, v___y_281_);
v___x_283_ = v___x_277_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_maxLowerCoeff_272_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_maxUpperCoeff_273_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v___y_281_);
lean_ctor_set(v_reuseFailAlloc_285_, 3, v_minCoeff_275_);
v___x_283_ = v_reuseFailAlloc_285_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; 
v___x_284_ = lean_array_fset(v_xs_x27_279_, v_x_261_, v___x_283_);
v___y_266_ = v___x_284_;
goto v___jp_265_;
}
}
}
}
v___jp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_264_);
lean_ctor_set(v___x_267_, 1, v___y_266_);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg___boxed(lean_object* v_a_288_, lean_object* v_x_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_288_, v_x_289_, v_a_290_);
lean_dec(v_x_289_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(lean_object* v_a_293_, lean_object* v_x_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_293_, v_x_294_, v_a_295_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___boxed(lean_object* v_a_308_, lean_object* v_x_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(v_a_308_, v_x_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec(v_a_311_);
lean_dec(v_x_309_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
if (lean_obj_tag(v_a_323_) == 0)
{
lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_334_; 
v_isSharedCheck_334_ = !lean_is_exclusive(v_a_323_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v_a_323_, 0);
lean_dec(v_unused_335_);
v___x_327_ = v_a_323_;
v_isShared_328_ = v_isSharedCheck_334_;
goto v_resetjp_326_;
}
else
{
lean_dec(v_a_323_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_334_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_329_ = lean_box(0);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v_a_324_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_330_);
v___x_332_ = v___x_327_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
else
{
lean_object* v_k_336_; lean_object* v_v_337_; lean_object* v_p_338_; lean_object* v___x_339_; lean_object* v_a_340_; lean_object* v_snd_341_; 
v_k_336_ = lean_ctor_get(v_a_323_, 0);
lean_inc(v_k_336_);
v_v_337_ = lean_ctor_get(v_a_323_, 1);
lean_inc(v_v_337_);
v_p_338_ = lean_ctor_get(v_a_323_, 2);
lean_inc_ref(v_p_338_);
lean_dec_ref_known(v_a_323_, 3);
v___x_339_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_k_336_, v_v_337_, v_a_324_);
lean_dec(v_v_337_);
lean_dec(v_k_336_);
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref(v___x_339_);
v_snd_341_ = lean_ctor_get(v_a_340_, 1);
lean_inc(v_snd_341_);
lean_dec(v_a_340_);
v_a_323_ = v_p_338_;
v_a_324_ = v_snd_341_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg___boxed(lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_343_, v_a_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_347_, v_a_348_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___boxed(lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec(v_a_363_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(lean_object* v_as_378_, size_t v_sz_379_, size_t v_i_380_, lean_object* v_b_381_, lean_object* v___y_382_){
_start:
{
uint8_t v___x_384_; 
v___x_384_ = lean_usize_dec_lt(v_i_380_, v_sz_379_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_b_381_);
lean_ctor_set(v___x_385_, 1, v___y_382_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
else
{
lean_object* v_a_387_; lean_object* v_p_388_; lean_object* v___x_389_; 
lean_dec_ref(v_b_381_);
v_a_387_ = lean_array_uget_borrowed(v_as_378_, v_i_380_);
v_p_388_ = lean_ctor_get(v_a_387_, 0);
lean_inc_ref(v_p_388_);
v___x_389_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_388_, v___y_382_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; lean_object* v_snd_391_; lean_object* v___x_392_; size_t v___x_393_; size_t v___x_394_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_a_390_);
lean_dec_ref_known(v___x_389_, 1);
v_snd_391_ = lean_ctor_get(v_a_390_, 1);
lean_inc(v_snd_391_);
lean_dec(v_a_390_);
v___x_392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_393_ = ((size_t)1ULL);
v___x_394_ = lean_usize_add(v_i_380_, v___x_393_);
v_i_380_ = v___x_394_;
v_b_381_ = v___x_392_;
v___y_382_ = v_snd_391_;
goto _start;
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
v_a_396_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_389_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_389_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_as_404_, lean_object* v_sz_405_, lean_object* v_i_406_, lean_object* v_b_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
size_t v_sz_boxed_410_; size_t v_i_boxed_411_; lean_object* v_res_412_; 
v_sz_boxed_410_ = lean_unbox_usize(v_sz_405_);
lean_dec(v_sz_405_);
v_i_boxed_411_ = lean_unbox_usize(v_i_406_);
lean_dec(v_i_406_);
v_res_412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_404_, v_sz_boxed_410_, v_i_boxed_411_, v_b_407_, v___y_408_);
lean_dec_ref(v_as_404_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(lean_object* v_as_413_, size_t v_sz_414_, size_t v_i_415_, lean_object* v_b_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
uint8_t v___x_429_; 
v___x_429_ = lean_usize_dec_lt(v_i_415_, v_sz_414_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v_b_416_);
lean_ctor_set(v___x_430_, 1, v___y_417_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
else
{
lean_object* v_a_432_; lean_object* v_p_433_; lean_object* v___x_434_; 
lean_dec_ref(v_b_416_);
v_a_432_ = lean_array_uget_borrowed(v_as_413_, v_i_415_);
v_p_433_ = lean_ctor_get(v_a_432_, 0);
lean_inc_ref(v_p_433_);
v___x_434_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_433_, v___y_417_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v_snd_436_; lean_object* v___x_437_; size_t v___x_438_; size_t v___x_439_; lean_object* v___x_440_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_434_, 1);
v_snd_436_ = lean_ctor_get(v_a_435_, 1);
lean_inc(v_snd_436_);
lean_dec(v_a_435_);
v___x_437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_438_ = ((size_t)1ULL);
v___x_439_ = lean_usize_add(v_i_415_, v___x_438_);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_413_, v_sz_414_, v___x_439_, v___x_437_, v_snd_436_);
return v___x_440_;
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_a_441_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_434_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_434_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1___boxed(lean_object* v_as_449_, lean_object* v_sz_450_, lean_object* v_i_451_, lean_object* v_b_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
size_t v_sz_boxed_465_; size_t v_i_boxed_466_; lean_object* v_res_467_; 
v_sz_boxed_465_ = lean_unbox_usize(v_sz_450_);
lean_dec(v_sz_450_);
v_i_boxed_466_ = lean_unbox_usize(v_i_451_);
lean_dec(v_i_451_);
v_res_467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_as_449_, v_sz_boxed_465_, v_i_boxed_466_, v_b_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v_as_449_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_as_471_, size_t v_sz_472_, size_t v_i_473_, lean_object* v_b_474_, lean_object* v___y_475_){
_start:
{
uint8_t v___x_477_; 
v___x_477_ = lean_usize_dec_lt(v_i_473_, v_sz_472_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v_b_474_);
lean_ctor_set(v___x_478_, 1, v___y_475_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
else
{
lean_object* v_a_480_; lean_object* v_p_481_; lean_object* v___x_482_; 
lean_dec_ref(v_b_474_);
v_a_480_ = lean_array_uget_borrowed(v_as_471_, v_i_473_);
v_p_481_ = lean_ctor_get(v_a_480_, 0);
lean_inc_ref(v_p_481_);
v___x_482_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_481_, v___y_475_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v_snd_484_; lean_object* v___x_485_; size_t v___x_486_; size_t v___x_487_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
v_snd_484_ = lean_ctor_get(v_a_483_, 1);
lean_inc(v_snd_484_);
lean_dec(v_a_483_);
v___x_485_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0));
v___x_486_ = ((size_t)1ULL);
v___x_487_ = lean_usize_add(v_i_473_, v___x_486_);
v_i_473_ = v___x_487_;
v_b_474_ = v___x_485_;
v___y_475_ = v_snd_484_;
goto _start;
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
v_a_489_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_482_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_482_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_as_497_, lean_object* v_sz_498_, lean_object* v_i_499_, lean_object* v_b_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
size_t v_sz_boxed_503_; size_t v_i_boxed_504_; lean_object* v_res_505_; 
v_sz_boxed_503_ = lean_unbox_usize(v_sz_498_);
lean_dec(v_sz_498_);
v_i_boxed_504_ = lean_unbox_usize(v_i_499_);
lean_dec(v_i_499_);
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_497_, v_sz_boxed_503_, v_i_boxed_504_, v_b_500_, v___y_501_);
lean_dec_ref(v_as_497_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(lean_object* v_as_506_, size_t v_sz_507_, size_t v_i_508_, lean_object* v_b_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
uint8_t v___x_522_; 
v___x_522_ = lean_usize_dec_lt(v_i_508_, v_sz_507_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v_b_509_);
lean_ctor_set(v___x_523_, 1, v___y_510_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
else
{
lean_object* v_a_525_; lean_object* v_p_526_; lean_object* v___x_527_; 
lean_dec_ref(v_b_509_);
v_a_525_ = lean_array_uget_borrowed(v_as_506_, v_i_508_);
v_p_526_ = lean_ctor_get(v_a_525_, 0);
lean_inc_ref(v_p_526_);
v___x_527_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_526_, v___y_510_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v_snd_529_; lean_object* v___x_530_; size_t v___x_531_; size_t v___x_532_; lean_object* v___x_533_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v___x_527_, 1);
v_snd_529_ = lean_ctor_get(v_a_528_, 1);
lean_inc(v_snd_529_);
lean_dec(v_a_528_);
v___x_530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0));
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_add(v_i_508_, v___x_531_);
v___x_533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_506_, v_sz_507_, v___x_532_, v___x_530_, v_snd_529_);
return v___x_533_;
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
v_a_534_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_527_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_527_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2___boxed(lean_object* v_as_542_, lean_object* v_sz_543_, lean_object* v_i_544_, lean_object* v_b_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
size_t v_sz_boxed_558_; size_t v_i_boxed_559_; lean_object* v_res_560_; 
v_sz_boxed_558_ = lean_unbox_usize(v_sz_543_);
lean_dec(v_sz_543_);
v_i_boxed_559_ = lean_unbox_usize(v_i_544_);
lean_dec(v_i_544_);
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_as_542_, v_sz_boxed_558_, v_i_boxed_559_, v_b_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v_as_542_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(lean_object* v_init_561_, lean_object* v_n_562_, lean_object* v_b_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
if (lean_obj_tag(v_n_562_) == 0)
{
lean_object* v_cs_576_; lean_object* v___x_577_; lean_object* v___x_578_; size_t v_sz_579_; size_t v___x_580_; lean_object* v___x_581_; 
v_cs_576_ = lean_ctor_get(v_n_562_, 0);
v___x_577_ = lean_box(0);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v_b_563_);
v_sz_579_ = lean_array_size(v_cs_576_);
v___x_580_ = ((size_t)0ULL);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_561_, v_cs_576_, v_sz_579_, v___x_580_, v___x_578_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_616_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_616_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_616_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_616_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v_fst_586_; lean_object* v_fst_587_; 
v_fst_586_ = lean_ctor_get(v_a_582_, 0);
lean_inc(v_fst_586_);
v_fst_587_ = lean_ctor_get(v_fst_586_, 0);
if (lean_obj_tag(v_fst_587_) == 0)
{
lean_object* v_snd_588_; lean_object* v_snd_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_600_; 
v_snd_588_ = lean_ctor_get(v_a_582_, 1);
lean_inc(v_snd_588_);
lean_dec(v_a_582_);
v_snd_589_ = lean_ctor_get(v_fst_586_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_fst_586_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; 
v_unused_601_ = lean_ctor_get(v_fst_586_, 0);
lean_dec(v_unused_601_);
v___x_591_ = v_fst_586_;
v_isShared_592_ = v_isSharedCheck_600_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_snd_589_);
lean_dec(v_fst_586_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_600_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v_snd_589_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v_snd_588_);
lean_ctor_set(v___x_591_, 0, v___x_593_);
v___x_595_ = v___x_591_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_snd_588_);
v___x_595_ = v_reuseFailAlloc_599_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_597_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_595_);
v___x_597_ = v___x_584_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
else
{
lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_613_; 
lean_inc_ref(v_fst_587_);
v_isSharedCheck_613_ = !lean_is_exclusive(v_fst_586_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; lean_object* v_unused_615_; 
v_unused_614_ = lean_ctor_get(v_fst_586_, 1);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_fst_586_, 0);
lean_dec(v_unused_615_);
v___x_603_ = v_fst_586_;
v_isShared_604_ = v_isSharedCheck_613_;
goto v_resetjp_602_;
}
else
{
lean_dec(v_fst_586_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_613_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v_snd_605_; lean_object* v_val_606_; lean_object* v___x_608_; 
v_snd_605_ = lean_ctor_get(v_a_582_, 1);
lean_inc(v_snd_605_);
lean_dec(v_a_582_);
v_val_606_ = lean_ctor_get(v_fst_587_, 0);
lean_inc(v_val_606_);
lean_dec_ref_known(v_fst_587_, 1);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 1, v_snd_605_);
lean_ctor_set(v___x_603_, 0, v_val_606_);
v___x_608_ = v___x_603_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_val_606_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_snd_605_);
v___x_608_ = v_reuseFailAlloc_612_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_610_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_608_);
v___x_610_ = v___x_584_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
v_a_617_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_581_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_581_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
else
{
lean_object* v_vs_625_; lean_object* v___x_626_; lean_object* v___x_627_; size_t v_sz_628_; size_t v___x_629_; lean_object* v___x_630_; 
v_vs_625_ = lean_ctor_get(v_n_562_, 0);
v___x_626_ = lean_box(0);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v_b_563_);
v_sz_628_ = lean_array_size(v_vs_625_);
v___x_629_ = ((size_t)0ULL);
v___x_630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_vs_625_, v_sz_628_, v___x_629_, v___x_627_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_665_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_665_ == 0)
{
v___x_633_ = v___x_630_;
v_isShared_634_ = v_isSharedCheck_665_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_665_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v_fst_635_; lean_object* v_fst_636_; 
v_fst_635_ = lean_ctor_get(v_a_631_, 0);
lean_inc(v_fst_635_);
v_fst_636_ = lean_ctor_get(v_fst_635_, 0);
if (lean_obj_tag(v_fst_636_) == 0)
{
lean_object* v_snd_637_; lean_object* v_snd_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_649_; 
v_snd_637_ = lean_ctor_get(v_a_631_, 1);
lean_inc(v_snd_637_);
lean_dec(v_a_631_);
v_snd_638_ = lean_ctor_get(v_fst_635_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v_fst_635_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v_fst_635_, 0);
lean_dec(v_unused_650_);
v___x_640_ = v_fst_635_;
v_isShared_641_ = v_isSharedCheck_649_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_snd_638_);
lean_dec(v_fst_635_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_649_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_642_, 0, v_snd_638_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v_snd_637_);
lean_ctor_set(v___x_640_, 0, v___x_642_);
v___x_644_ = v___x_640_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_snd_637_);
v___x_644_ = v_reuseFailAlloc_648_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_646_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_644_);
v___x_646_ = v___x_633_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
else
{
lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_662_; 
lean_inc_ref(v_fst_636_);
v_isSharedCheck_662_ = !lean_is_exclusive(v_fst_635_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; lean_object* v_unused_664_; 
v_unused_663_ = lean_ctor_get(v_fst_635_, 1);
lean_dec(v_unused_663_);
v_unused_664_ = lean_ctor_get(v_fst_635_, 0);
lean_dec(v_unused_664_);
v___x_652_ = v_fst_635_;
v_isShared_653_ = v_isSharedCheck_662_;
goto v_resetjp_651_;
}
else
{
lean_dec(v_fst_635_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_662_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_snd_654_; lean_object* v_val_655_; lean_object* v___x_657_; 
v_snd_654_ = lean_ctor_get(v_a_631_, 1);
lean_inc(v_snd_654_);
lean_dec(v_a_631_);
v_val_655_ = lean_ctor_get(v_fst_636_, 0);
lean_inc(v_val_655_);
lean_dec_ref_known(v_fst_636_, 1);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v_snd_654_);
lean_ctor_set(v___x_652_, 0, v_val_655_);
v___x_657_ = v___x_652_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_val_655_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_snd_654_);
v___x_657_ = v_reuseFailAlloc_661_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_659_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_657_);
v___x_659_ = v___x_633_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
v_a_666_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_630_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_630_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(lean_object* v_init_674_, lean_object* v_as_675_, size_t v_sz_676_, size_t v_i_677_, lean_object* v_b_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
uint8_t v___x_691_; 
v___x_691_ = lean_usize_dec_lt(v_i_677_, v_sz_676_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_b_678_);
lean_ctor_set(v___x_692_, 1, v___y_679_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
else
{
lean_object* v_snd_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_744_; 
v_snd_694_ = lean_ctor_get(v_b_678_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_b_678_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v_b_678_, 0);
lean_dec(v_unused_745_);
v___x_696_ = v_b_678_;
v_isShared_697_ = v_isSharedCheck_744_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_snd_694_);
lean_dec(v_b_678_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_744_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v_a_699_; lean_object* v___x_700_; 
v___x_698_ = lean_box(0);
v_a_699_ = lean_array_uget_borrowed(v_as_675_, v_i_677_);
lean_inc(v_snd_694_);
v___x_700_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_674_, v_a_699_, v_snd_694_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_735_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_735_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_735_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_735_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_fst_705_; 
v_fst_705_ = lean_ctor_get(v_a_701_, 0);
lean_inc(v_fst_705_);
if (lean_obj_tag(v_fst_705_) == 0)
{
lean_object* v_snd_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_720_; 
v_snd_706_ = lean_ctor_get(v_a_701_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_a_701_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v_a_701_, 0);
lean_dec(v_unused_721_);
v___x_708_ = v_a_701_;
v_isShared_709_ = v_isSharedCheck_720_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_snd_706_);
lean_dec(v_a_701_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_720_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_710_, 0, v_fst_705_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v_snd_694_);
lean_ctor_set(v___x_708_, 0, v___x_710_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_snd_694_);
v___x_712_ = v_reuseFailAlloc_719_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v_snd_706_);
lean_ctor_set(v___x_696_, 0, v___x_712_);
v___x_714_ = v___x_696_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_snd_706_);
v___x_714_ = v_reuseFailAlloc_718_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_716_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_714_);
v___x_716_ = v___x_703_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
else
{
lean_object* v_snd_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_733_; 
lean_del_object(v___x_703_);
lean_del_object(v___x_696_);
lean_dec(v_snd_694_);
v_snd_722_ = lean_ctor_get(v_a_701_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v_a_701_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v_a_701_, 0);
lean_dec(v_unused_734_);
v___x_724_ = v_a_701_;
v_isShared_725_ = v_isSharedCheck_733_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_snd_722_);
lean_dec(v_a_701_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_733_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v_a_726_; lean_object* v___x_728_; 
v_a_726_ = lean_ctor_get(v_fst_705_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v_fst_705_, 1);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 1, v_a_726_);
lean_ctor_set(v___x_724_, 0, v___x_698_);
v___x_728_ = v___x_724_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_a_726_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
size_t v___x_729_; size_t v___x_730_; 
v___x_729_ = ((size_t)1ULL);
v___x_730_ = lean_usize_add(v_i_677_, v___x_729_);
v_i_677_ = v___x_730_;
v_b_678_ = v___x_728_;
v___y_679_ = v_snd_722_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_del_object(v___x_696_);
lean_dec(v_snd_694_);
v_a_736_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_700_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_700_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_746_ = _args[0];
lean_object* v_as_747_ = _args[1];
lean_object* v_sz_748_ = _args[2];
lean_object* v_i_749_ = _args[3];
lean_object* v_b_750_ = _args[4];
lean_object* v___y_751_ = _args[5];
lean_object* v___y_752_ = _args[6];
lean_object* v___y_753_ = _args[7];
lean_object* v___y_754_ = _args[8];
lean_object* v___y_755_ = _args[9];
lean_object* v___y_756_ = _args[10];
lean_object* v___y_757_ = _args[11];
lean_object* v___y_758_ = _args[12];
lean_object* v___y_759_ = _args[13];
lean_object* v___y_760_ = _args[14];
lean_object* v___y_761_ = _args[15];
lean_object* v___y_762_ = _args[16];
_start:
{
size_t v_sz_boxed_763_; size_t v_i_boxed_764_; lean_object* v_res_765_; 
v_sz_boxed_763_ = lean_unbox_usize(v_sz_748_);
lean_dec(v_sz_748_);
v_i_boxed_764_ = lean_unbox_usize(v_i_749_);
lean_dec(v_i_749_);
v_res_765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_746_, v_as_747_, v_sz_boxed_763_, v_i_boxed_764_, v_b_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v_as_747_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0___boxed(lean_object* v_init_766_, lean_object* v_n_767_, lean_object* v_b_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_766_, v_n_767_, v_b_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v_n_767_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(lean_object* v_t_782_, lean_object* v_init_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v_b_797_; lean_object* v___y_798_; lean_object* v_root_801_; lean_object* v_tail_802_; lean_object* v___x_803_; 
v_root_801_ = lean_ctor_get(v_t_782_, 0);
v_tail_802_ = lean_ctor_get(v_t_782_, 1);
v___x_803_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_783_, v_root_801_, v_init_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v_fst_805_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
v_fst_805_ = lean_ctor_get(v_a_804_, 0);
lean_inc(v_fst_805_);
if (lean_obj_tag(v_fst_805_) == 0)
{
lean_object* v_snd_806_; lean_object* v_a_807_; 
v_snd_806_ = lean_ctor_get(v_a_804_, 1);
lean_inc(v_snd_806_);
lean_dec(v_a_804_);
v_a_807_ = lean_ctor_get(v_fst_805_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v_fst_805_, 1);
v_b_797_ = v_a_807_;
v___y_798_ = v_snd_806_;
goto v___jp_796_;
}
else
{
lean_object* v_snd_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_850_; 
v_snd_808_ = lean_ctor_get(v_a_804_, 1);
v_isSharedCheck_850_ = !lean_is_exclusive(v_a_804_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v_a_804_, 0);
lean_dec(v_unused_851_);
v___x_810_ = v_a_804_;
v_isShared_811_ = v_isSharedCheck_850_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_snd_808_);
lean_dec(v_a_804_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_850_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v_a_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
v_a_812_ = lean_ctor_get(v_fst_805_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v_fst_805_, 1);
v___x_813_ = lean_box(0);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 1, v_a_812_);
lean_ctor_set(v___x_810_, 0, v___x_813_);
v___x_815_ = v___x_810_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_a_812_);
v___x_815_ = v_reuseFailAlloc_849_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
size_t v_sz_816_; size_t v___x_817_; lean_object* v___x_818_; 
v_sz_816_ = lean_array_size(v_tail_802_);
v___x_817_ = ((size_t)0ULL);
v___x_818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_tail_802_, v_sz_816_, v___x_817_, v___x_815_, v_snd_808_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_840_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_840_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_840_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_840_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v_fst_823_; lean_object* v_fst_824_; 
v_fst_823_ = lean_ctor_get(v_a_819_, 0);
lean_inc(v_fst_823_);
v_fst_824_ = lean_ctor_get(v_fst_823_, 0);
if (lean_obj_tag(v_fst_824_) == 0)
{
lean_object* v_snd_825_; lean_object* v_snd_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_836_; 
v_snd_825_ = lean_ctor_get(v_a_819_, 1);
lean_inc(v_snd_825_);
lean_dec(v_a_819_);
v_snd_826_ = lean_ctor_get(v_fst_823_, 1);
v_isSharedCheck_836_ = !lean_is_exclusive(v_fst_823_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; 
v_unused_837_ = lean_ctor_get(v_fst_823_, 0);
lean_dec(v_unused_837_);
v___x_828_ = v_fst_823_;
v_isShared_829_ = v_isSharedCheck_836_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_snd_826_);
lean_dec(v_fst_823_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_836_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v_snd_825_);
lean_ctor_set(v___x_828_, 0, v_snd_826_);
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_snd_826_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_snd_825_);
v___x_831_ = v_reuseFailAlloc_835_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_833_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_831_);
v___x_833_ = v___x_821_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
else
{
lean_object* v_snd_838_; lean_object* v_val_839_; 
lean_inc_ref(v_fst_824_);
lean_dec(v_fst_823_);
lean_del_object(v___x_821_);
v_snd_838_ = lean_ctor_get(v_a_819_, 1);
lean_inc(v_snd_838_);
lean_dec(v_a_819_);
v_val_839_ = lean_ctor_get(v_fst_824_, 0);
lean_inc(v_val_839_);
lean_dec_ref_known(v_fst_824_, 1);
v_b_797_ = v_val_839_;
v___y_798_ = v_snd_838_;
goto v___jp_796_;
}
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
v_a_841_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_818_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_818_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
v_a_852_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_803_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_803_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
v___jp_796_:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v_b_797_);
lean_ctor_set(v___x_799_, 1, v___y_798_);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0___boxed(lean_object* v_t_860_, lean_object* v_init_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v_t_860_, v_init_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v_t_860_);
return v_res_874_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(lean_object* v_xs_875_, lean_object* v_i_876_){
_start:
{
lean_object* v_size_877_; uint8_t v___x_878_; 
v_size_877_ = lean_ctor_get(v_xs_875_, 2);
v___x_878_ = lean_nat_dec_lt(v_i_876_, v_size_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0___boxed(lean_object* v_xs_879_, lean_object* v_i_880_){
_start:
{
uint8_t v_res_881_; lean_object* v_r_882_; 
v_res_881_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_xs_879_, v_i_880_);
lean_dec(v_i_880_);
lean_dec_ref(v_xs_879_);
v_r_882_ = lean_box(v_res_881_);
return v_r_882_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(lean_object* v_a_884_, lean_object* v_range_885_, lean_object* v_b_886_, lean_object* v_i_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_stop_900_; lean_object* v_step_901_; uint8_t v___x_902_; 
v_stop_900_ = lean_ctor_get(v_range_885_, 1);
v_step_901_ = lean_ctor_get(v_range_885_, 2);
v___x_902_ = lean_nat_dec_lt(v_i_887_, v_stop_900_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
lean_dec(v_i_887_);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v_b_886_);
lean_ctor_set(v___x_903_, 1, v___y_888_);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
else
{
lean_object* v___x_905_; lean_object* v_snd_907_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___x_919_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_905_ = lean_box(0);
v___x_919_ = lean_box(0);
v___x_931_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0);
v___x_932_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_i_887_, v___y_889_, v___y_897_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; uint8_t v___x_934_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
v___x_934_ = lean_unbox(v_a_933_);
lean_dec(v_a_933_);
if (v___x_934_ == 0)
{
lean_object* v_lowers_935_; lean_object* v_uppers_936_; lean_object* v___y_938_; uint8_t v___x_945_; 
v_lowers_935_ = lean_ctor_get(v_a_884_, 6);
v_uppers_936_ = lean_ctor_get(v_a_884_, 7);
v___x_945_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_lowers_935_, v_i_887_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; 
v___x_946_ = l_outOfBounds___redArg(v___x_931_);
v___y_938_ = v___x_946_;
goto v___jp_937_;
}
else
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_PersistentArray_get_x21___redArg(v___x_931_, v_lowers_935_, v_i_887_);
v___y_938_ = v___x_947_;
goto v___jp_937_;
}
v___jp_937_:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v___y_938_, v___x_905_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec_ref(v___y_938_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v_snd_941_; uint8_t v___x_942_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_a_940_);
lean_dec_ref_known(v___x_939_, 1);
v_snd_941_ = lean_ctor_get(v_a_940_, 1);
lean_inc(v_snd_941_);
lean_dec(v_a_940_);
v___x_942_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_uppers_936_, v_i_887_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
v___x_943_ = l_outOfBounds___redArg(v___x_931_);
v___y_921_ = v_snd_941_;
v___y_922_ = v___x_943_;
goto v___jp_920_;
}
else
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_PersistentArray_get_x21___redArg(v___x_931_, v_uppers_936_, v_i_887_);
v___y_921_ = v_snd_941_;
v___y_922_ = v___x_944_;
goto v___jp_920_;
}
}
else
{
lean_dec(v_i_887_);
return v___x_939_;
}
}
}
else
{
v_snd_907_ = v___y_888_;
goto v___jp_906_;
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v___y_888_);
lean_dec(v_i_887_);
v_a_948_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_932_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_932_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
v___jp_906_:
{
lean_object* v___x_908_; 
v___x_908_ = lean_nat_add(v_i_887_, v_step_901_);
lean_dec(v_i_887_);
v_b_886_ = v___x_905_;
v_i_887_ = v___x_908_;
v___y_888_ = v_snd_907_;
goto _start;
}
v___jp_910_:
{
if (lean_obj_tag(v___y_912_) == 1)
{
lean_object* v_val_913_; lean_object* v_d_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v_a_917_; lean_object* v_snd_918_; 
v_val_913_ = lean_ctor_get(v___y_912_, 0);
lean_inc(v_val_913_);
lean_dec_ref_known(v___y_912_, 1);
v_d_914_ = lean_ctor_get(v_val_913_, 0);
lean_inc(v_d_914_);
lean_dec(v_val_913_);
v___x_915_ = lean_nat_abs(v_d_914_);
lean_dec(v_d_914_);
v___x_916_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v___x_915_, v_i_887_, v___y_911_);
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref(v___x_916_);
v_snd_918_ = lean_ctor_get(v_a_917_, 1);
lean_inc(v_snd_918_);
lean_dec(v_a_917_);
v_snd_907_ = v_snd_918_;
goto v___jp_906_;
}
else
{
lean_dec(v___y_912_);
v_snd_907_ = v___y_911_;
goto v___jp_906_;
}
}
v___jp_920_:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v___y_922_, v___x_905_, v___y_921_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec_ref(v___y_922_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v_dvds_925_; lean_object* v_snd_926_; lean_object* v_size_927_; uint8_t v___x_928_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v___x_923_, 1);
v_dvds_925_ = lean_ctor_get(v_a_884_, 5);
v_snd_926_ = lean_ctor_get(v_a_924_, 1);
lean_inc(v_snd_926_);
lean_dec(v_a_924_);
v_size_927_ = lean_ctor_get(v_dvds_925_, 2);
v___x_928_ = lean_nat_dec_lt(v_i_887_, v_size_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
v___x_929_ = l_outOfBounds___redArg(v___x_919_);
v___y_911_ = v_snd_926_;
v___y_912_ = v___x_929_;
goto v___jp_910_;
}
else
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_PersistentArray_get_x21___redArg(v___x_919_, v_dvds_925_, v_i_887_);
v___y_911_ = v_snd_926_;
v___y_912_ = v___x_930_;
goto v___jp_910_;
}
}
else
{
lean_dec(v_i_887_);
return v___x_923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___boxed(lean_object* v_a_956_, lean_object* v_range_957_, lean_object* v_b_958_, lean_object* v_i_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_956_, v_range_957_, v_b_958_, v_i_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v_range_957_);
lean_dec_ref(v_a_956_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_974_, v_a_982_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v_vars_987_; lean_object* v_size_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
v_vars_987_ = lean_ctor_get(v_a_986_, 0);
v_size_988_ = lean_ctor_get(v_vars_987_, 2);
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = lean_unsigned_to_nat(1u);
lean_inc(v_size_988_);
v___x_991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v_size_988_);
lean_ctor_set(v___x_991_, 2, v___x_990_);
v___x_992_ = lean_box(0);
v___x_993_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_986_, v___x_991_, v___x_992_, v___x_989_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
lean_dec_ref_known(v___x_991_, 3);
lean_dec(v_a_986_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1010_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1010_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1010_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_snd_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1008_; 
v_snd_998_ = lean_ctor_get(v_a_994_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_a_994_);
if (v_isSharedCheck_1008_ == 0)
{
lean_object* v_unused_1009_; 
v_unused_1009_ = lean_ctor_get(v_a_994_, 0);
lean_dec(v_unused_1009_);
v___x_1000_ = v_a_994_;
v_isShared_1001_ = v_isSharedCheck_1008_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_snd_998_);
lean_dec(v_a_994_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1008_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_992_);
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_snd_998_);
v___x_1003_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1005_; 
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1003_);
v___x_1005_ = v___x_996_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
else
{
return v___x_993_;
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec_ref(v_a_973_);
v_a_1011_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_985_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_985_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go___boxed(lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec(v_a_1020_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(lean_object* v_a_1032_, lean_object* v_range_1033_, lean_object* v_b_1034_, lean_object* v_i_1035_, lean_object* v_hs_1036_, lean_object* v_hl_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_1032_, v_range_1033_, v_b_1034_, v_i_1035_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___boxed(lean_object** _args){
lean_object* v_a_1051_ = _args[0];
lean_object* v_range_1052_ = _args[1];
lean_object* v_b_1053_ = _args[2];
lean_object* v_i_1054_ = _args[3];
lean_object* v_hs_1055_ = _args[4];
lean_object* v_hl_1056_ = _args[5];
lean_object* v___y_1057_ = _args[6];
lean_object* v___y_1058_ = _args[7];
lean_object* v___y_1059_ = _args[8];
lean_object* v___y_1060_ = _args[9];
lean_object* v___y_1061_ = _args[10];
lean_object* v___y_1062_ = _args[11];
lean_object* v___y_1063_ = _args[12];
lean_object* v___y_1064_ = _args[13];
lean_object* v___y_1065_ = _args[14];
lean_object* v___y_1066_ = _args[15];
lean_object* v___y_1067_ = _args[16];
lean_object* v___y_1068_ = _args[17];
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(v_a_1051_, v_range_1052_, v_b_1053_, v_i_1054_, v_hs_1055_, v_hl_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v_range_1052_);
lean_dec_ref(v_a_1051_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(lean_object* v_as_1070_, size_t v_sz_1071_, size_t v_i_1072_, lean_object* v_b_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_1070_, v_sz_1071_, v_i_1072_, v_b_1073_, v___y_1074_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1087_, lean_object* v_sz_1088_, lean_object* v_i_1089_, lean_object* v_b_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
size_t v_sz_boxed_1103_; size_t v_i_boxed_1104_; lean_object* v_res_1105_; 
v_sz_boxed_1103_ = lean_unbox_usize(v_sz_1088_);
lean_dec(v_sz_1088_);
v_i_boxed_1104_ = lean_unbox_usize(v_i_1089_);
lean_dec(v_i_1089_);
v_res_1105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(v_as_1087_, v_sz_boxed_1103_, v_i_boxed_1104_, v_b_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v_as_1087_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(lean_object* v_as_1106_, size_t v_sz_1107_, size_t v_i_1108_, lean_object* v_b_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1106_, v_sz_1107_, v_i_1108_, v_b_1109_, v___y_1110_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_as_1123_, lean_object* v_sz_1124_, lean_object* v_i_1125_, lean_object* v_b_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
size_t v_sz_boxed_1139_; size_t v_i_boxed_1140_; lean_object* v_res_1141_; 
v_sz_boxed_1139_ = lean_unbox_usize(v_sz_1124_);
lean_dec(v_sz_1124_);
v_i_boxed_1140_ = lean_unbox_usize(v_i_1125_);
lean_dec(v_i_1125_);
v_res_1141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(v_as_1123_, v_sz_boxed_1139_, v_i_boxed_1140_, v_b_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v_as_1123_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1142_, v_a_1150_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v_vars_1155_; lean_object* v_size_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___x_1153_, 1);
v_vars_1155_ = lean_ctor_get(v_a_1154_, 0);
lean_inc_ref(v_vars_1155_);
lean_dec(v_a_1154_);
v_size_1156_ = lean_ctor_get(v_vars_1155_, 2);
lean_inc(v_size_1156_);
lean_dec_ref(v_vars_1155_);
v___x_1157_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0));
v___x_1158_ = lean_mk_array(v_size_1156_, v___x_1157_);
v___x_1159_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v___x_1158_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1168_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1162_ = v___x_1159_;
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1159_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v_snd_1164_; lean_object* v___x_1166_; 
v_snd_1164_ = lean_ctor_get(v_a_1160_, 1);
lean_inc(v_snd_1164_);
lean_dec(v_a_1160_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v_snd_1164_);
v___x_1166_ = v___x_1162_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_snd_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
v_a_1169_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1159_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1159_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
v_a_1177_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1153_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1153_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo___boxed(lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec(v_a_1185_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(lean_object* v_info_1197_){
_start:
{
lean_object* v_maxLowerCoeff_1198_; lean_object* v_maxUpperCoeff_1199_; lean_object* v_maxDvdCoeff_1200_; lean_object* v___y_1202_; uint8_t v___x_1204_; 
v_maxLowerCoeff_1198_ = lean_ctor_get(v_info_1197_, 0);
v_maxUpperCoeff_1199_ = lean_ctor_get(v_info_1197_, 1);
v_maxDvdCoeff_1200_ = lean_ctor_get(v_info_1197_, 2);
v___x_1204_ = lean_nat_dec_le(v_maxLowerCoeff_1198_, v_maxUpperCoeff_1199_);
if (v___x_1204_ == 0)
{
v___y_1202_ = v_maxUpperCoeff_1199_;
goto v___jp_1201_;
}
else
{
v___y_1202_ = v_maxLowerCoeff_1198_;
goto v___jp_1201_;
}
v___jp_1201_:
{
uint8_t v___x_1203_; 
v___x_1203_ = lean_nat_dec_le(v_maxDvdCoeff_1200_, v___y_1202_);
if (v___x_1203_ == 0)
{
lean_inc(v_maxDvdCoeff_1200_);
return v_maxDvdCoeff_1200_;
}
else
{
lean_inc(v___y_1202_);
return v___y_1202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081___boxed(lean_object* v_info_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v_info_1205_);
lean_dec_ref(v_info_1205_);
return v_res_1206_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(lean_object* v_infos_1207_, lean_object* v_x_1208_, lean_object* v_y_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1210_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1211_ = lean_array_get_borrowed(v___x_1210_, v_infos_1207_, v_x_1208_);
v___x_1212_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_1211_);
v___x_1213_ = lean_array_get_borrowed(v___x_1210_, v_infos_1207_, v_y_1209_);
v___x_1214_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_1213_);
v___x_1215_ = lean_nat_dec_lt(v___x_1212_, v___x_1214_);
if (v___x_1215_ == 0)
{
uint8_t v___x_1216_; 
v___x_1216_ = lean_nat_dec_eq(v___x_1212_, v___x_1214_);
lean_dec(v___x_1214_);
lean_dec(v___x_1212_);
if (v___x_1216_ == 0)
{
uint8_t v___x_1217_; 
v___x_1217_ = 0;
return v___x_1217_;
}
else
{
uint8_t v___x_1218_; 
v___x_1218_ = 1;
return v___x_1218_;
}
}
else
{
uint8_t v___x_1219_; 
lean_dec(v___x_1214_);
lean_dec(v___x_1212_);
v___x_1219_ = 2;
return v___x_1219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081___boxed(lean_object* v_infos_1220_, lean_object* v_x_1221_, lean_object* v_y_1222_){
_start:
{
uint8_t v_res_1223_; lean_object* v_r_1224_; 
v_res_1223_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_1220_, v_x_1221_, v_y_1222_);
lean_dec(v_y_1222_);
lean_dec(v_x_1221_);
lean_dec_ref(v_infos_1220_);
v_r_1224_ = lean_box(v_res_1223_);
return v_r_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(lean_object* v_info_1225_){
_start:
{
lean_object* v_maxLowerCoeff_1226_; lean_object* v_maxUpperCoeff_1227_; lean_object* v_maxDvdCoeff_1228_; lean_object* v___y_1230_; uint8_t v___x_1232_; 
v_maxLowerCoeff_1226_ = lean_ctor_get(v_info_1225_, 0);
v_maxUpperCoeff_1227_ = lean_ctor_get(v_info_1225_, 1);
v_maxDvdCoeff_1228_ = lean_ctor_get(v_info_1225_, 2);
v___x_1232_ = lean_nat_dec_le(v_maxLowerCoeff_1226_, v_maxUpperCoeff_1227_);
if (v___x_1232_ == 0)
{
v___y_1230_ = v_maxLowerCoeff_1226_;
goto v___jp_1229_;
}
else
{
v___y_1230_ = v_maxUpperCoeff_1227_;
goto v___jp_1229_;
}
v___jp_1229_:
{
uint8_t v___x_1231_; 
v___x_1231_ = lean_nat_dec_le(v_maxDvdCoeff_1228_, v___y_1230_);
if (v___x_1231_ == 0)
{
lean_inc(v_maxDvdCoeff_1228_);
return v_maxDvdCoeff_1228_;
}
else
{
lean_inc(v___y_1230_);
return v___y_1230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082___boxed(lean_object* v_info_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v_info_1233_);
lean_dec_ref(v_info_1233_);
return v_res_1234_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(lean_object* v_infos_1235_, lean_object* v_x_1236_, lean_object* v_y_1237_){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1238_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1239_ = lean_array_get_borrowed(v___x_1238_, v_infos_1235_, v_x_1236_);
v___x_1240_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v___x_1239_);
v___x_1241_ = lean_array_get_borrowed(v___x_1238_, v_infos_1235_, v_y_1237_);
v___x_1242_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v___x_1241_);
v___x_1243_ = lean_nat_dec_lt(v___x_1240_, v___x_1242_);
if (v___x_1243_ == 0)
{
uint8_t v___x_1244_; 
v___x_1244_ = lean_nat_dec_eq(v___x_1240_, v___x_1242_);
lean_dec(v___x_1242_);
lean_dec(v___x_1240_);
if (v___x_1244_ == 0)
{
uint8_t v___x_1245_; 
v___x_1245_ = 0;
return v___x_1245_;
}
else
{
uint8_t v___x_1246_; 
v___x_1246_ = 1;
return v___x_1246_;
}
}
else
{
uint8_t v___x_1247_; 
lean_dec(v___x_1242_);
lean_dec(v___x_1240_);
v___x_1247_ = 2;
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082___boxed(lean_object* v_infos_1248_, lean_object* v_x_1249_, lean_object* v_y_1250_){
_start:
{
uint8_t v_res_1251_; lean_object* v_r_1252_; 
v_res_1251_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_1248_, v_x_1249_, v_y_1250_);
lean_dec(v_y_1250_);
lean_dec(v_x_1249_);
lean_dec_ref(v_infos_1248_);
v_r_1252_ = lean_box(v_res_1251_);
return v_r_1252_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2083(lean_object* v_infos_1253_, lean_object* v_x_1254_, lean_object* v_y_1255_){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v_minCoeff_1258_; lean_object* v___x_1259_; lean_object* v_minCoeff_1260_; uint8_t v___x_1261_; 
v___x_1256_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1257_ = lean_array_get_borrowed(v___x_1256_, v_infos_1253_, v_x_1254_);
v_minCoeff_1258_ = lean_ctor_get(v___x_1257_, 3);
v___x_1259_ = lean_array_get_borrowed(v___x_1256_, v_infos_1253_, v_y_1255_);
v_minCoeff_1260_ = lean_ctor_get(v___x_1259_, 3);
v___x_1261_ = lean_nat_dec_lt(v_minCoeff_1258_, v_minCoeff_1260_);
if (v___x_1261_ == 0)
{
uint8_t v___x_1262_; 
v___x_1262_ = lean_nat_dec_eq(v_minCoeff_1258_, v_minCoeff_1260_);
if (v___x_1262_ == 0)
{
uint8_t v___x_1263_; 
v___x_1263_ = 0;
return v___x_1263_;
}
else
{
uint8_t v___x_1264_; 
v___x_1264_ = 1;
return v___x_1264_;
}
}
else
{
uint8_t v___x_1265_; 
v___x_1265_ = 2;
return v___x_1265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2083___boxed(lean_object* v_infos_1266_, lean_object* v_x_1267_, lean_object* v_y_1268_){
_start:
{
uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_res_1269_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2083(v_infos_1266_, v_x_1267_, v_y_1268_);
lean_dec(v_y_1268_);
lean_dec(v_x_1267_);
lean_dec_ref(v_infos_1266_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(lean_object* v_infos_1271_, lean_object* v_x_1272_, lean_object* v_y_1273_){
_start:
{
uint8_t v___y_1275_; uint8_t v___y_1281_; uint8_t v___x_1283_; 
v___x_1283_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_1271_, v_x_1272_, v_y_1273_);
if (v___x_1283_ == 1)
{
uint8_t v___x_1284_; 
v___x_1284_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_1271_, v_x_1272_, v_y_1273_);
v___y_1281_ = v___x_1284_;
goto v___jp_1280_;
}
else
{
v___y_1281_ = v___x_1283_;
goto v___jp_1280_;
}
v___jp_1274_:
{
if (v___y_1275_ == 1)
{
uint8_t v___x_1276_; 
v___x_1276_ = lean_nat_dec_lt(v_x_1272_, v_y_1273_);
if (v___x_1276_ == 0)
{
uint8_t v___x_1277_; 
v___x_1277_ = lean_nat_dec_eq(v_x_1272_, v_y_1273_);
if (v___x_1277_ == 0)
{
uint8_t v___x_1278_; 
v___x_1278_ = 2;
return v___x_1278_;
}
else
{
return v___y_1275_;
}
}
else
{
uint8_t v___x_1279_; 
v___x_1279_ = 0;
return v___x_1279_;
}
}
else
{
return v___y_1275_;
}
}
v___jp_1280_:
{
if (v___y_1281_ == 1)
{
uint8_t v___x_1282_; 
v___x_1282_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2083(v_infos_1271_, v_x_1272_, v_y_1273_);
v___y_1275_ = v___x_1282_;
goto v___jp_1274_;
}
else
{
v___y_1275_ = v___y_1281_;
goto v___jp_1274_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp___boxed(lean_object* v_infos_1285_, lean_object* v_x_1286_, lean_object* v_y_1287_){
_start:
{
uint8_t v_res_1288_; lean_object* v_r_1289_; 
v_res_1288_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_1285_, v_x_1286_, v_y_1287_);
lean_dec(v_y_1287_);
lean_dec(v_x_1286_);
lean_dec_ref(v_infos_1285_);
v_r_1289_ = lean_box(v_res_1288_);
return v_r_1289_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(lean_object* v_infos_1290_, lean_object* v_x_1291_, lean_object* v_y_1292_){
_start:
{
uint8_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1293_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_1290_, v_x_1291_, v_y_1292_);
v___x_1294_ = lean_box(v___x_1293_);
v___x_1295_ = lean_obj_tag_nat(v___x_1294_);
lean_dec(v___x_1294_);
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1297_ = lean_nat_dec_eq(v___x_1295_, v___x_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0___boxed(lean_object* v_infos_1298_, lean_object* v_x_1299_, lean_object* v_y_1300_){
_start:
{
uint8_t v_res_1301_; lean_object* v_r_1302_; 
v_res_1301_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1298_, v_x_1299_, v_y_1300_);
lean_dec(v_y_1300_);
lean_dec(v_x_1299_);
lean_dec_ref(v_infos_1298_);
v_r_1302_ = lean_box(v_res_1301_);
return v_r_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(lean_object* v_infos_1303_, lean_object* v_hi_1304_, lean_object* v_pivot_1305_, lean_object* v_as_1306_, lean_object* v_i_1307_, lean_object* v_k_1308_){
_start:
{
uint8_t v___x_1309_; 
v___x_1309_ = lean_nat_dec_lt(v_k_1308_, v_hi_1304_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_dec(v_k_1308_);
v___x_1310_ = lean_array_fswap(v_as_1306_, v_i_1307_, v_hi_1304_);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v_i_1307_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
return v___x_1311_;
}
else
{
lean_object* v___x_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1312_ = lean_array_fget_borrowed(v_as_1306_, v_k_1308_);
v___x_1313_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_1303_, v___x_1312_, v_pivot_1305_);
v___x_1314_ = lean_box(v___x_1313_);
v___x_1315_ = lean_obj_tag_nat(v___x_1314_);
lean_dec(v___x_1314_);
v___x_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = lean_nat_dec_eq(v___x_1315_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_unsigned_to_nat(1u);
v___x_1319_ = lean_nat_add(v_k_1308_, v___x_1318_);
lean_dec(v_k_1308_);
v_k_1308_ = v___x_1319_;
goto _start;
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1321_ = lean_array_fswap(v_as_1306_, v_i_1307_, v_k_1308_);
v___x_1322_ = lean_unsigned_to_nat(1u);
v___x_1323_ = lean_nat_add(v_i_1307_, v___x_1322_);
lean_dec(v_i_1307_);
v___x_1324_ = lean_nat_add(v_k_1308_, v___x_1322_);
lean_dec(v_k_1308_);
v_as_1306_ = v___x_1321_;
v_i_1307_ = v___x_1323_;
v_k_1308_ = v___x_1324_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg___boxed(lean_object* v_infos_1326_, lean_object* v_hi_1327_, lean_object* v_pivot_1328_, lean_object* v_as_1329_, lean_object* v_i_1330_, lean_object* v_k_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_infos_1326_, v_hi_1327_, v_pivot_1328_, v_as_1329_, v_i_1330_, v_k_1331_);
lean_dec(v_pivot_1328_);
lean_dec(v_hi_1327_);
lean_dec_ref(v_infos_1326_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(lean_object* v_infos_1333_, lean_object* v_n_1334_, lean_object* v_as_1335_, lean_object* v_lo_1336_, lean_object* v_hi_1337_){
_start:
{
lean_object* v___y_1339_; uint8_t v___x_1349_; 
v___x_1349_ = lean_nat_dec_lt(v_lo_1336_, v_hi_1337_);
if (v___x_1349_ == 0)
{
lean_dec(v_lo_1336_);
return v_as_1335_;
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v_mid_1352_; lean_object* v___y_1354_; lean_object* v___y_1360_; lean_object* v___x_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1350_ = lean_nat_add(v_lo_1336_, v_hi_1337_);
v___x_1351_ = lean_unsigned_to_nat(1u);
v_mid_1352_ = lean_nat_shiftr(v___x_1350_, v___x_1351_);
lean_dec(v___x_1350_);
v___x_1365_ = lean_array_fget_borrowed(v_as_1335_, v_mid_1352_);
v___x_1366_ = lean_array_fget_borrowed(v_as_1335_, v_lo_1336_);
v___x_1367_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1333_, v___x_1365_, v___x_1366_);
if (v___x_1367_ == 0)
{
v___y_1360_ = v_as_1335_;
goto v___jp_1359_;
}
else
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_array_fswap(v_as_1335_, v_lo_1336_, v_mid_1352_);
v___y_1360_ = v___x_1368_;
goto v___jp_1359_;
}
v___jp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1355_ = lean_array_fget_borrowed(v___y_1354_, v_mid_1352_);
v___x_1356_ = lean_array_fget_borrowed(v___y_1354_, v_hi_1337_);
v___x_1357_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1333_, v___x_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_dec(v_mid_1352_);
v___y_1339_ = v___y_1354_;
goto v___jp_1338_;
}
else
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_array_fswap(v___y_1354_, v_mid_1352_, v_hi_1337_);
lean_dec(v_mid_1352_);
v___y_1339_ = v___x_1358_;
goto v___jp_1338_;
}
}
v___jp_1359_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1361_ = lean_array_fget_borrowed(v___y_1360_, v_hi_1337_);
v___x_1362_ = lean_array_fget_borrowed(v___y_1360_, v_lo_1336_);
v___x_1363_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1333_, v___x_1361_, v___x_1362_);
if (v___x_1363_ == 0)
{
v___y_1354_ = v___y_1360_;
goto v___jp_1353_;
}
else
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_array_fswap(v___y_1360_, v_lo_1336_, v_hi_1337_);
v___y_1354_ = v___x_1364_;
goto v___jp_1353_;
}
}
}
v___jp_1338_:
{
lean_object* v_pivot_1340_; lean_object* v___x_1341_; lean_object* v_fst_1342_; lean_object* v_snd_1343_; uint8_t v___x_1344_; 
v_pivot_1340_ = lean_array_fget(v___y_1339_, v_hi_1337_);
lean_inc_n(v_lo_1336_, 2);
v___x_1341_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_infos_1333_, v_hi_1337_, v_pivot_1340_, v___y_1339_, v_lo_1336_, v_lo_1336_);
lean_dec(v_pivot_1340_);
v_fst_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_fst_1342_);
v_snd_1343_ = lean_ctor_get(v___x_1341_, 1);
lean_inc(v_snd_1343_);
lean_dec_ref(v___x_1341_);
v___x_1344_ = lean_nat_dec_le(v_hi_1337_, v_fst_1342_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_infos_1333_, v_n_1334_, v_snd_1343_, v_lo_1336_, v_fst_1342_);
v___x_1346_ = lean_unsigned_to_nat(1u);
v___x_1347_ = lean_nat_add(v_fst_1342_, v___x_1346_);
lean_dec(v_fst_1342_);
v_as_1335_ = v___x_1345_;
v_lo_1336_ = v___x_1347_;
goto _start;
}
else
{
lean_dec(v_fst_1342_);
lean_dec(v_lo_1336_);
return v_snd_1343_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___boxed(lean_object* v_infos_1369_, lean_object* v_n_1370_, lean_object* v_as_1371_, lean_object* v_lo_1372_, lean_object* v_hi_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_infos_1369_, v_n_1370_, v_as_1371_, v_lo_1372_, v_hi_1373_);
lean_dec(v_hi_1373_);
lean_dec(v_n_1370_);
lean_dec_ref(v_infos_1369_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(lean_object* v_infos_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1404_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1404_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1404_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_vars_1384_; lean_object* v_size_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_vars_1384_ = lean_ctor_get(v_a_1380_, 0);
lean_inc_ref(v_vars_1384_);
lean_dec(v_a_1380_);
v_size_1385_ = lean_ctor_get(v_vars_1384_, 2);
lean_inc(v_size_1385_);
lean_dec_ref(v_vars_1384_);
v___x_1386_ = l_Array_range(v_size_1385_);
v___x_1387_ = lean_array_get_size(v___x_1386_);
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = lean_nat_dec_eq(v___x_1387_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___y_1400_; uint8_t v___x_1402_; 
v___x_1397_ = lean_unsigned_to_nat(1u);
v___x_1398_ = lean_nat_sub(v___x_1387_, v___x_1397_);
v___x_1402_ = lean_nat_dec_le(v___x_1395_, v___x_1398_);
if (v___x_1402_ == 0)
{
lean_inc(v___x_1398_);
v___y_1400_ = v___x_1398_;
goto v___jp_1399_;
}
else
{
v___y_1400_ = v___x_1395_;
goto v___jp_1399_;
}
v___jp_1399_:
{
uint8_t v___x_1401_; 
v___x_1401_ = lean_nat_dec_le(v___y_1400_, v___x_1398_);
if (v___x_1401_ == 0)
{
lean_dec(v___x_1398_);
lean_inc(v___y_1400_);
v___y_1389_ = v___y_1400_;
v___y_1390_ = v___y_1400_;
goto v___jp_1388_;
}
else
{
v___y_1389_ = v___y_1400_;
v___y_1390_ = v___x_1398_;
goto v___jp_1388_;
}
}
}
else
{
lean_object* v___x_1403_; 
lean_del_object(v___x_1382_);
v___x_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1386_);
return v___x_1403_;
}
v___jp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_infos_1375_, v___x_1387_, v___x_1386_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1391_);
v___x_1393_ = v___x_1382_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1379_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1379_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg___boxed(lean_object* v_infos_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(v_infos_1413_, v_a_1414_, v_a_1415_);
lean_dec_ref(v_a_1415_);
lean_dec(v_a_1414_);
lean_dec_ref(v_infos_1413_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(lean_object* v_infos_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(v_infos_1418_, v_a_1419_, v_a_1427_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___boxed(lean_object* v_infos_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(v_infos_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_a_1435_);
lean_dec_ref(v_a_1434_);
lean_dec(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_infos_1431_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(lean_object* v_infos_1444_, lean_object* v_n_1445_, lean_object* v_as_1446_, lean_object* v_lo_1447_, lean_object* v_hi_1448_, lean_object* v_w_1449_, lean_object* v_hlo_1450_, lean_object* v_hhi_1451_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_infos_1444_, v_n_1445_, v_as_1446_, v_lo_1447_, v_hi_1448_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___boxed(lean_object* v_infos_1453_, lean_object* v_n_1454_, lean_object* v_as_1455_, lean_object* v_lo_1456_, lean_object* v_hi_1457_, lean_object* v_w_1458_, lean_object* v_hlo_1459_, lean_object* v_hhi_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(v_infos_1453_, v_n_1454_, v_as_1455_, v_lo_1456_, v_hi_1457_, v_w_1458_, v_hlo_1459_, v_hhi_1460_);
lean_dec(v_hi_1457_);
lean_dec(v_n_1454_);
lean_dec_ref(v_infos_1453_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0(lean_object* v_infos_1462_, lean_object* v_n_1463_, lean_object* v_lo_1464_, lean_object* v_hi_1465_, lean_object* v_hhi_1466_, lean_object* v_pivot_1467_, lean_object* v_as_1468_, lean_object* v_i_1469_, lean_object* v_k_1470_, lean_object* v_ilo_1471_, lean_object* v_ik_1472_, lean_object* v_w_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_infos_1462_, v_hi_1465_, v_pivot_1467_, v_as_1468_, v_i_1469_, v_k_1470_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___boxed(lean_object* v_infos_1475_, lean_object* v_n_1476_, lean_object* v_lo_1477_, lean_object* v_hi_1478_, lean_object* v_hhi_1479_, lean_object* v_pivot_1480_, lean_object* v_as_1481_, lean_object* v_i_1482_, lean_object* v_k_1483_, lean_object* v_ilo_1484_, lean_object* v_ik_1485_, lean_object* v_w_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0(v_infos_1475_, v_n_1476_, v_lo_1477_, v_hi_1478_, v_hhi_1479_, v_pivot_1480_, v_as_1481_, v_i_1482_, v_k_1483_, v_ilo_1484_, v_ik_1485_, v_w_1486_);
lean_dec(v_pivot_1480_);
lean_dec(v_hi_1478_);
lean_dec(v_lo_1477_);
lean_dec(v_n_1476_);
lean_dec_ref(v_infos_1475_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(lean_object* v_perm_1488_, lean_object* v_range_1489_, lean_object* v_b_1490_, lean_object* v_i_1491_){
_start:
{
lean_object* v_stop_1492_; lean_object* v_step_1493_; uint8_t v___x_1494_; 
v_stop_1492_ = lean_ctor_get(v_range_1489_, 1);
v_step_1493_ = lean_ctor_get(v_range_1489_, 2);
v___x_1494_ = lean_nat_dec_lt(v_i_1491_, v_stop_1492_);
if (v___x_1494_ == 0)
{
lean_dec(v_i_1491_);
return v_b_1490_;
}
else
{
lean_object* v___x_1495_; lean_object* v_inv_1496_; lean_object* v___x_1497_; 
v___x_1495_ = lean_array_fget_borrowed(v_perm_1488_, v_i_1491_);
lean_inc(v_i_1491_);
v_inv_1496_ = lean_array_set(v_b_1490_, v___x_1495_, v_i_1491_);
v___x_1497_ = lean_nat_add(v_i_1491_, v_step_1493_);
lean_dec(v_i_1491_);
v_b_1490_ = v_inv_1496_;
v_i_1491_ = v___x_1497_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg___boxed(lean_object* v_perm_1499_, lean_object* v_range_1500_, lean_object* v_b_1501_, lean_object* v_i_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1499_, v_range_1500_, v_b_1501_, v_i_1502_);
lean_dec_ref(v_range_1500_);
lean_dec_ref(v_perm_1499_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(lean_object* v_perm_1504_){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v_inv_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1505_ = lean_array_get_size(v_perm_1504_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v_inv_1507_ = lean_mk_array(v___x_1505_, v___x_1506_);
v___x_1508_ = lean_unsigned_to_nat(1u);
v___x_1509_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1506_);
lean_ctor_set(v___x_1509_, 1, v___x_1505_);
lean_ctor_set(v___x_1509_, 2, v___x_1508_);
v___x_1510_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1504_, v___x_1509_, v_inv_1507_, v___x_1506_);
lean_dec_ref_known(v___x_1509_, 3);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv___boxed(lean_object* v_perm_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_perm_1511_);
lean_dec_ref(v_perm_1511_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(lean_object* v_perm_1513_, lean_object* v_range_1514_, lean_object* v_b_1515_, lean_object* v_i_1516_, lean_object* v_hs_1517_, lean_object* v_hl_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1513_, v_range_1514_, v_b_1515_, v_i_1516_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___boxed(lean_object* v_perm_1520_, lean_object* v_range_1521_, lean_object* v_b_1522_, lean_object* v_i_1523_, lean_object* v_hs_1524_, lean_object* v_hl_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(v_perm_1520_, v_range_1521_, v_b_1522_, v_i_1523_, v_hs_1524_, v_hl_1525_);
lean_dec_ref(v_range_1521_);
lean_dec_ref(v_perm_1520_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_reorder(lean_object* v_p_1527_, lean_object* v_old2new_1528_){
_start:
{
if (lean_obj_tag(v_p_1527_) == 0)
{
return v_p_1527_;
}
else
{
lean_object* v_k_1529_; lean_object* v_v_1530_; lean_object* v_p_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1541_; 
v_k_1529_ = lean_ctor_get(v_p_1527_, 0);
v_v_1530_ = lean_ctor_get(v_p_1527_, 1);
v_p_1531_ = lean_ctor_get(v_p_1527_, 2);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_p_1527_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1533_ = v_p_1527_;
v_isShared_1534_ = v_isSharedCheck_1541_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_p_1531_);
lean_inc(v_v_1530_);
lean_inc(v_k_1529_);
lean_dec(v_p_1527_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1541_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1539_; 
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = lean_array_get_borrowed(v___x_1535_, v_old2new_1528_, v_v_1530_);
lean_dec(v_v_1530_);
v___x_1537_ = l_Int_Internal_Linear_Poly_reorder(v_p_1531_, v_old2new_1528_);
lean_inc(v___x_1536_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 2, v___x_1537_);
lean_ctor_set(v___x_1533_, 1, v___x_1536_);
v___x_1539_ = v___x_1533_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_k_1529_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_reorder___boxed(lean_object* v_p_1542_, lean_object* v_old2new_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Int_Internal_Linear_Poly_reorder(v_p_1542_, v_old2new_1543_);
lean_dec_ref(v_old2new_1543_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(lean_object* v_c_1545_, lean_object* v_old2new_1546_){
_start:
{
lean_object* v_d_1547_; lean_object* v_p_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_d_1547_ = lean_ctor_get(v_c_1545_, 0);
lean_inc(v_d_1547_);
v_p_1548_ = lean_ctor_get(v_c_1545_, 1);
lean_inc_ref(v_p_1548_);
v___x_1549_ = l_Int_Internal_Linear_Poly_reorder(v_p_1548_, v_old2new_1546_);
v___x_1550_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1550_, 0, v_c_1545_);
v___x_1551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1551_, 0, v_d_1547_);
lean_ctor_set(v___x_1551_, 1, v___x_1549_);
lean_ctor_set(v___x_1551_, 2, v___x_1550_);
v___x_1552_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v___x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder___boxed(lean_object* v_c_1553_, lean_object* v_old2new_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(v_c_1553_, v_old2new_1554_);
lean_dec_ref(v_old2new_1554_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(lean_object* v_c_1556_, lean_object* v_old2new_1557_){
_start:
{
lean_object* v_p_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_p_1558_ = lean_ctor_get(v_c_1556_, 0);
lean_inc_ref(v_p_1558_);
v___x_1559_ = l_Int_Internal_Linear_Poly_reorder(v_p_1558_, v_old2new_1557_);
v___x_1560_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_1560_, 0, v_c_1556_);
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_norm(v___x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder___boxed(lean_object* v_c_1563_, lean_object* v_old2new_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_c_1563_, v_old2new_1564_);
lean_dec_ref(v_old2new_1564_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(lean_object* v_c_1566_, lean_object* v_old2new_1567_){
_start:
{
lean_object* v_p_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_p_1568_ = lean_ctor_get(v_c_1566_, 0);
lean_inc_ref(v_p_1568_);
v___x_1569_ = l_Int_Internal_Linear_Poly_reorder(v_p_1568_, v_old2new_1567_);
v___x_1570_ = lean_alloc_ctor(16, 1, 0);
lean_ctor_set(v___x_1570_, 0, v_c_1566_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder___boxed(lean_object* v_c_1573_, lean_object* v_old2new_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_c_1573_, v_old2new_1574_);
lean_dec_ref(v_old2new_1574_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(lean_object* v_c_1576_, lean_object* v_old2new_1577_){
_start:
{
lean_object* v_p_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v_p_1578_ = lean_ctor_get(v_c_1576_, 0);
lean_inc_ref(v_p_1578_);
v___x_1579_ = l_Int_Internal_Linear_Poly_reorder(v_p_1578_, v_old2new_1577_);
v___x_1580_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1580_, 0, v_c_1576_);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_norm(v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder___boxed(lean_object* v_c_1583_, lean_object* v_old2new_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(v_c_1583_, v_old2new_1584_);
lean_dec_ref(v_old2new_1584_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(lean_object* v_new2old_1586_, lean_object* v_inst_1587_, lean_object* v_m_1588_, lean_object* v_i_1589_, lean_object* v_h_1590_, lean_object* v_____s_1591_){
_start:
{
lean_object* v_j_1592_; lean_object* v___x_1593_; lean_object* v_r_1594_; lean_object* v___x_1595_; 
v_j_1592_ = lean_array_fget_borrowed(v_new2old_1586_, v_i_1589_);
v___x_1593_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_1587_, v_m_1588_, v_j_1592_);
v_r_1594_ = l_Lean_PersistentArray_push___redArg(v_____s_1591_, v___x_1593_);
v___x_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1595_, 0, v_r_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed(lean_object* v_new2old_1596_, lean_object* v_inst_1597_, lean_object* v_m_1598_, lean_object* v_i_1599_, lean_object* v_h_1600_, lean_object* v_____s_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(v_new2old_1596_, v_inst_1597_, v_m_1598_, v_i_1599_, v_h_1600_, v_____s_1601_);
lean_dec(v_i_1599_);
lean_dec_ref(v_m_1598_);
lean_dec(v_inst_1597_);
lean_dec_ref(v_new2old_1596_);
return v_res_1602_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1622_ = lean_unsigned_to_nat(32u);
v___x_1623_ = lean_mk_empty_array_with_capacity(v___x_1622_);
v___x_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
return v___x_1624_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11(void){
_start:
{
size_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v_r_1630_; 
v___x_1625_ = ((size_t)5ULL);
v___x_1626_ = lean_unsigned_to_nat(0u);
v___x_1627_ = lean_unsigned_to_nat(32u);
v___x_1628_ = lean_mk_empty_array_with_capacity(v___x_1627_);
v___x_1629_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10);
v_r_1630_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_r_1630_, 0, v___x_1629_);
lean_ctor_set(v_r_1630_, 1, v___x_1628_);
lean_ctor_set(v_r_1630_, 2, v___x_1626_);
lean_ctor_set(v_r_1630_, 3, v___x_1626_);
lean_ctor_set_usize(v_r_1630_, 4, v___x_1625_);
return v_r_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(lean_object* v_inst_1631_, lean_object* v_m_1632_, lean_object* v_new2old_1633_){
_start:
{
lean_object* v___f_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v_r_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_inc_ref(v_new2old_1633_);
v___f_1634_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1634_, 0, v_new2old_1633_);
lean_closure_set(v___f_1634_, 1, v_inst_1631_);
lean_closure_set(v___f_1634_, 2, v_m_1632_);
v___x_1635_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9));
v___x_1636_ = lean_unsigned_to_nat(0u);
v_r_1637_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11);
v___x_1638_ = lean_array_get_size(v_new2old_1633_);
lean_dec_ref(v_new2old_1633_);
v___x_1639_ = lean_unsigned_to_nat(1u);
v___x_1640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1636_);
lean_ctor_set(v___x_1640_, 1, v___x_1638_);
lean_ctor_set(v___x_1640_, 2, v___x_1639_);
v___x_1641_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_box(0), lean_box(0), v___x_1635_, v___x_1640_, v___f_1634_, v_r_1637_, v___x_1636_, lean_box(0), lean_box(0));
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap(lean_object* v_00_u03b1_1642_, lean_object* v_inst_1643_, lean_object* v_m_1644_, lean_object* v_new2old_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v_inst_1643_, v_m_1644_, v_new2old_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_){
_start:
{
lean_object* v_ks_1651_; lean_object* v_vs_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1676_; 
v_ks_1651_ = lean_ctor_get(v_x_1647_, 0);
v_vs_1652_ = lean_ctor_get(v_x_1647_, 1);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_x_1647_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1654_ = v_x_1647_;
v_isShared_1655_ = v_isSharedCheck_1676_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_vs_1652_);
lean_inc(v_ks_1651_);
lean_dec(v_x_1647_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1676_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1656_ = lean_array_get_size(v_ks_1651_);
v___x_1657_ = lean_nat_dec_lt(v_x_1648_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
lean_dec(v_x_1648_);
v___x_1658_ = lean_array_push(v_ks_1651_, v_x_1649_);
v___x_1659_ = lean_array_push(v_vs_1652_, v_x_1650_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 1, v___x_1659_);
lean_ctor_set(v___x_1654_, 0, v___x_1658_);
v___x_1661_ = v___x_1654_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1658_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
else
{
lean_object* v_k_x27_1663_; uint8_t v___x_1664_; 
v_k_x27_1663_ = lean_array_fget_borrowed(v_ks_1651_, v_x_1648_);
v___x_1664_ = l_Int_Internal_Linear_instBEqPoly_beq(v_x_1649_, v_k_x27_1663_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1666_; 
if (v_isShared_1655_ == 0)
{
v___x_1666_ = v___x_1654_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_ks_1651_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_vs_1652_);
v___x_1666_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = lean_nat_add(v_x_1648_, v___x_1667_);
lean_dec(v_x_1648_);
v_x_1647_ = v___x_1666_;
v_x_1648_ = v___x_1668_;
goto _start;
}
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1671_ = lean_array_fset(v_ks_1651_, v_x_1648_, v_x_1649_);
v___x_1672_ = lean_array_fset(v_vs_1652_, v_x_1648_, v_x_1650_);
lean_dec(v_x_1648_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 1, v___x_1672_);
lean_ctor_set(v___x_1654_, 0, v___x_1671_);
v___x_1674_ = v___x_1654_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1677_, lean_object* v_k_1678_, lean_object* v_v_1679_){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_unsigned_to_nat(0u);
v___x_1681_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1677_, v___x_1680_, v_k_1678_, v_v_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(lean_object* v_x_1683_, size_t v_x_1684_, size_t v_x_1685_, lean_object* v_x_1686_, lean_object* v_x_1687_){
_start:
{
if (lean_obj_tag(v_x_1683_) == 0)
{
lean_object* v_es_1688_; size_t v___x_1689_; size_t v___x_1690_; lean_object* v_j_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v_es_1688_ = lean_ctor_get(v_x_1683_, 0);
v___x_1689_ = ((size_t)31ULL);
v___x_1690_ = lean_usize_land(v_x_1684_, v___x_1689_);
v_j_1691_ = lean_usize_to_nat(v___x_1690_);
v___x_1692_ = lean_array_get_size(v_es_1688_);
v___x_1693_ = lean_nat_dec_lt(v_j_1691_, v___x_1692_);
if (v___x_1693_ == 0)
{
lean_dec(v_j_1691_);
lean_dec(v_x_1687_);
lean_dec_ref(v_x_1686_);
return v_x_1683_;
}
else
{
lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1732_; 
lean_inc_ref(v_es_1688_);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_x_1683_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; 
v_unused_1733_ = lean_ctor_get(v_x_1683_, 0);
lean_dec(v_unused_1733_);
v___x_1695_ = v_x_1683_;
v_isShared_1696_ = v_isSharedCheck_1732_;
goto v_resetjp_1694_;
}
else
{
lean_dec(v_x_1683_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1732_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v_v_1697_; lean_object* v___x_1698_; lean_object* v_xs_x27_1699_; lean_object* v___y_1701_; 
v_v_1697_ = lean_array_fget(v_es_1688_, v_j_1691_);
v___x_1698_ = lean_box(0);
v_xs_x27_1699_ = lean_array_fset(v_es_1688_, v_j_1691_, v___x_1698_);
switch(lean_obj_tag(v_v_1697_))
{
case 0:
{
lean_object* v_key_1706_; lean_object* v_val_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1717_; 
v_key_1706_ = lean_ctor_get(v_v_1697_, 0);
v_val_1707_ = lean_ctor_get(v_v_1697_, 1);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_v_1697_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1709_ = v_v_1697_;
v_isShared_1710_ = v_isSharedCheck_1717_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_val_1707_);
lean_inc(v_key_1706_);
lean_dec(v_v_1697_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1717_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
uint8_t v___x_1711_; 
v___x_1711_ = l_Int_Internal_Linear_instBEqPoly_beq(v_x_1686_, v_key_1706_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_del_object(v___x_1709_);
v___x_1712_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1706_, v_val_1707_, v_x_1686_, v_x_1687_);
v___x_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
v___y_1701_ = v___x_1713_;
goto v___jp_1700_;
}
else
{
lean_object* v___x_1715_; 
lean_dec(v_val_1707_);
lean_dec(v_key_1706_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 1, v_x_1687_);
lean_ctor_set(v___x_1709_, 0, v_x_1686_);
v___x_1715_ = v___x_1709_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_x_1686_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_x_1687_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
v___y_1701_ = v___x_1715_;
goto v___jp_1700_;
}
}
}
}
case 1:
{
lean_object* v_node_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1730_; 
v_node_1718_ = lean_ctor_get(v_v_1697_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_v_1697_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1720_ = v_v_1697_;
v_isShared_1721_ = v_isSharedCheck_1730_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_node_1718_);
lean_dec(v_v_1697_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1730_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
size_t v___x_1722_; size_t v___x_1723_; size_t v___x_1724_; size_t v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1722_ = ((size_t)5ULL);
v___x_1723_ = lean_usize_shift_right(v_x_1684_, v___x_1722_);
v___x_1724_ = ((size_t)1ULL);
v___x_1725_ = lean_usize_add(v_x_1685_, v___x_1724_);
v___x_1726_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_node_1718_, v___x_1723_, v___x_1725_, v_x_1686_, v_x_1687_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1726_);
v___x_1728_ = v___x_1720_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
v___y_1701_ = v___x_1728_;
goto v___jp_1700_;
}
}
}
default: 
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v_x_1686_);
lean_ctor_set(v___x_1731_, 1, v_x_1687_);
v___y_1701_ = v___x_1731_;
goto v___jp_1700_;
}
}
v___jp_1700_:
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = lean_array_fset(v_xs_x27_1699_, v_j_1691_, v___y_1701_);
lean_dec(v_j_1691_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1702_);
v___x_1704_ = v___x_1695_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
else
{
lean_object* v_ks_1734_; lean_object* v_vs_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1753_; 
v_ks_1734_ = lean_ctor_get(v_x_1683_, 0);
v_vs_1735_ = lean_ctor_get(v_x_1683_, 1);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_x_1683_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1737_ = v_x_1683_;
v_isShared_1738_ = v_isSharedCheck_1753_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_vs_1735_);
lean_inc(v_ks_1734_);
lean_dec(v_x_1683_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1753_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_ks_1734_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_vs_1735_);
v___x_1740_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v_newNode_1741_; size_t v___x_1742_; uint8_t v___x_1743_; 
v_newNode_1741_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(v___x_1740_, v_x_1686_, v_x_1687_);
v___x_1742_ = ((size_t)7ULL);
v___x_1743_ = lean_usize_dec_le(v___x_1742_, v_x_1685_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1744_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1741_);
v___x_1745_ = lean_unsigned_to_nat(4u);
v___x_1746_ = lean_nat_dec_lt(v___x_1744_, v___x_1745_);
lean_dec(v___x_1744_);
if (v___x_1746_ == 0)
{
lean_object* v_ks_1747_; lean_object* v_vs_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_ks_1747_ = lean_ctor_get(v_newNode_1741_, 0);
lean_inc_ref(v_ks_1747_);
v_vs_1748_ = lean_ctor_get(v_newNode_1741_, 1);
lean_inc_ref(v_vs_1748_);
lean_dec_ref(v_newNode_1741_);
v___x_1749_ = lean_unsigned_to_nat(0u);
v___x_1750_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0);
v___x_1751_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_x_1685_, v_ks_1747_, v_vs_1748_, v___x_1749_, v___x_1750_);
lean_dec_ref(v_vs_1748_);
lean_dec_ref(v_ks_1747_);
return v___x_1751_;
}
else
{
return v_newNode_1741_;
}
}
else
{
return v_newNode_1741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(size_t v_depth_1754_, lean_object* v_keys_1755_, lean_object* v_vals_1756_, lean_object* v_i_1757_, lean_object* v_entries_1758_){
_start:
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = lean_array_get_size(v_keys_1755_);
v___x_1760_ = lean_nat_dec_lt(v_i_1757_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_dec(v_i_1757_);
return v_entries_1758_;
}
else
{
lean_object* v_k_1761_; lean_object* v_v_1762_; uint64_t v___x_1763_; size_t v_h_1764_; size_t v___x_1765_; lean_object* v___x_1766_; size_t v___x_1767_; size_t v___x_1768_; size_t v___x_1769_; size_t v_h_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_k_1761_ = lean_array_fget_borrowed(v_keys_1755_, v_i_1757_);
v_v_1762_ = lean_array_fget_borrowed(v_vals_1756_, v_i_1757_);
v___x_1763_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_k_1761_);
v_h_1764_ = lean_uint64_to_usize(v___x_1763_);
v___x_1765_ = ((size_t)5ULL);
v___x_1766_ = lean_unsigned_to_nat(1u);
v___x_1767_ = ((size_t)1ULL);
v___x_1768_ = lean_usize_sub(v_depth_1754_, v___x_1767_);
v___x_1769_ = lean_usize_mul(v___x_1765_, v___x_1768_);
v_h_1770_ = lean_usize_shift_right(v_h_1764_, v___x_1769_);
v___x_1771_ = lean_nat_add(v_i_1757_, v___x_1766_);
lean_dec(v_i_1757_);
lean_inc(v_v_1762_);
lean_inc(v_k_1761_);
v___x_1772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_entries_1758_, v_h_1770_, v_depth_1754_, v_k_1761_, v_v_1762_);
v_i_1757_ = v___x_1771_;
v_entries_1758_ = v___x_1772_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1774_, lean_object* v_keys_1775_, lean_object* v_vals_1776_, lean_object* v_i_1777_, lean_object* v_entries_1778_){
_start:
{
size_t v_depth_boxed_1779_; lean_object* v_res_1780_; 
v_depth_boxed_1779_ = lean_unbox_usize(v_depth_1774_);
lean_dec(v_depth_1774_);
v_res_1780_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1779_, v_keys_1775_, v_vals_1776_, v_i_1777_, v_entries_1778_);
lean_dec_ref(v_vals_1776_);
lean_dec_ref(v_keys_1775_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___boxed(lean_object* v_x_1781_, lean_object* v_x_1782_, lean_object* v_x_1783_, lean_object* v_x_1784_, lean_object* v_x_1785_){
_start:
{
size_t v_x_1760__boxed_1786_; size_t v_x_1761__boxed_1787_; lean_object* v_res_1788_; 
v_x_1760__boxed_1786_ = lean_unbox_usize(v_x_1782_);
lean_dec(v_x_1782_);
v_x_1761__boxed_1787_ = lean_unbox_usize(v_x_1783_);
lean_dec(v_x_1783_);
v_res_1788_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1781_, v_x_1760__boxed_1786_, v_x_1761__boxed_1787_, v_x_1784_, v_x_1785_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(lean_object* v_x_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_){
_start:
{
uint64_t v___x_1792_; size_t v___x_1793_; size_t v___x_1794_; lean_object* v___x_1795_; 
v___x_1792_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_x_1790_);
v___x_1793_ = lean_uint64_to_usize(v___x_1792_);
v___x_1794_ = ((size_t)1ULL);
v___x_1795_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1789_, v___x_1793_, v___x_1794_, v_x_1790_, v_x_1791_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(lean_object* v_old2new_1796_, lean_object* v_x_1797_, lean_object* v_____s_1798_){
_start:
{
lean_object* v_fst_1799_; lean_object* v_snd_1800_; lean_object* v___x_1801_; lean_object* v_m_x27_1802_; lean_object* v___x_1803_; 
v_fst_1799_ = lean_ctor_get(v_x_1797_, 0);
lean_inc(v_fst_1799_);
v_snd_1800_ = lean_ctor_get(v_x_1797_, 1);
lean_inc(v_snd_1800_);
lean_dec_ref(v_x_1797_);
v___x_1801_ = l_Int_Internal_Linear_Poly_reorder(v_fst_1799_, v_old2new_1796_);
v_m_x27_1802_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(v_____s_1798_, v___x_1801_, v_snd_1800_);
v___x_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1803_, 0, v_m_x27_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed(lean_object* v_old2new_1804_, lean_object* v_x_1805_, lean_object* v_____s_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(v_old2new_1804_, v_x_1805_, v_____s_1806_);
lean_dec_ref(v_old2new_1804_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_f_1808_, lean_object* v_keys_1809_, lean_object* v_vals_1810_, lean_object* v_i_1811_, lean_object* v_acc_1812_){
_start:
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = lean_array_get_size(v_keys_1809_);
v___x_1814_ = lean_nat_dec_lt(v_i_1811_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; 
lean_dec(v_i_1811_);
lean_dec_ref(v_f_1808_);
v___x_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_acc_1812_);
return v___x_1815_;
}
else
{
lean_object* v_k_1816_; lean_object* v_v_1817_; lean_object* v___x_1818_; 
v_k_1816_ = lean_array_fget_borrowed(v_keys_1809_, v_i_1811_);
v_v_1817_ = lean_array_fget_borrowed(v_vals_1810_, v_i_1811_);
lean_inc_ref(v_f_1808_);
lean_inc(v_v_1817_);
lean_inc(v_k_1816_);
v___x_1818_ = lean_apply_3(v_f_1808_, v_acc_1812_, v_k_1816_, v_v_1817_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_dec(v_i_1811_);
lean_dec_ref(v_f_1808_);
return v___x_1818_;
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1818_, 1);
v___x_1820_ = lean_unsigned_to_nat(1u);
v___x_1821_ = lean_nat_add(v_i_1811_, v___x_1820_);
lean_dec(v_i_1811_);
v_i_1811_ = v___x_1821_;
v_acc_1812_ = v_a_1819_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_f_1823_, lean_object* v_keys_1824_, lean_object* v_vals_1825_, lean_object* v_i_1826_, lean_object* v_acc_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1823_, v_keys_1824_, v_vals_1825_, v_i_1826_, v_acc_1827_);
lean_dec_ref(v_vals_1825_);
lean_dec_ref(v_keys_1824_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_f_1829_, lean_object* v_as_1830_, size_t v_i_1831_, size_t v_stop_1832_, lean_object* v_b_1833_){
_start:
{
lean_object* v_a_1835_; lean_object* v___y_1840_; uint8_t v___x_1842_; 
v___x_1842_ = lean_usize_dec_eq(v_i_1831_, v_stop_1832_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_array_uget_borrowed(v_as_1830_, v_i_1831_);
switch(lean_obj_tag(v___x_1843_))
{
case 0:
{
lean_object* v_key_1844_; lean_object* v_val_1845_; lean_object* v___x_1846_; 
v_key_1844_ = lean_ctor_get(v___x_1843_, 0);
v_val_1845_ = lean_ctor_get(v___x_1843_, 1);
lean_inc_ref(v_f_1829_);
lean_inc(v_val_1845_);
lean_inc(v_key_1844_);
v___x_1846_ = lean_apply_3(v_f_1829_, v_b_1833_, v_key_1844_, v_val_1845_);
v___y_1840_ = v___x_1846_;
goto v___jp_1839_;
}
case 1:
{
lean_object* v_node_1847_; lean_object* v___x_1848_; 
v_node_1847_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_node_1847_);
lean_inc_ref(v_f_1829_);
v___x_1848_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1829_, v_node_1847_, v_b_1833_);
v___y_1840_ = v___x_1848_;
goto v___jp_1839_;
}
default: 
{
v_a_1835_ = v_b_1833_;
goto v___jp_1834_;
}
}
}
else
{
lean_object* v___x_1849_; 
lean_dec_ref(v_f_1829_);
v___x_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1849_, 0, v_b_1833_);
return v___x_1849_;
}
v___jp_1834_:
{
size_t v___x_1836_; size_t v___x_1837_; 
v___x_1836_ = ((size_t)1ULL);
v___x_1837_ = lean_usize_add(v_i_1831_, v___x_1836_);
v_i_1831_ = v___x_1837_;
v_b_1833_ = v_a_1835_;
goto _start;
}
v___jp_1839_:
{
if (lean_obj_tag(v___y_1840_) == 0)
{
lean_dec_ref(v_f_1829_);
return v___y_1840_;
}
else
{
lean_object* v_a_1841_; 
v_a_1841_ = lean_ctor_get(v___y_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v___y_1840_, 1);
v_a_1835_ = v_a_1841_;
goto v___jp_1834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(lean_object* v_f_1850_, lean_object* v_x_1851_, lean_object* v_x_1852_){
_start:
{
if (lean_obj_tag(v_x_1851_) == 0)
{
lean_object* v_es_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1866_; 
v_es_1853_ = lean_ctor_get(v_x_1851_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v_x_1851_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1855_ = v_x_1851_;
v_isShared_1856_ = v_isSharedCheck_1866_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_es_1853_);
lean_dec(v_x_1851_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1866_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1857_ = lean_unsigned_to_nat(0u);
v___x_1858_ = lean_array_get_size(v_es_1853_);
v___x_1859_ = lean_nat_dec_lt(v___x_1857_, v___x_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1861_; 
lean_dec_ref(v_es_1853_);
lean_dec_ref(v_f_1850_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set_tag(v___x_1855_, 1);
lean_ctor_set(v___x_1855_, 0, v_x_1852_);
v___x_1861_ = v___x_1855_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_x_1852_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
else
{
size_t v___x_1863_; size_t v___x_1864_; lean_object* v___x_1865_; 
lean_del_object(v___x_1855_);
v___x_1863_ = ((size_t)0ULL);
v___x_1864_ = lean_usize_of_nat(v___x_1858_);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1850_, v_es_1853_, v___x_1863_, v___x_1864_, v_x_1852_);
lean_dec_ref(v_es_1853_);
return v___x_1865_;
}
}
}
else
{
lean_object* v_ks_1867_; lean_object* v_vs_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_ks_1867_ = lean_ctor_get(v_x_1851_, 0);
lean_inc_ref(v_ks_1867_);
v_vs_1868_ = lean_ctor_get(v_x_1851_, 1);
lean_inc_ref(v_vs_1868_);
lean_dec_ref_known(v_x_1851_, 2);
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1870_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1850_, v_ks_1867_, v_vs_1868_, v___x_1869_, v_x_1852_);
lean_dec_ref(v_vs_1868_);
lean_dec_ref(v_ks_1867_);
return v___x_1870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_f_1871_, lean_object* v_as_1872_, lean_object* v_i_1873_, lean_object* v_stop_1874_, lean_object* v_b_1875_){
_start:
{
size_t v_i_boxed_1876_; size_t v_stop_boxed_1877_; lean_object* v_res_1878_; 
v_i_boxed_1876_ = lean_unbox_usize(v_i_1873_);
lean_dec(v_i_1873_);
v_stop_boxed_1877_ = lean_unbox_usize(v_stop_1874_);
lean_dec(v_stop_1874_);
v_res_1878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1871_, v_as_1872_, v_i_boxed_1876_, v_stop_boxed_1877_, v_b_1875_);
lean_dec_ref(v_as_1872_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0(lean_object* v_f_1879_, lean_object* v_s_1880_, lean_object* v_a_1881_, lean_object* v_b_1882_){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v_a_1881_);
lean_ctor_set(v___x_1883_, 1, v_b_1882_);
v___x_1884_ = lean_apply_2(v_f_1879_, v___x_1883_, v_s_1880_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1884_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1884_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
v_a_1893_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1884_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1884_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(lean_object* v_map_1901_, lean_object* v_init_1902_, lean_object* v_f_1903_){
_start:
{
lean_object* v___f_1904_; lean_object* v___x_1905_; lean_object* v_a_1906_; 
v___f_1904_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1904_, 0, v_f_1903_);
lean_inc_ref(v_map_1901_);
v___x_1905_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v___f_1904_, v_map_1901_, v_init_1902_);
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref(v___x_1905_);
return v_a_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___boxed(lean_object* v_map_1907_, lean_object* v_init_1908_, lean_object* v_f_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_map_1907_, v_init_1908_, v_f_1909_);
lean_dec_ref(v_map_1907_);
return v_res_1910_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0(void){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1911_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1(void){
_start:
{
lean_object* v___x_1912_; lean_object* v_m_x27_1913_; 
v___x_1912_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0);
v_m_x27_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_m_x27_1913_, 0, v___x_1912_);
return v_m_x27_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(lean_object* v_m_1914_, lean_object* v_old2new_1915_){
_start:
{
lean_object* v___f_1916_; lean_object* v_m_x27_1917_; lean_object* v___x_1918_; 
v___f_1916_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1916_, 0, v_old2new_1915_);
v_m_x27_1917_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1);
v___x_1918_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_m_1914_, v_m_x27_1917_, v___f_1916_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___boxed(lean_object* v_m_1919_, lean_object* v_old2new_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(v_m_1919_, v_old2new_1920_);
lean_dec_ref(v_m_1919_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0(lean_object* v_00_u03b2_1922_, lean_object* v_x_1923_, lean_object* v_x_1924_, lean_object* v_x_1925_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(v_x_1923_, v_x_1924_, v_x_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(lean_object* v_00_u03c3_1927_, lean_object* v_00_u03b2_1928_, lean_object* v_map_1929_, lean_object* v_init_1930_, lean_object* v_f_1931_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_map_1929_, v_init_1930_, v_f_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___boxed(lean_object* v_00_u03c3_1933_, lean_object* v_00_u03b2_1934_, lean_object* v_map_1935_, lean_object* v_init_1936_, lean_object* v_f_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(v_00_u03c3_1933_, v_00_u03b2_1934_, v_map_1935_, v_init_1936_, v_f_1937_);
lean_dec_ref(v_map_1935_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(lean_object* v_00_u03b2_1939_, lean_object* v_x_1940_, size_t v_x_1941_, size_t v_x_1942_, lean_object* v_x_1943_, lean_object* v_x_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1940_, v_x_1941_, v_x_1942_, v_x_1943_, v_x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1946_, lean_object* v_x_1947_, lean_object* v_x_1948_, lean_object* v_x_1949_, lean_object* v_x_1950_, lean_object* v_x_1951_){
_start:
{
size_t v_x_2093__boxed_1952_; size_t v_x_2094__boxed_1953_; lean_object* v_res_1954_; 
v_x_2093__boxed_1952_ = lean_unbox_usize(v_x_1948_);
lean_dec(v_x_1948_);
v_x_2094__boxed_1953_ = lean_unbox_usize(v_x_1949_);
lean_dec(v_x_1949_);
v_res_1954_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(v_00_u03b2_1946_, v_x_1947_, v_x_2093__boxed_1952_, v_x_2094__boxed_1953_, v_x_1950_, v_x_1951_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2___redArg(lean_object* v_map_1955_, lean_object* v_f_1956_, lean_object* v_init_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1956_, v_map_1955_, v_init_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2(lean_object* v_00_u03c3_1959_, lean_object* v_00_u03c3_1960_, lean_object* v_00_u03b2_1961_, lean_object* v_map_1962_, lean_object* v_f_1963_, lean_object* v_init_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1963_, v_map_1962_, v_init_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1966_, lean_object* v_n_1967_, lean_object* v_k_1968_, lean_object* v_v_1969_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(v_n_1967_, v_k_1968_, v_v_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1971_, size_t v_depth_1972_, lean_object* v_keys_1973_, lean_object* v_vals_1974_, lean_object* v_heq_1975_, lean_object* v_i_1976_, lean_object* v_entries_1977_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_1972_, v_keys_1973_, v_vals_1974_, v_i_1976_, v_entries_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1979_, lean_object* v_depth_1980_, lean_object* v_keys_1981_, lean_object* v_vals_1982_, lean_object* v_heq_1983_, lean_object* v_i_1984_, lean_object* v_entries_1985_){
_start:
{
size_t v_depth_boxed_1986_; lean_object* v_res_1987_; 
v_depth_boxed_1986_ = lean_unbox_usize(v_depth_1980_);
lean_dec(v_depth_1980_);
v_res_1987_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(v_00_u03b2_1979_, v_depth_boxed_1986_, v_keys_1981_, v_vals_1982_, v_heq_1983_, v_i_1984_, v_entries_1985_);
lean_dec_ref(v_vals_1982_);
lean_dec_ref(v_keys_1981_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5(lean_object* v_00_u03c3_1988_, lean_object* v_00_u03c3_1989_, lean_object* v_00_u03b1_1990_, lean_object* v_00_u03b2_1991_, lean_object* v_f_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1992_, v_x_1993_, v_x_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1996_, lean_object* v_x_1997_, lean_object* v_x_1998_, lean_object* v_x_1999_, lean_object* v_x_2000_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1997_, v_x_1998_, v_x_1999_, v_x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2002_, lean_object* v_00_u03b2_2003_, lean_object* v_00_u03c3_2004_, lean_object* v_00_u03c3_2005_, lean_object* v_f_2006_, lean_object* v_as_2007_, size_t v_i_2008_, size_t v_stop_2009_, lean_object* v_b_2010_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_2006_, v_as_2007_, v_i_2008_, v_stop_2009_, v_b_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2012_, lean_object* v_00_u03b2_2013_, lean_object* v_00_u03c3_2014_, lean_object* v_00_u03c3_2015_, lean_object* v_f_2016_, lean_object* v_as_2017_, lean_object* v_i_2018_, lean_object* v_stop_2019_, lean_object* v_b_2020_){
_start:
{
size_t v_i_boxed_2021_; size_t v_stop_boxed_2022_; lean_object* v_res_2023_; 
v_i_boxed_2021_ = lean_unbox_usize(v_i_2018_);
lean_dec(v_i_2018_);
v_stop_boxed_2022_ = lean_unbox_usize(v_stop_2019_);
lean_dec(v_stop_2019_);
v_res_2023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2012_, v_00_u03b2_2013_, v_00_u03c3_2014_, v_00_u03c3_2015_, v_f_2016_, v_as_2017_, v_i_boxed_2021_, v_stop_boxed_2022_, v_b_2020_);
lean_dec_ref(v_as_2017_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03c3_2024_, lean_object* v_00_u03c3_2025_, lean_object* v_00_u03b1_2026_, lean_object* v_00_u03b2_2027_, lean_object* v_f_2028_, lean_object* v_keys_2029_, lean_object* v_vals_2030_, lean_object* v_heq_2031_, lean_object* v_i_2032_, lean_object* v_acc_2033_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_2028_, v_keys_2029_, v_vals_2030_, v_i_2032_, v_acc_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03c3_2035_, lean_object* v_00_u03c3_2036_, lean_object* v_00_u03b1_2037_, lean_object* v_00_u03b2_2038_, lean_object* v_f_2039_, lean_object* v_keys_2040_, lean_object* v_vals_2041_, lean_object* v_heq_2042_, lean_object* v_i_2043_, lean_object* v_acc_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(v_00_u03c3_2035_, v_00_u03c3_2036_, v_00_u03b1_2037_, v_00_u03b2_2038_, v_f_2039_, v_keys_2040_, v_vals_2041_, v_heq_2042_, v_i_2043_, v_acc_2044_);
lean_dec_ref(v_vals_2041_);
lean_dec_ref(v_keys_2040_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(lean_object* v___x_2046_, lean_object* v___x_2047_, lean_object* v_x_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = lean_array_get_borrowed(v___x_2046_, v___x_2047_, v_x_2048_);
lean_inc(v___x_2049_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed(lean_object* v___x_2050_, lean_object* v___x_2051_, lean_object* v_x_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(v___x_2050_, v___x_2051_, v_x_2052_);
lean_dec(v_x_2052_);
lean_dec_ref(v___x_2051_);
lean_dec(v___x_2050_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(lean_object* v___x_2054_, size_t v_sz_2055_, size_t v_i_2056_, lean_object* v_bs_2057_){
_start:
{
uint8_t v___x_2058_; 
v___x_2058_ = lean_usize_dec_lt(v_i_2056_, v_sz_2055_);
if (v___x_2058_ == 0)
{
return v_bs_2057_;
}
else
{
lean_object* v_v_2059_; lean_object* v___x_2060_; lean_object* v_bs_x27_2061_; lean_object* v___y_2063_; 
v_v_2059_ = lean_array_uget(v_bs_2057_, v_i_2056_);
v___x_2060_ = lean_unsigned_to_nat(0u);
v_bs_x27_2061_ = lean_array_uset(v_bs_2057_, v_i_2056_, v___x_2060_);
if (lean_obj_tag(v_v_2059_) == 0)
{
v___y_2063_ = v_v_2059_;
goto v___jp_2062_;
}
else
{
lean_object* v_val_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2076_; 
v_val_2068_ = lean_ctor_get(v_v_2059_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_v_2059_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2070_ = v_v_2059_;
v_isShared_2071_ = v_isSharedCheck_2076_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_val_2068_);
lean_dec(v_v_2059_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2076_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2072_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_val_2068_, v___x_2054_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2072_);
v___x_2074_ = v___x_2070_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
v___y_2063_ = v___x_2074_;
goto v___jp_2062_;
}
}
}
v___jp_2062_:
{
size_t v___x_2064_; size_t v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = ((size_t)1ULL);
v___x_2065_ = lean_usize_add(v_i_2056_, v___x_2064_);
v___x_2066_ = lean_array_uset(v_bs_x27_2061_, v_i_2056_, v___y_2063_);
v_i_2056_ = v___x_2065_;
v_bs_2057_ = v___x_2066_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13___boxed(lean_object* v___x_2077_, lean_object* v_sz_2078_, lean_object* v_i_2079_, lean_object* v_bs_2080_){
_start:
{
size_t v_sz_boxed_2081_; size_t v_i_boxed_2082_; lean_object* v_res_2083_; 
v_sz_boxed_2081_ = lean_unbox_usize(v_sz_2078_);
lean_dec(v_sz_2078_);
v_i_boxed_2082_ = lean_unbox_usize(v_i_2079_);
lean_dec(v_i_2079_);
v_res_2083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(v___x_2077_, v_sz_boxed_2081_, v_i_boxed_2082_, v_bs_2080_);
lean_dec_ref(v___x_2077_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17(lean_object* v___x_2084_, size_t v_sz_2085_, size_t v_i_2086_, lean_object* v_bs_2087_){
_start:
{
uint8_t v___x_2088_; 
v___x_2088_ = lean_usize_dec_lt(v_i_2086_, v_sz_2085_);
if (v___x_2088_ == 0)
{
return v_bs_2087_;
}
else
{
lean_object* v_v_2089_; lean_object* v___x_2090_; lean_object* v_bs_x27_2091_; lean_object* v___x_2092_; size_t v___x_2093_; size_t v___x_2094_; lean_object* v___x_2095_; 
v_v_2089_ = lean_array_uget(v_bs_2087_, v_i_2086_);
v___x_2090_ = lean_unsigned_to_nat(0u);
v_bs_x27_2091_ = lean_array_uset(v_bs_2087_, v_i_2086_, v___x_2090_);
v___x_2092_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(v___x_2084_, v_v_2089_);
v___x_2093_ = ((size_t)1ULL);
v___x_2094_ = lean_usize_add(v_i_2086_, v___x_2093_);
v___x_2095_ = lean_array_uset(v_bs_x27_2091_, v_i_2086_, v___x_2092_);
v_i_2086_ = v___x_2094_;
v_bs_2087_ = v___x_2095_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(lean_object* v___x_2097_, lean_object* v_x_2098_){
_start:
{
if (lean_obj_tag(v_x_2098_) == 0)
{
lean_object* v_cs_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2109_; 
v_cs_2099_ = lean_ctor_get(v_x_2098_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_x_2098_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2101_ = v_x_2098_;
v_isShared_2102_ = v_isSharedCheck_2109_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_cs_2099_);
lean_dec(v_x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2109_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
size_t v_sz_2103_; size_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2107_; 
v_sz_2103_ = lean_array_size(v_cs_2099_);
v___x_2104_ = ((size_t)0ULL);
v___x_2105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17(v___x_2097_, v_sz_2103_, v___x_2104_, v_cs_2099_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2105_);
v___x_2107_ = v___x_2101_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
else
{
lean_object* v_vs_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2120_; 
v_vs_2110_ = lean_ctor_get(v_x_2098_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_x_2098_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2112_ = v_x_2098_;
v_isShared_2113_ = v_isSharedCheck_2120_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_vs_2110_);
lean_dec(v_x_2098_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2120_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
size_t v_sz_2114_; size_t v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
v_sz_2114_ = lean_array_size(v_vs_2110_);
v___x_2115_ = ((size_t)0ULL);
v___x_2116_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(v___x_2097_, v_sz_2114_, v___x_2115_, v_vs_2110_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___x_2116_);
v___x_2118_ = v___x_2112_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12___boxed(lean_object* v___x_2121_, lean_object* v_x_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(v___x_2121_, v_x_2122_);
lean_dec_ref(v___x_2121_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17___boxed(lean_object* v___x_2124_, lean_object* v_sz_2125_, lean_object* v_i_2126_, lean_object* v_bs_2127_){
_start:
{
size_t v_sz_boxed_2128_; size_t v_i_boxed_2129_; lean_object* v_res_2130_; 
v_sz_boxed_2128_ = lean_unbox_usize(v_sz_2125_);
lean_dec(v_sz_2125_);
v_i_boxed_2129_ = lean_unbox_usize(v_i_2126_);
lean_dec(v_i_2126_);
v_res_2130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17(v___x_2124_, v_sz_boxed_2128_, v_i_boxed_2129_, v_bs_2127_);
lean_dec_ref(v___x_2124_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(lean_object* v___x_2131_, lean_object* v_t_2132_){
_start:
{
lean_object* v_root_2133_; lean_object* v_tail_2134_; lean_object* v_size_2135_; size_t v_shift_2136_; lean_object* v_tailOff_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2148_; 
v_root_2133_ = lean_ctor_get(v_t_2132_, 0);
v_tail_2134_ = lean_ctor_get(v_t_2132_, 1);
v_size_2135_ = lean_ctor_get(v_t_2132_, 2);
v_shift_2136_ = lean_ctor_get_usize(v_t_2132_, 4);
v_tailOff_2137_ = lean_ctor_get(v_t_2132_, 3);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_t_2132_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2139_ = v_t_2132_;
v_isShared_2140_ = v_isSharedCheck_2148_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_tailOff_2137_);
lean_inc(v_size_2135_);
lean_inc(v_tail_2134_);
lean_inc(v_root_2133_);
lean_dec(v_t_2132_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2148_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; size_t v_sz_2142_; size_t v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2146_; 
v___x_2141_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(v___x_2131_, v_root_2133_);
v_sz_2142_ = lean_array_size(v_tail_2134_);
v___x_2143_ = ((size_t)0ULL);
v___x_2144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(v___x_2131_, v_sz_2142_, v___x_2143_, v_tail_2134_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 1, v___x_2144_);
lean_ctor_set(v___x_2139_, 0, v___x_2141_);
v___x_2146_ = v___x_2139_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v___x_2144_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v_size_2135_);
lean_ctor_set(v_reuseFailAlloc_2147_, 3, v_tailOff_2137_);
lean_ctor_set_usize(v_reuseFailAlloc_2147_, 4, v_shift_2136_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5___boxed(lean_object* v___x_2149_, lean_object* v_t_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(v___x_2149_, v_t_2150_);
lean_dec_ref(v___x_2149_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17(size_t v_sz_2152_, size_t v_i_2153_, lean_object* v_bs_2154_){
_start:
{
uint8_t v___x_2155_; 
v___x_2155_ = lean_usize_dec_lt(v_i_2153_, v_sz_2152_);
if (v___x_2155_ == 0)
{
return v_bs_2154_;
}
else
{
lean_object* v___x_2156_; lean_object* v_bs_x27_2157_; lean_object* v___x_2158_; size_t v___x_2159_; size_t v___x_2160_; lean_object* v___x_2161_; 
v___x_2156_ = lean_unsigned_to_nat(0u);
v_bs_x27_2157_ = lean_array_uset(v_bs_2154_, v_i_2153_, v___x_2156_);
v___x_2158_ = lean_box(1);
v___x_2159_ = ((size_t)1ULL);
v___x_2160_ = lean_usize_add(v_i_2153_, v___x_2159_);
v___x_2161_ = lean_array_uset(v_bs_x27_2157_, v_i_2153_, v___x_2158_);
v_i_2153_ = v___x_2160_;
v_bs_2154_ = v___x_2161_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17___boxed(lean_object* v_sz_2163_, lean_object* v_i_2164_, lean_object* v_bs_2165_){
_start:
{
size_t v_sz_boxed_2166_; size_t v_i_boxed_2167_; lean_object* v_res_2168_; 
v_sz_boxed_2166_ = lean_unbox_usize(v_sz_2163_);
lean_dec(v_sz_2163_);
v_i_boxed_2167_ = lean_unbox_usize(v_i_2164_);
lean_dec(v_i_2164_);
v_res_2168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17(v_sz_boxed_2166_, v_i_boxed_2167_, v_bs_2165_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22(size_t v_sz_2169_, size_t v_i_2170_, lean_object* v_bs_2171_){
_start:
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_usize_dec_lt(v_i_2170_, v_sz_2169_);
if (v___x_2172_ == 0)
{
return v_bs_2171_;
}
else
{
lean_object* v_v_2173_; lean_object* v___x_2174_; lean_object* v_bs_x27_2175_; lean_object* v___x_2176_; size_t v___x_2177_; size_t v___x_2178_; lean_object* v___x_2179_; 
v_v_2173_ = lean_array_uget(v_bs_2171_, v_i_2170_);
v___x_2174_ = lean_unsigned_to_nat(0u);
v_bs_x27_2175_ = lean_array_uset(v_bs_2171_, v_i_2170_, v___x_2174_);
v___x_2176_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16(v_v_2173_);
v___x_2177_ = ((size_t)1ULL);
v___x_2178_ = lean_usize_add(v_i_2170_, v___x_2177_);
v___x_2179_ = lean_array_uset(v_bs_x27_2175_, v_i_2170_, v___x_2176_);
v_i_2170_ = v___x_2178_;
v_bs_2171_ = v___x_2179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16(lean_object* v_x_2181_){
_start:
{
if (lean_obj_tag(v_x_2181_) == 0)
{
lean_object* v_cs_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2192_; 
v_cs_2182_ = lean_ctor_get(v_x_2181_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_x_2181_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2184_ = v_x_2181_;
v_isShared_2185_ = v_isSharedCheck_2192_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_cs_2182_);
lean_dec(v_x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2192_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
size_t v_sz_2186_; size_t v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2190_; 
v_sz_2186_ = lean_array_size(v_cs_2182_);
v___x_2187_ = ((size_t)0ULL);
v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22(v_sz_2186_, v___x_2187_, v_cs_2182_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v___x_2188_);
v___x_2190_ = v___x_2184_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
else
{
lean_object* v_vs_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2203_; 
v_vs_2193_ = lean_ctor_get(v_x_2181_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_x_2181_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2195_ = v_x_2181_;
v_isShared_2196_ = v_isSharedCheck_2203_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_vs_2193_);
lean_dec(v_x_2181_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2203_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
size_t v_sz_2197_; size_t v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
v_sz_2197_ = lean_array_size(v_vs_2193_);
v___x_2198_ = ((size_t)0ULL);
v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17(v_sz_2197_, v___x_2198_, v_vs_2193_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2199_);
v___x_2201_ = v___x_2195_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22___boxed(lean_object* v_sz_2204_, lean_object* v_i_2205_, lean_object* v_bs_2206_){
_start:
{
size_t v_sz_boxed_2207_; size_t v_i_boxed_2208_; lean_object* v_res_2209_; 
v_sz_boxed_2207_ = lean_unbox_usize(v_sz_2204_);
lean_dec(v_sz_2204_);
v_i_boxed_2208_ = lean_unbox_usize(v_i_2205_);
lean_dec(v_i_2205_);
v_res_2209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22(v_sz_boxed_2207_, v_i_boxed_2208_, v_bs_2206_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(lean_object* v_t_2210_){
_start:
{
lean_object* v_root_2211_; lean_object* v_tail_2212_; lean_object* v_size_2213_; size_t v_shift_2214_; lean_object* v_tailOff_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2226_; 
v_root_2211_ = lean_ctor_get(v_t_2210_, 0);
v_tail_2212_ = lean_ctor_get(v_t_2210_, 1);
v_size_2213_ = lean_ctor_get(v_t_2210_, 2);
v_shift_2214_ = lean_ctor_get_usize(v_t_2210_, 4);
v_tailOff_2215_ = lean_ctor_get(v_t_2210_, 3);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_t_2210_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2217_ = v_t_2210_;
v_isShared_2218_ = v_isSharedCheck_2226_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_tailOff_2215_);
lean_inc(v_size_2213_);
lean_inc(v_tail_2212_);
lean_inc(v_root_2211_);
lean_dec(v_t_2210_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2226_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; size_t v_sz_2220_; size_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2219_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16(v_root_2211_);
v_sz_2220_ = lean_array_size(v_tail_2212_);
v___x_2221_ = ((size_t)0ULL);
v___x_2222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17(v_sz_2220_, v___x_2221_, v_tail_2212_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v___x_2222_);
lean_ctor_set(v___x_2217_, 0, v___x_2219_);
v___x_2224_ = v___x_2217_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_size_2213_);
lean_ctor_set(v_reuseFailAlloc_2225_, 3, v_tailOff_2215_);
lean_ctor_set_usize(v_reuseFailAlloc_2225_, 4, v_shift_2214_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(lean_object* v___x_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_){
_start:
{
if (lean_obj_tag(v_a_2228_) == 0)
{
lean_object* v___x_2230_; 
v___x_2230_ = l_List_reverse___redArg(v_a_2229_);
return v___x_2230_;
}
else
{
lean_object* v_head_2231_; lean_object* v_tail_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2242_; 
v_head_2231_ = lean_ctor_get(v_a_2228_, 0);
v_tail_2232_ = lean_ctor_get(v_a_2228_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_a_2228_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2234_ = v_a_2228_;
v_isShared_2235_ = v_isSharedCheck_2242_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_tail_2232_);
lean_inc(v_head_2231_);
lean_dec(v_a_2228_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2242_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2236_ = lean_unsigned_to_nat(0u);
v___x_2237_ = lean_array_get_borrowed(v___x_2236_, v___x_2227_, v_head_2231_);
lean_dec(v_head_2231_);
lean_inc(v___x_2237_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 1, v_a_2229_);
lean_ctor_set(v___x_2234_, 0, v___x_2237_);
v___x_2239_ = v___x_2234_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_a_2229_);
v___x_2239_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
v_a_2228_ = v_tail_2232_;
v_a_2229_ = v___x_2239_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6___boxed(lean_object* v___x_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(v___x_2243_, v_a_2244_, v_a_2245_);
lean_dec_ref(v___x_2243_);
return v_res_2246_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2247_ = lean_unsigned_to_nat(32u);
v___x_2248_ = lean_mk_empty_array_with_capacity(v___x_2247_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
return v___x_2249_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__1(void){
_start:
{
size_t v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2250_ = ((size_t)5ULL);
v___x_2251_ = lean_unsigned_to_nat(0u);
v___x_2252_ = lean_unsigned_to_nat(32u);
v___x_2253_ = lean_mk_empty_array_with_capacity(v___x_2252_);
v___x_2254_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__0);
v___x_2255_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
lean_ctor_set(v___x_2255_, 1, v___x_2253_);
lean_ctor_set(v___x_2255_, 2, v___x_2251_);
lean_ctor_set(v___x_2255_, 3, v___x_2251_);
lean_ctor_set_usize(v___x_2255_, 4, v___x_2250_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10(size_t v_sz_2256_, size_t v_i_2257_, lean_object* v_bs_2258_){
_start:
{
uint8_t v___x_2259_; 
v___x_2259_ = lean_usize_dec_lt(v_i_2257_, v_sz_2256_);
if (v___x_2259_ == 0)
{
return v_bs_2258_;
}
else
{
lean_object* v___x_2260_; lean_object* v_bs_x27_2261_; lean_object* v___x_2262_; size_t v___x_2263_; size_t v___x_2264_; lean_object* v___x_2265_; 
v___x_2260_ = lean_unsigned_to_nat(0u);
v_bs_x27_2261_ = lean_array_uset(v_bs_2258_, v_i_2257_, v___x_2260_);
v___x_2262_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__1);
v___x_2263_ = ((size_t)1ULL);
v___x_2264_ = lean_usize_add(v_i_2257_, v___x_2263_);
v___x_2265_ = lean_array_uset(v_bs_x27_2261_, v_i_2257_, v___x_2262_);
v_i_2257_ = v___x_2264_;
v_bs_2258_ = v___x_2265_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___boxed(lean_object* v_sz_2267_, lean_object* v_i_2268_, lean_object* v_bs_2269_){
_start:
{
size_t v_sz_boxed_2270_; size_t v_i_boxed_2271_; lean_object* v_res_2272_; 
v_sz_boxed_2270_ = lean_unbox_usize(v_sz_2267_);
lean_dec(v_sz_2267_);
v_i_boxed_2271_ = lean_unbox_usize(v_i_2268_);
lean_dec(v_i_2268_);
v_res_2272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10(v_sz_boxed_2270_, v_i_boxed_2271_, v_bs_2269_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13(size_t v_sz_2273_, size_t v_i_2274_, lean_object* v_bs_2275_){
_start:
{
uint8_t v___x_2276_; 
v___x_2276_ = lean_usize_dec_lt(v_i_2274_, v_sz_2273_);
if (v___x_2276_ == 0)
{
return v_bs_2275_;
}
else
{
lean_object* v_v_2277_; lean_object* v___x_2278_; lean_object* v_bs_x27_2279_; lean_object* v___x_2280_; size_t v___x_2281_; size_t v___x_2282_; lean_object* v___x_2283_; 
v_v_2277_ = lean_array_uget(v_bs_2275_, v_i_2274_);
v___x_2278_ = lean_unsigned_to_nat(0u);
v_bs_x27_2279_ = lean_array_uset(v_bs_2275_, v_i_2274_, v___x_2278_);
v___x_2280_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9(v_v_2277_);
v___x_2281_ = ((size_t)1ULL);
v___x_2282_ = lean_usize_add(v_i_2274_, v___x_2281_);
v___x_2283_ = lean_array_uset(v_bs_x27_2279_, v_i_2274_, v___x_2280_);
v_i_2274_ = v___x_2282_;
v_bs_2275_ = v___x_2283_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9(lean_object* v_x_2285_){
_start:
{
if (lean_obj_tag(v_x_2285_) == 0)
{
lean_object* v_cs_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2296_; 
v_cs_2286_ = lean_ctor_get(v_x_2285_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v_x_2285_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2288_ = v_x_2285_;
v_isShared_2289_ = v_isSharedCheck_2296_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_cs_2286_);
lean_dec(v_x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2296_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
size_t v_sz_2290_; size_t v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
v_sz_2290_ = lean_array_size(v_cs_2286_);
v___x_2291_ = ((size_t)0ULL);
v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13(v_sz_2290_, v___x_2291_, v_cs_2286_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v___x_2292_);
v___x_2294_ = v___x_2288_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
else
{
lean_object* v_vs_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2307_; 
v_vs_2297_ = lean_ctor_get(v_x_2285_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v_x_2285_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2299_ = v_x_2285_;
v_isShared_2300_ = v_isSharedCheck_2307_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_vs_2297_);
lean_dec(v_x_2285_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2307_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
size_t v_sz_2301_; size_t v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2305_; 
v_sz_2301_ = lean_array_size(v_vs_2297_);
v___x_2302_ = ((size_t)0ULL);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10(v_sz_2301_, v___x_2302_, v_vs_2297_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2303_);
v___x_2305_ = v___x_2299_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13___boxed(lean_object* v_sz_2308_, lean_object* v_i_2309_, lean_object* v_bs_2310_){
_start:
{
size_t v_sz_boxed_2311_; size_t v_i_boxed_2312_; lean_object* v_res_2313_; 
v_sz_boxed_2311_ = lean_unbox_usize(v_sz_2308_);
lean_dec(v_sz_2308_);
v_i_boxed_2312_ = lean_unbox_usize(v_i_2309_);
lean_dec(v_i_2309_);
v_res_2313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13(v_sz_boxed_2311_, v_i_boxed_2312_, v_bs_2310_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(lean_object* v_t_2314_){
_start:
{
lean_object* v_root_2315_; lean_object* v_tail_2316_; lean_object* v_size_2317_; size_t v_shift_2318_; lean_object* v_tailOff_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2330_; 
v_root_2315_ = lean_ctor_get(v_t_2314_, 0);
v_tail_2316_ = lean_ctor_get(v_t_2314_, 1);
v_size_2317_ = lean_ctor_get(v_t_2314_, 2);
v_shift_2318_ = lean_ctor_get_usize(v_t_2314_, 4);
v_tailOff_2319_ = lean_ctor_get(v_t_2314_, 3);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_t_2314_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2321_ = v_t_2314_;
v_isShared_2322_ = v_isSharedCheck_2330_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_tailOff_2319_);
lean_inc(v_size_2317_);
lean_inc(v_tail_2316_);
lean_inc(v_root_2315_);
lean_dec(v_t_2314_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2330_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; size_t v_sz_2324_; size_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2323_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9(v_root_2315_);
v_sz_2324_ = lean_array_size(v_tail_2316_);
v___x_2325_ = ((size_t)0ULL);
v___x_2326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10(v_sz_2324_, v___x_2325_, v_tail_2316_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 1, v___x_2326_);
lean_ctor_set(v___x_2321_, 0, v___x_2323_);
v___x_2328_ = v___x_2321_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2323_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v___x_2326_);
lean_ctor_set(v_reuseFailAlloc_2329_, 2, v_size_2317_);
lean_ctor_set(v_reuseFailAlloc_2329_, 3, v_tailOff_2319_);
lean_ctor_set_usize(v_reuseFailAlloc_2329_, 4, v_shift_2318_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__0(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = lean_unsigned_to_nat(32u);
v___x_2332_ = lean_mk_empty_array_with_capacity(v___x_2331_);
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
return v___x_2333_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__1(void){
_start:
{
size_t v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2334_ = ((size_t)5ULL);
v___x_2335_ = lean_unsigned_to_nat(0u);
v___x_2336_ = lean_unsigned_to_nat(32u);
v___x_2337_ = lean_mk_empty_array_with_capacity(v___x_2336_);
v___x_2338_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__0);
v___x_2339_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
lean_ctor_set(v___x_2339_, 1, v___x_2337_);
lean_ctor_set(v___x_2339_, 2, v___x_2335_);
lean_ctor_set(v___x_2339_, 3, v___x_2335_);
lean_ctor_set_usize(v___x_2339_, 4, v___x_2334_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(size_t v_sz_2340_, size_t v_i_2341_, lean_object* v_bs_2342_){
_start:
{
uint8_t v___x_2343_; 
v___x_2343_ = lean_usize_dec_lt(v_i_2341_, v_sz_2340_);
if (v___x_2343_ == 0)
{
return v_bs_2342_;
}
else
{
lean_object* v___x_2344_; lean_object* v_bs_x27_2345_; lean_object* v___x_2346_; size_t v___x_2347_; size_t v___x_2348_; lean_object* v___x_2349_; 
v___x_2344_ = lean_unsigned_to_nat(0u);
v_bs_x27_2345_ = lean_array_uset(v_bs_2342_, v_i_2341_, v___x_2344_);
v___x_2346_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__1);
v___x_2347_ = ((size_t)1ULL);
v___x_2348_ = lean_usize_add(v_i_2341_, v___x_2347_);
v___x_2349_ = lean_array_uset(v_bs_x27_2345_, v_i_2341_, v___x_2346_);
v_i_2341_ = v___x_2348_;
v_bs_2342_ = v___x_2349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___boxed(lean_object* v_sz_2351_, lean_object* v_i_2352_, lean_object* v_bs_2353_){
_start:
{
size_t v_sz_boxed_2354_; size_t v_i_boxed_2355_; lean_object* v_res_2356_; 
v_sz_boxed_2354_ = lean_unbox_usize(v_sz_2351_);
lean_dec(v_sz_2351_);
v_i_boxed_2355_ = lean_unbox_usize(v_i_2352_);
lean_dec(v_i_2352_);
v_res_2356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(v_sz_boxed_2354_, v_i_boxed_2355_, v_bs_2353_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9(size_t v_sz_2357_, size_t v_i_2358_, lean_object* v_bs_2359_){
_start:
{
uint8_t v___x_2360_; 
v___x_2360_ = lean_usize_dec_lt(v_i_2358_, v_sz_2357_);
if (v___x_2360_ == 0)
{
return v_bs_2359_;
}
else
{
lean_object* v_v_2361_; lean_object* v___x_2362_; lean_object* v_bs_x27_2363_; lean_object* v___x_2364_; size_t v___x_2365_; size_t v___x_2366_; lean_object* v___x_2367_; 
v_v_2361_ = lean_array_uget(v_bs_2359_, v_i_2358_);
v___x_2362_ = lean_unsigned_to_nat(0u);
v_bs_x27_2363_ = lean_array_uset(v_bs_2359_, v_i_2358_, v___x_2362_);
v___x_2364_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6(v_v_2361_);
v___x_2365_ = ((size_t)1ULL);
v___x_2366_ = lean_usize_add(v_i_2358_, v___x_2365_);
v___x_2367_ = lean_array_uset(v_bs_x27_2363_, v_i_2358_, v___x_2364_);
v_i_2358_ = v___x_2366_;
v_bs_2359_ = v___x_2367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6(lean_object* v_x_2369_){
_start:
{
if (lean_obj_tag(v_x_2369_) == 0)
{
lean_object* v_cs_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2380_; 
v_cs_2370_ = lean_ctor_get(v_x_2369_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_x_2369_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2372_ = v_x_2369_;
v_isShared_2373_ = v_isSharedCheck_2380_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_cs_2370_);
lean_dec(v_x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2380_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
size_t v_sz_2374_; size_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2378_; 
v_sz_2374_ = lean_array_size(v_cs_2370_);
v___x_2375_ = ((size_t)0ULL);
v___x_2376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9(v_sz_2374_, v___x_2375_, v_cs_2370_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2376_);
v___x_2378_ = v___x_2372_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
else
{
lean_object* v_vs_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2391_; 
v_vs_2381_ = lean_ctor_get(v_x_2369_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v_x_2369_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2383_ = v_x_2369_;
v_isShared_2384_ = v_isSharedCheck_2391_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_vs_2381_);
lean_dec(v_x_2369_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2391_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
size_t v_sz_2385_; size_t v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
v_sz_2385_ = lean_array_size(v_vs_2381_);
v___x_2386_ = ((size_t)0ULL);
v___x_2387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(v_sz_2385_, v___x_2386_, v_vs_2381_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2387_);
v___x_2389_ = v___x_2383_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9___boxed(lean_object* v_sz_2392_, lean_object* v_i_2393_, lean_object* v_bs_2394_){
_start:
{
size_t v_sz_boxed_2395_; size_t v_i_boxed_2396_; lean_object* v_res_2397_; 
v_sz_boxed_2395_ = lean_unbox_usize(v_sz_2392_);
lean_dec(v_sz_2392_);
v_i_boxed_2396_ = lean_unbox_usize(v_i_2393_);
lean_dec(v_i_2393_);
v_res_2397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9(v_sz_boxed_2395_, v_i_boxed_2396_, v_bs_2394_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(lean_object* v_t_2398_){
_start:
{
lean_object* v_root_2399_; lean_object* v_tail_2400_; lean_object* v_size_2401_; size_t v_shift_2402_; lean_object* v_tailOff_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2414_; 
v_root_2399_ = lean_ctor_get(v_t_2398_, 0);
v_tail_2400_ = lean_ctor_get(v_t_2398_, 1);
v_size_2401_ = lean_ctor_get(v_t_2398_, 2);
v_shift_2402_ = lean_ctor_get_usize(v_t_2398_, 4);
v_tailOff_2403_ = lean_ctor_get(v_t_2398_, 3);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_t_2398_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2405_ = v_t_2398_;
v_isShared_2406_ = v_isSharedCheck_2414_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_tailOff_2403_);
lean_inc(v_size_2401_);
lean_inc(v_tail_2400_);
lean_inc(v_root_2399_);
lean_dec(v_t_2398_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2414_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; size_t v_sz_2408_; size_t v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2412_; 
v___x_2407_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6(v_root_2399_);
v_sz_2408_ = lean_array_size(v_tail_2400_);
v___x_2409_ = ((size_t)0ULL);
v___x_2410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(v_sz_2408_, v___x_2409_, v_tail_2400_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 1, v___x_2410_);
lean_ctor_set(v___x_2405_, 0, v___x_2407_);
v___x_2412_ = v___x_2405_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2413_, 2, v_size_2401_);
lean_ctor_set(v_reuseFailAlloc_2413_, 3, v_tailOff_2403_);
lean_ctor_set_usize(v_reuseFailAlloc_2413_, 4, v_shift_2402_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4(size_t v_sz_2415_, size_t v_i_2416_, lean_object* v_bs_2417_){
_start:
{
uint8_t v___x_2418_; 
v___x_2418_ = lean_usize_dec_lt(v_i_2416_, v_sz_2415_);
if (v___x_2418_ == 0)
{
return v_bs_2417_;
}
else
{
lean_object* v___x_2419_; lean_object* v_bs_x27_2420_; lean_object* v___x_2421_; size_t v___x_2422_; size_t v___x_2423_; lean_object* v___x_2424_; 
v___x_2419_ = lean_unsigned_to_nat(0u);
v_bs_x27_2420_ = lean_array_uset(v_bs_2417_, v_i_2416_, v___x_2419_);
v___x_2421_ = lean_box(0);
v___x_2422_ = ((size_t)1ULL);
v___x_2423_ = lean_usize_add(v_i_2416_, v___x_2422_);
v___x_2424_ = lean_array_uset(v_bs_x27_2420_, v_i_2416_, v___x_2421_);
v_i_2416_ = v___x_2423_;
v_bs_2417_ = v___x_2424_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4___boxed(lean_object* v_sz_2426_, lean_object* v_i_2427_, lean_object* v_bs_2428_){
_start:
{
size_t v_sz_boxed_2429_; size_t v_i_boxed_2430_; lean_object* v_res_2431_; 
v_sz_boxed_2429_ = lean_unbox_usize(v_sz_2426_);
lean_dec(v_sz_2426_);
v_i_boxed_2430_ = lean_unbox_usize(v_i_2427_);
lean_dec(v_i_2427_);
v_res_2431_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4(v_sz_boxed_2429_, v_i_boxed_2430_, v_bs_2428_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5(size_t v_sz_2432_, size_t v_i_2433_, lean_object* v_bs_2434_){
_start:
{
uint8_t v___x_2435_; 
v___x_2435_ = lean_usize_dec_lt(v_i_2433_, v_sz_2432_);
if (v___x_2435_ == 0)
{
return v_bs_2434_;
}
else
{
lean_object* v_v_2436_; lean_object* v___x_2437_; lean_object* v_bs_x27_2438_; lean_object* v___x_2439_; size_t v___x_2440_; size_t v___x_2441_; lean_object* v___x_2442_; 
v_v_2436_ = lean_array_uget(v_bs_2434_, v_i_2433_);
v___x_2437_ = lean_unsigned_to_nat(0u);
v_bs_x27_2438_ = lean_array_uset(v_bs_2434_, v_i_2433_, v___x_2437_);
v___x_2439_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3(v_v_2436_);
v___x_2440_ = ((size_t)1ULL);
v___x_2441_ = lean_usize_add(v_i_2433_, v___x_2440_);
v___x_2442_ = lean_array_uset(v_bs_x27_2438_, v_i_2433_, v___x_2439_);
v_i_2433_ = v___x_2441_;
v_bs_2434_ = v___x_2442_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3(lean_object* v_x_2444_){
_start:
{
if (lean_obj_tag(v_x_2444_) == 0)
{
lean_object* v_cs_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2455_; 
v_cs_2445_ = lean_ctor_get(v_x_2444_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_x_2444_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2447_ = v_x_2444_;
v_isShared_2448_ = v_isSharedCheck_2455_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_cs_2445_);
lean_dec(v_x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2455_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
size_t v_sz_2449_; size_t v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2453_; 
v_sz_2449_ = lean_array_size(v_cs_2445_);
v___x_2450_ = ((size_t)0ULL);
v___x_2451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5(v_sz_2449_, v___x_2450_, v_cs_2445_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v___x_2451_);
v___x_2453_ = v___x_2447_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
else
{
lean_object* v_vs_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2466_; 
v_vs_2456_ = lean_ctor_get(v_x_2444_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v_x_2444_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2458_ = v_x_2444_;
v_isShared_2459_ = v_isSharedCheck_2466_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_vs_2456_);
lean_dec(v_x_2444_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2466_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
size_t v_sz_2460_; size_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
v_sz_2460_ = lean_array_size(v_vs_2456_);
v___x_2461_ = ((size_t)0ULL);
v___x_2462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4(v_sz_2460_, v___x_2461_, v_vs_2456_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2462_);
v___x_2464_ = v___x_2458_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_2467_, lean_object* v_i_2468_, lean_object* v_bs_2469_){
_start:
{
size_t v_sz_boxed_2470_; size_t v_i_boxed_2471_; lean_object* v_res_2472_; 
v_sz_boxed_2470_ = lean_unbox_usize(v_sz_2467_);
lean_dec(v_sz_2467_);
v_i_boxed_2471_ = lean_unbox_usize(v_i_2468_);
lean_dec(v_i_2468_);
v_res_2472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5(v_sz_boxed_2470_, v_i_boxed_2471_, v_bs_2469_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(lean_object* v_t_2473_){
_start:
{
lean_object* v_root_2474_; lean_object* v_tail_2475_; lean_object* v_size_2476_; size_t v_shift_2477_; lean_object* v_tailOff_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2489_; 
v_root_2474_ = lean_ctor_get(v_t_2473_, 0);
v_tail_2475_ = lean_ctor_get(v_t_2473_, 1);
v_size_2476_ = lean_ctor_get(v_t_2473_, 2);
v_shift_2477_ = lean_ctor_get_usize(v_t_2473_, 4);
v_tailOff_2478_ = lean_ctor_get(v_t_2473_, 3);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_t_2473_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2480_ = v_t_2473_;
v_isShared_2481_ = v_isSharedCheck_2489_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_tailOff_2478_);
lean_inc(v_size_2476_);
lean_inc(v_tail_2475_);
lean_inc(v_root_2474_);
lean_dec(v_t_2473_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2489_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; size_t v_sz_2483_; size_t v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2482_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3(v_root_2474_);
v_sz_2483_ = lean_array_size(v_tail_2475_);
v___x_2484_ = ((size_t)0ULL);
v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4(v_sz_2483_, v___x_2484_, v_tail_2475_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v___x_2485_);
lean_ctor_set(v___x_2480_, 0, v___x_2482_);
v___x_2487_ = v___x_2480_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2488_, 2, v_size_2476_);
lean_ctor_set(v_reuseFailAlloc_2488_, 3, v_tailOff_2478_);
lean_ctor_set_usize(v_reuseFailAlloc_2488_, 4, v_shift_2477_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg(lean_object* v_f_2490_, lean_object* v_as_2491_, lean_object* v_i_2492_, lean_object* v_acc_2493_){
_start:
{
lean_object* v___x_2494_; uint8_t v___x_2495_; 
v___x_2494_ = lean_array_get_size(v_as_2491_);
v___x_2495_ = lean_nat_dec_eq(v_i_2492_, v___x_2494_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2496_ = lean_array_fget_borrowed(v_as_2491_, v_i_2492_);
lean_inc(v_f_2490_);
lean_inc(v___x_2496_);
v___x_2497_ = lean_apply_1(v_f_2490_, v___x_2496_);
v___x_2498_ = lean_unsigned_to_nat(1u);
v___x_2499_ = lean_nat_add(v_i_2492_, v___x_2498_);
lean_dec(v_i_2492_);
v___x_2500_ = lean_array_push(v_acc_2493_, v___x_2497_);
v_i_2492_ = v___x_2499_;
v_acc_2493_ = v___x_2500_;
goto _start;
}
else
{
lean_dec(v_i_2492_);
lean_dec(v_f_2490_);
return v_acc_2493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg___boxed(lean_object* v_f_2502_, lean_object* v_as_2503_, lean_object* v_i_2504_, lean_object* v_acc_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg(v_f_2502_, v_as_2503_, v_i_2504_, v_acc_2505_);
lean_dec_ref(v_as_2503_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg(lean_object* v_f_2507_, lean_object* v_as_2508_){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2509_ = lean_unsigned_to_nat(0u);
v___x_2510_ = lean_array_get_size(v_as_2508_);
v___x_2511_ = lean_mk_empty_array_with_capacity(v___x_2510_);
v___x_2512_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg(v_f_2507_, v_as_2508_, v___x_2509_, v___x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg___boxed(lean_object* v_f_2513_, lean_object* v_as_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg(v_f_2513_, v_as_2514_);
lean_dec_ref(v_as_2514_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg(lean_object* v_f_2516_, size_t v_sz_2517_, size_t v_i_2518_, lean_object* v_bs_2519_){
_start:
{
uint8_t v___x_2520_; 
v___x_2520_ = lean_usize_dec_lt(v_i_2518_, v_sz_2517_);
if (v___x_2520_ == 0)
{
lean_dec(v_f_2516_);
return v_bs_2519_;
}
else
{
lean_object* v_v_2521_; lean_object* v___x_2522_; lean_object* v_bs_x27_2523_; lean_object* v___y_2525_; 
v_v_2521_ = lean_array_uget(v_bs_2519_, v_i_2518_);
v___x_2522_ = lean_unsigned_to_nat(0u);
v_bs_x27_2523_ = lean_array_uset(v_bs_2519_, v_i_2518_, v___x_2522_);
switch(lean_obj_tag(v_v_2521_))
{
case 0:
{
lean_object* v_key_2530_; lean_object* v_val_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2539_; 
v_key_2530_ = lean_ctor_get(v_v_2521_, 0);
v_val_2531_ = lean_ctor_get(v_v_2521_, 1);
v_isSharedCheck_2539_ = !lean_is_exclusive(v_v_2521_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2533_ = v_v_2521_;
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_val_2531_);
lean_inc(v_key_2530_);
lean_dec(v_v_2521_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
lean_inc(v_f_2516_);
v___x_2535_ = lean_apply_1(v_f_2516_, v_val_2531_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 1, v___x_2535_);
v___x_2537_ = v___x_2533_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_key_2530_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
v___y_2525_ = v___x_2537_;
goto v___jp_2524_;
}
}
}
case 1:
{
lean_object* v_node_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2548_; 
v_node_2540_ = lean_ctor_get(v_v_2521_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_v_2521_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2542_ = v_v_2521_;
v_isShared_2543_ = v_isSharedCheck_2548_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_node_2540_);
lean_dec(v_v_2521_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2548_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2544_; lean_object* v___x_2546_; 
lean_inc(v_f_2516_);
v___x_2544_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(v_f_2516_, v_node_2540_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v___x_2544_);
v___x_2546_ = v___x_2542_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2544_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
v___y_2525_ = v___x_2546_;
goto v___jp_2524_;
}
}
}
default: 
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_box(2);
v___y_2525_ = v___x_2549_;
goto v___jp_2524_;
}
}
v___jp_2524_:
{
size_t v___x_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = ((size_t)1ULL);
v___x_2527_ = lean_usize_add(v_i_2518_, v___x_2526_);
v___x_2528_ = lean_array_uset(v_bs_x27_2523_, v_i_2518_, v___y_2525_);
v_i_2518_ = v___x_2527_;
v_bs_2519_ = v___x_2528_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(lean_object* v_f_2550_, lean_object* v_n_2551_){
_start:
{
if (lean_obj_tag(v_n_2551_) == 0)
{
lean_object* v_es_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2562_; 
v_es_2552_ = lean_ctor_get(v_n_2551_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_n_2551_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2554_ = v_n_2551_;
v_isShared_2555_ = v_isSharedCheck_2562_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_es_2552_);
lean_dec(v_n_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2562_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
size_t v_sz_2556_; size_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2560_; 
v_sz_2556_ = lean_array_size(v_es_2552_);
v___x_2557_ = ((size_t)0ULL);
v___x_2558_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg(v_f_2550_, v_sz_2556_, v___x_2557_, v_es_2552_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v___x_2558_);
v___x_2560_ = v___x_2554_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_ks_2563_; lean_object* v_vs_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2572_; 
v_ks_2563_ = lean_ctor_get(v_n_2551_, 0);
v_vs_2564_ = lean_ctor_get(v_n_2551_, 1);
v_isSharedCheck_2572_ = !lean_is_exclusive(v_n_2551_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2566_ = v_n_2551_;
v_isShared_2567_ = v_isSharedCheck_2572_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_vs_2564_);
lean_inc(v_ks_2563_);
lean_dec(v_n_2551_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2572_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v_val_2568_; lean_object* v___x_2570_; 
v_val_2568_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg(v_f_2550_, v_vs_2564_);
lean_dec_ref(v_vs_2564_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 1, v_val_2568_);
v___x_2570_ = v___x_2566_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_ks_2563_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v_val_2568_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg___boxed(lean_object* v_f_2573_, lean_object* v_sz_2574_, lean_object* v_i_2575_, lean_object* v_bs_2576_){
_start:
{
size_t v_sz_boxed_2577_; size_t v_i_boxed_2578_; lean_object* v_res_2579_; 
v_sz_boxed_2577_ = lean_unbox_usize(v_sz_2574_);
lean_dec(v_sz_2574_);
v_i_boxed_2578_ = lean_unbox_usize(v_i_2575_);
lean_dec(v_i_2575_);
v_res_2579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg(v_f_2573_, v_sz_boxed_2577_, v_i_boxed_2578_, v_bs_2576_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg___lam__0(lean_object* v_f_2580_, lean_object* v_x_2581_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = lean_apply_1(v_f_2580_, v_x_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg(lean_object* v_pm_2583_, lean_object* v_f_2584_){
_start:
{
lean_object* v___f_2585_; lean_object* v___x_2586_; 
v___f_2585_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2585_, 0, v_f_2584_);
v___x_2586_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(v___f_2585_, v_pm_2583_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(lean_object* v___x_2587_, lean_object* v_a_2588_, lean_object* v___f_2589_, lean_object* v___x_2590_, lean_object* v___x_2591_, lean_object* v_s_2592_){
_start:
{
lean_object* v_vars_2593_; lean_object* v_varMap_2594_; lean_object* v_varsHistory_2595_; lean_object* v_natToIntMap_2596_; lean_object* v_natDef_2597_; lean_object* v_dvds_2598_; lean_object* v_lowers_2599_; lean_object* v_uppers_2600_; lean_object* v_diseqs_2601_; lean_object* v_elimEqs_2602_; lean_object* v_elimStack_2603_; lean_object* v_occurs_2604_; lean_object* v_assignment_2605_; lean_object* v_nextCnstrId_2606_; uint8_t v_caseSplits_2607_; lean_object* v_steps_2608_; lean_object* v_conflict_x3f_2609_; lean_object* v_divMod_2610_; uint8_t v_usedCommRing_2611_; lean_object* v_nonlinearOccs_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2634_; 
v_vars_2593_ = lean_ctor_get(v_s_2592_, 0);
v_varMap_2594_ = lean_ctor_get(v_s_2592_, 1);
v_varsHistory_2595_ = lean_ctor_get(v_s_2592_, 2);
v_natToIntMap_2596_ = lean_ctor_get(v_s_2592_, 3);
v_natDef_2597_ = lean_ctor_get(v_s_2592_, 4);
v_dvds_2598_ = lean_ctor_get(v_s_2592_, 5);
v_lowers_2599_ = lean_ctor_get(v_s_2592_, 6);
v_uppers_2600_ = lean_ctor_get(v_s_2592_, 7);
v_diseqs_2601_ = lean_ctor_get(v_s_2592_, 8);
v_elimEqs_2602_ = lean_ctor_get(v_s_2592_, 9);
v_elimStack_2603_ = lean_ctor_get(v_s_2592_, 10);
v_occurs_2604_ = lean_ctor_get(v_s_2592_, 11);
v_assignment_2605_ = lean_ctor_get(v_s_2592_, 12);
v_nextCnstrId_2606_ = lean_ctor_get(v_s_2592_, 13);
v_caseSplits_2607_ = lean_ctor_get_uint8(v_s_2592_, sizeof(void*)*19);
v_steps_2608_ = lean_ctor_get(v_s_2592_, 14);
v_conflict_x3f_2609_ = lean_ctor_get(v_s_2592_, 15);
v_divMod_2610_ = lean_ctor_get(v_s_2592_, 17);
v_usedCommRing_2611_ = lean_ctor_get_uint8(v_s_2592_, sizeof(void*)*19 + 1);
v_nonlinearOccs_2612_ = lean_ctor_get(v_s_2592_, 18);
v_isSharedCheck_2634_ = !lean_is_exclusive(v_s_2592_);
if (v_isSharedCheck_2634_ == 0)
{
lean_object* v_unused_2635_; 
v_unused_2635_ = lean_ctor_get(v_s_2592_, 16);
lean_dec(v_unused_2635_);
v___x_2614_ = v_s_2592_;
v_isShared_2615_ = v_isSharedCheck_2634_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_nonlinearOccs_2612_);
lean_inc(v_divMod_2610_);
lean_inc(v_conflict_x3f_2609_);
lean_inc(v_steps_2608_);
lean_inc(v_nextCnstrId_2606_);
lean_inc(v_assignment_2605_);
lean_inc(v_occurs_2604_);
lean_inc(v_elimStack_2603_);
lean_inc(v_elimEqs_2602_);
lean_inc(v_diseqs_2601_);
lean_inc(v_uppers_2600_);
lean_inc(v_lowers_2599_);
lean_inc(v_dvds_2598_);
lean_inc(v_natDef_2597_);
lean_inc(v_natToIntMap_2596_);
lean_inc(v_varsHistory_2595_);
lean_inc(v_varMap_2594_);
lean_inc(v_vars_2593_);
lean_dec(v_s_2592_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2634_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2632_; 
lean_inc_ref(v_a_2588_);
lean_inc_ref(v_vars_2593_);
v___x_2616_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2587_, v_vars_2593_, v_a_2588_);
lean_inc_ref(v___f_2589_);
lean_inc_ref(v_varMap_2594_);
v___x_2617_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg(v_varMap_2594_, v___f_2589_);
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v_vars_2593_);
lean_ctor_set(v___x_2618_, 1, v_varMap_2594_);
v___x_2619_ = l_Lean_PersistentArray_push___redArg(v_varsHistory_2595_, v___x_2618_);
v___x_2620_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg(v_natDef_2597_, v___f_2589_);
v___x_2621_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(v_dvds_2598_);
v___x_2622_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(v_lowers_2599_);
v___x_2623_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(v_uppers_2600_);
v___x_2624_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(v_diseqs_2601_);
v___x_2625_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2590_, v_elimEqs_2602_, v_a_2588_);
v___x_2626_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(v___x_2591_, v___x_2625_);
v___x_2627_ = lean_box(0);
v___x_2628_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(v___x_2591_, v_elimStack_2603_, v___x_2627_);
v___x_2629_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(v_occurs_2604_);
v___x_2630_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 16, v___x_2630_);
lean_ctor_set(v___x_2614_, 11, v___x_2629_);
lean_ctor_set(v___x_2614_, 10, v___x_2628_);
lean_ctor_set(v___x_2614_, 9, v___x_2626_);
lean_ctor_set(v___x_2614_, 8, v___x_2624_);
lean_ctor_set(v___x_2614_, 7, v___x_2623_);
lean_ctor_set(v___x_2614_, 6, v___x_2622_);
lean_ctor_set(v___x_2614_, 5, v___x_2621_);
lean_ctor_set(v___x_2614_, 4, v___x_2620_);
lean_ctor_set(v___x_2614_, 2, v___x_2619_);
lean_ctor_set(v___x_2614_, 1, v___x_2617_);
lean_ctor_set(v___x_2614_, 0, v___x_2616_);
v___x_2632_ = v___x_2614_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2616_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v___x_2617_);
lean_ctor_set(v_reuseFailAlloc_2633_, 2, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2633_, 3, v_natToIntMap_2596_);
lean_ctor_set(v_reuseFailAlloc_2633_, 4, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2633_, 5, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2633_, 6, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2633_, 7, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2633_, 8, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2633_, 9, v___x_2626_);
lean_ctor_set(v_reuseFailAlloc_2633_, 10, v___x_2628_);
lean_ctor_set(v_reuseFailAlloc_2633_, 11, v___x_2629_);
lean_ctor_set(v_reuseFailAlloc_2633_, 12, v_assignment_2605_);
lean_ctor_set(v_reuseFailAlloc_2633_, 13, v_nextCnstrId_2606_);
lean_ctor_set(v_reuseFailAlloc_2633_, 14, v_steps_2608_);
lean_ctor_set(v_reuseFailAlloc_2633_, 15, v_conflict_x3f_2609_);
lean_ctor_set(v_reuseFailAlloc_2633_, 16, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2633_, 17, v_divMod_2610_);
lean_ctor_set(v_reuseFailAlloc_2633_, 18, v_nonlinearOccs_2612_);
lean_ctor_set_uint8(v_reuseFailAlloc_2633_, sizeof(void*)*19, v_caseSplits_2607_);
lean_ctor_set_uint8(v_reuseFailAlloc_2633_, sizeof(void*)*19 + 1, v_usedCommRing_2611_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed(lean_object* v___x_2636_, lean_object* v_a_2637_, lean_object* v___f_2638_, lean_object* v___x_2639_, lean_object* v___x_2640_, lean_object* v_s_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(v___x_2636_, v_a_2637_, v___f_2638_, v___x_2639_, v___x_2640_, v_s_2641_);
lean_dec_ref(v___x_2640_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(lean_object* v___x_2643_, size_t v_sz_2644_, size_t v_i_2645_, lean_object* v_bs_2646_){
_start:
{
uint8_t v___x_2647_; 
v___x_2647_ = lean_usize_dec_lt(v_i_2645_, v_sz_2644_);
if (v___x_2647_ == 0)
{
return v_bs_2646_;
}
else
{
lean_object* v_v_2648_; lean_object* v___x_2649_; lean_object* v_bs_x27_2650_; lean_object* v___x_2651_; size_t v___x_2652_; size_t v___x_2653_; lean_object* v___x_2654_; 
v_v_2648_ = lean_array_uget(v_bs_2646_, v_i_2645_);
v___x_2649_ = lean_unsigned_to_nat(0u);
v_bs_x27_2650_ = lean_array_uset(v_bs_2646_, v_i_2645_, v___x_2649_);
v___x_2651_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_v_2648_, v___x_2643_);
v___x_2652_ = ((size_t)1ULL);
v___x_2653_ = lean_usize_add(v_i_2645_, v___x_2652_);
v___x_2654_ = lean_array_uset(v_bs_x27_2650_, v_i_2645_, v___x_2651_);
v_i_2645_ = v___x_2653_;
v_bs_2646_ = v___x_2654_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11___boxed(lean_object* v___x_2656_, lean_object* v_sz_2657_, lean_object* v_i_2658_, lean_object* v_bs_2659_){
_start:
{
size_t v_sz_boxed_2660_; size_t v_i_boxed_2661_; lean_object* v_res_2662_; 
v_sz_boxed_2660_ = lean_unbox_usize(v_sz_2657_);
lean_dec(v_sz_2657_);
v_i_boxed_2661_ = lean_unbox_usize(v_i_2658_);
lean_dec(v_i_2658_);
v_res_2662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v___x_2656_, v_sz_boxed_2660_, v_i_boxed_2661_, v_bs_2659_);
lean_dec_ref(v___x_2656_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(lean_object* v_as_2663_, size_t v_i_2664_, size_t v_stop_2665_, lean_object* v_b_2666_){
_start:
{
lean_object* v___y_2668_; uint8_t v___x_2672_; 
v___x_2672_ = lean_usize_dec_eq(v_i_2664_, v_stop_2665_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_array_uget_borrowed(v_as_2663_, v_i_2664_);
if (lean_obj_tag(v___x_2673_) == 0)
{
v___y_2668_ = v_b_2666_;
goto v___jp_2667_;
}
else
{
lean_object* v_val_2674_; lean_object* v___x_2675_; 
v_val_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_val_2674_);
v___x_2675_ = lean_array_push(v_b_2666_, v_val_2674_);
v___y_2668_ = v___x_2675_;
goto v___jp_2667_;
}
}
else
{
return v_b_2666_;
}
v___jp_2667_:
{
size_t v___x_2669_; size_t v___x_2670_; 
v___x_2669_ = ((size_t)1ULL);
v___x_2670_ = lean_usize_add(v_i_2664_, v___x_2669_);
v_i_2664_ = v___x_2670_;
v_b_2666_ = v___y_2668_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20___boxed(lean_object* v_as_2676_, lean_object* v_i_2677_, lean_object* v_stop_2678_, lean_object* v_b_2679_){
_start:
{
size_t v_i_boxed_2680_; size_t v_stop_boxed_2681_; lean_object* v_res_2682_; 
v_i_boxed_2680_ = lean_unbox_usize(v_i_2677_);
lean_dec(v_i_2677_);
v_stop_boxed_2681_ = lean_unbox_usize(v_stop_2678_);
lean_dec(v_stop_2678_);
v_res_2682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_as_2676_, v_i_boxed_2680_, v_stop_boxed_2681_, v_b_2679_);
lean_dec_ref(v_as_2676_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21(lean_object* v_x_2683_, lean_object* v_x_2684_){
_start:
{
if (lean_obj_tag(v_x_2683_) == 0)
{
lean_object* v_cs_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
v_cs_2685_ = lean_ctor_get(v_x_2683_, 0);
v___x_2686_ = lean_unsigned_to_nat(0u);
v___x_2687_ = lean_array_get_size(v_cs_2685_);
v___x_2688_ = lean_nat_dec_lt(v___x_2686_, v___x_2687_);
if (v___x_2688_ == 0)
{
return v_x_2684_;
}
else
{
size_t v___x_2689_; size_t v___x_2690_; lean_object* v___x_2691_; 
v___x_2689_ = ((size_t)0ULL);
v___x_2690_ = lean_usize_of_nat(v___x_2687_);
v___x_2691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26(v_cs_2685_, v___x_2689_, v___x_2690_, v_x_2684_);
return v___x_2691_;
}
}
else
{
lean_object* v_vs_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v_vs_2692_ = lean_ctor_get(v_x_2683_, 0);
v___x_2693_ = lean_unsigned_to_nat(0u);
v___x_2694_ = lean_array_get_size(v_vs_2692_);
v___x_2695_ = lean_nat_dec_lt(v___x_2693_, v___x_2694_);
if (v___x_2695_ == 0)
{
return v_x_2684_;
}
else
{
size_t v___x_2696_; size_t v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = ((size_t)0ULL);
v___x_2697_ = lean_usize_of_nat(v___x_2694_);
v___x_2698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_vs_2692_, v___x_2696_, v___x_2697_, v_x_2684_);
return v___x_2698_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26(lean_object* v_as_2699_, size_t v_i_2700_, size_t v_stop_2701_, lean_object* v_b_2702_){
_start:
{
uint8_t v___x_2703_; 
v___x_2703_ = lean_usize_dec_eq(v_i_2700_, v_stop_2701_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; lean_object* v___x_2705_; size_t v___x_2706_; size_t v___x_2707_; 
v___x_2704_ = lean_array_uget_borrowed(v_as_2699_, v_i_2700_);
v___x_2705_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21(v___x_2704_, v_b_2702_);
v___x_2706_ = ((size_t)1ULL);
v___x_2707_ = lean_usize_add(v_i_2700_, v___x_2706_);
v_i_2700_ = v___x_2707_;
v_b_2702_ = v___x_2705_;
goto _start;
}
else
{
return v_b_2702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26___boxed(lean_object* v_as_2709_, lean_object* v_i_2710_, lean_object* v_stop_2711_, lean_object* v_b_2712_){
_start:
{
size_t v_i_boxed_2713_; size_t v_stop_boxed_2714_; lean_object* v_res_2715_; 
v_i_boxed_2713_ = lean_unbox_usize(v_i_2710_);
lean_dec(v_i_2710_);
v_stop_boxed_2714_ = lean_unbox_usize(v_stop_2711_);
lean_dec(v_stop_2711_);
v_res_2715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26(v_as_2709_, v_i_boxed_2713_, v_stop_boxed_2714_, v_b_2712_);
lean_dec_ref(v_as_2709_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21___boxed(lean_object* v_x_2716_, lean_object* v_x_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21(v_x_2716_, v_x_2717_);
lean_dec_ref(v_x_2716_);
return v_res_2718_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0(void){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(lean_object* v_x_2720_, size_t v_x_2721_, size_t v_x_2722_, lean_object* v_x_2723_){
_start:
{
if (lean_obj_tag(v_x_2720_) == 0)
{
lean_object* v_cs_2724_; lean_object* v___x_2725_; size_t v___x_2726_; lean_object* v_j_2727_; lean_object* v___x_2728_; size_t v___x_2729_; size_t v___x_2730_; size_t v___x_2731_; size_t v___x_2732_; size_t v___x_2733_; size_t v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v_cs_2724_ = lean_ctor_get(v_x_2720_, 0);
v___x_2725_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0);
v___x_2726_ = lean_usize_shift_right(v_x_2721_, v_x_2722_);
v_j_2727_ = lean_usize_to_nat(v___x_2726_);
v___x_2728_ = lean_array_get_borrowed(v___x_2725_, v_cs_2724_, v_j_2727_);
v___x_2729_ = ((size_t)1ULL);
v___x_2730_ = lean_usize_shift_left(v___x_2729_, v_x_2722_);
v___x_2731_ = lean_usize_sub(v___x_2730_, v___x_2729_);
v___x_2732_ = lean_usize_land(v_x_2721_, v___x_2731_);
v___x_2733_ = ((size_t)5ULL);
v___x_2734_ = lean_usize_sub(v_x_2722_, v___x_2733_);
v___x_2735_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(v___x_2728_, v___x_2732_, v___x_2734_, v_x_2723_);
v___x_2736_ = lean_unsigned_to_nat(1u);
v___x_2737_ = lean_nat_add(v_j_2727_, v___x_2736_);
lean_dec(v_j_2727_);
v___x_2738_ = lean_array_get_size(v_cs_2724_);
v___x_2739_ = lean_nat_dec_lt(v___x_2737_, v___x_2738_);
if (v___x_2739_ == 0)
{
lean_dec(v___x_2737_);
return v___x_2735_;
}
else
{
size_t v___x_2740_; size_t v___x_2741_; lean_object* v___x_2742_; 
v___x_2740_ = lean_usize_of_nat(v___x_2737_);
lean_dec(v___x_2737_);
v___x_2741_ = lean_usize_of_nat(v___x_2738_);
v___x_2742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26(v_cs_2724_, v___x_2740_, v___x_2741_, v___x_2735_);
return v___x_2742_;
}
}
else
{
lean_object* v_vs_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; uint8_t v___x_2746_; 
v_vs_2743_ = lean_ctor_get(v_x_2720_, 0);
v___x_2744_ = lean_usize_to_nat(v_x_2721_);
v___x_2745_ = lean_array_get_size(v_vs_2743_);
v___x_2746_ = lean_nat_dec_lt(v___x_2744_, v___x_2745_);
if (v___x_2746_ == 0)
{
lean_dec(v___x_2744_);
return v_x_2723_;
}
else
{
size_t v___x_2747_; size_t v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = lean_usize_of_nat(v___x_2744_);
lean_dec(v___x_2744_);
v___x_2748_ = lean_usize_of_nat(v___x_2745_);
v___x_2749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_vs_2743_, v___x_2747_, v___x_2748_, v_x_2723_);
return v___x_2749_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___boxed(lean_object* v_x_2750_, lean_object* v_x_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_){
_start:
{
size_t v_x_96788__boxed_2754_; size_t v_x_96789__boxed_2755_; lean_object* v_res_2756_; 
v_x_96788__boxed_2754_ = lean_unbox_usize(v_x_2751_);
lean_dec(v_x_2751_);
v_x_96789__boxed_2755_ = lean_unbox_usize(v_x_2752_);
lean_dec(v_x_2752_);
v_res_2756_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(v_x_2750_, v_x_96788__boxed_2754_, v_x_96789__boxed_2755_, v_x_2753_);
lean_dec_ref(v_x_2750_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(lean_object* v_t_2757_, lean_object* v_init_2758_, lean_object* v_start_2759_){
_start:
{
lean_object* v___x_2760_; uint8_t v___x_2761_; 
v___x_2760_ = lean_unsigned_to_nat(0u);
v___x_2761_ = lean_nat_dec_eq(v_start_2759_, v___x_2760_);
if (v___x_2761_ == 0)
{
lean_object* v_root_2762_; lean_object* v_tail_2763_; size_t v_shift_2764_; lean_object* v_tailOff_2765_; uint8_t v___x_2766_; 
v_root_2762_ = lean_ctor_get(v_t_2757_, 0);
v_tail_2763_ = lean_ctor_get(v_t_2757_, 1);
v_shift_2764_ = lean_ctor_get_usize(v_t_2757_, 4);
v_tailOff_2765_ = lean_ctor_get(v_t_2757_, 3);
v___x_2766_ = lean_nat_dec_le(v_tailOff_2765_, v_start_2759_);
if (v___x_2766_ == 0)
{
size_t v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2767_ = lean_usize_of_nat(v_start_2759_);
v___x_2768_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(v_root_2762_, v___x_2767_, v_shift_2764_, v_init_2758_);
v___x_2769_ = lean_array_get_size(v_tail_2763_);
v___x_2770_ = lean_nat_dec_lt(v___x_2760_, v___x_2769_);
if (v___x_2770_ == 0)
{
return v___x_2768_;
}
else
{
size_t v___x_2771_; size_t v___x_2772_; lean_object* v___x_2773_; 
v___x_2771_ = ((size_t)0ULL);
v___x_2772_ = lean_usize_of_nat(v___x_2769_);
v___x_2773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_tail_2763_, v___x_2771_, v___x_2772_, v___x_2768_);
return v___x_2773_;
}
}
else
{
lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; 
v___x_2774_ = lean_nat_sub(v_start_2759_, v_tailOff_2765_);
v___x_2775_ = lean_array_get_size(v_tail_2763_);
v___x_2776_ = lean_nat_dec_lt(v___x_2774_, v___x_2775_);
if (v___x_2776_ == 0)
{
lean_dec(v___x_2774_);
return v_init_2758_;
}
else
{
size_t v___x_2777_; size_t v___x_2778_; lean_object* v___x_2779_; 
v___x_2777_ = lean_usize_of_nat(v___x_2774_);
lean_dec(v___x_2774_);
v___x_2778_ = lean_usize_of_nat(v___x_2775_);
v___x_2779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_tail_2763_, v___x_2777_, v___x_2778_, v_init_2758_);
return v___x_2779_;
}
}
}
else
{
lean_object* v_root_2780_; lean_object* v_tail_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v_root_2780_ = lean_ctor_get(v_t_2757_, 0);
v_tail_2781_ = lean_ctor_get(v_t_2757_, 1);
v___x_2782_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21(v_root_2780_, v_init_2758_);
v___x_2783_ = lean_array_get_size(v_tail_2781_);
v___x_2784_ = lean_nat_dec_lt(v___x_2760_, v___x_2783_);
if (v___x_2784_ == 0)
{
return v___x_2782_;
}
else
{
size_t v___x_2785_; size_t v___x_2786_; lean_object* v___x_2787_; 
v___x_2785_ = ((size_t)0ULL);
v___x_2786_ = lean_usize_of_nat(v___x_2783_);
v___x_2787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_tail_2781_, v___x_2785_, v___x_2786_, v___x_2782_);
return v___x_2787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8___boxed(lean_object* v_t_2788_, lean_object* v_init_2789_, lean_object* v_start_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_t_2788_, v_init_2789_, v_start_2790_);
lean_dec(v_start_2790_);
lean_dec_ref(v_t_2788_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(lean_object* v___x_2792_, size_t v_sz_2793_, size_t v_i_2794_, lean_object* v_bs_2795_){
_start:
{
uint8_t v___x_2796_; 
v___x_2796_ = lean_usize_dec_lt(v_i_2794_, v_sz_2793_);
if (v___x_2796_ == 0)
{
return v_bs_2795_;
}
else
{
lean_object* v_v_2797_; lean_object* v___x_2798_; lean_object* v_bs_x27_2799_; lean_object* v___x_2800_; size_t v___x_2801_; size_t v___x_2802_; lean_object* v___x_2803_; 
v_v_2797_ = lean_array_uget(v_bs_2795_, v_i_2794_);
v___x_2798_ = lean_unsigned_to_nat(0u);
v_bs_x27_2799_ = lean_array_uset(v_bs_2795_, v_i_2794_, v___x_2798_);
v___x_2800_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(v_v_2797_, v___x_2792_);
v___x_2801_ = ((size_t)1ULL);
v___x_2802_ = lean_usize_add(v_i_2794_, v___x_2801_);
v___x_2803_ = lean_array_uset(v_bs_x27_2799_, v_i_2794_, v___x_2800_);
v_i_2794_ = v___x_2802_;
v_bs_2795_ = v___x_2803_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9___boxed(lean_object* v___x_2805_, lean_object* v_sz_2806_, lean_object* v_i_2807_, lean_object* v_bs_2808_){
_start:
{
size_t v_sz_boxed_2809_; size_t v_i_boxed_2810_; lean_object* v_res_2811_; 
v_sz_boxed_2809_ = lean_unbox_usize(v_sz_2806_);
lean_dec(v_sz_2806_);
v_i_boxed_2810_ = lean_unbox_usize(v_i_2807_);
lean_dec(v_i_2807_);
v_res_2811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v___x_2805_, v_sz_boxed_2809_, v_i_boxed_2810_, v_bs_2808_);
lean_dec_ref(v___x_2805_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(lean_object* v_as_2812_, size_t v_sz_2813_, size_t v_i_2814_, lean_object* v_b_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
uint8_t v___x_2827_; 
v___x_2827_ = lean_usize_dec_lt(v_i_2814_, v_sz_2813_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; 
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v_b_2815_);
return v___x_2828_;
}
else
{
lean_object* v___x_2829_; lean_object* v_a_2830_; lean_object* v___x_2831_; 
v___x_2829_ = lean_box(0);
v_a_2830_ = lean_array_uget_borrowed(v_as_2812_, v_i_2814_);
lean_inc_ref(v___y_2824_);
lean_inc(v_a_2830_);
v___x_2831_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_a_2830_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
if (lean_obj_tag(v___x_2831_) == 0)
{
size_t v___x_2832_; size_t v___x_2833_; 
lean_dec_ref_known(v___x_2831_, 1);
v___x_2832_ = ((size_t)1ULL);
v___x_2833_ = lean_usize_add(v_i_2814_, v___x_2832_);
v_i_2814_ = v___x_2833_;
v_b_2815_ = v___x_2829_;
goto _start;
}
else
{
return v___x_2831_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14___boxed(lean_object* v_as_2835_, lean_object* v_sz_2836_, lean_object* v_i_2837_, lean_object* v_b_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
size_t v_sz_boxed_2850_; size_t v_i_boxed_2851_; lean_object* v_res_2852_; 
v_sz_boxed_2850_ = lean_unbox_usize(v_sz_2836_);
lean_dec(v_sz_2836_);
v_i_boxed_2851_ = lean_unbox_usize(v_i_2837_);
lean_dec(v_i_2837_);
v_res_2852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v_as_2835_, v_sz_boxed_2850_, v_i_boxed_2851_, v_b_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v_as_2835_);
return v_res_2852_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(lean_object* v___x_2853_, uint8_t v___x_2854_, lean_object* v_a_2855_, uint8_t v___x_2856_, lean_object* v_x_2857_){
_start:
{
if (lean_obj_tag(v_x_2857_) == 0)
{
uint8_t v___x_2858_; 
v___x_2858_ = 0;
return v___x_2858_;
}
else
{
lean_object* v_head_2859_; lean_object* v_tail_2860_; uint8_t v___y_2862_; lean_object* v___x_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; 
v_head_2859_ = lean_ctor_get(v_x_2857_, 0);
v_tail_2860_ = lean_ctor_get(v_x_2857_, 1);
v___x_2864_ = lean_unsigned_to_nat(0u);
v___x_2865_ = lean_array_get_borrowed(v___x_2864_, v___x_2853_, v_head_2859_);
v___x_2866_ = lean_nat_dec_eq(v___x_2865_, v_head_2859_);
if (v___x_2866_ == 0)
{
if (v___x_2854_ == 0)
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2867_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_2868_ = lean_unsigned_to_nat(1u);
v___x_2869_ = lean_array_get_borrowed(v___x_2867_, v_a_2855_, v_head_2859_);
v___x_2870_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_2869_);
v___x_2871_ = lean_nat_dec_lt(v___x_2868_, v___x_2870_);
lean_dec(v___x_2870_);
v___y_2862_ = v___x_2871_;
goto v___jp_2861_;
}
else
{
return v___x_2854_;
}
}
else
{
v___y_2862_ = v___x_2856_;
goto v___jp_2861_;
}
v___jp_2861_:
{
if (v___y_2862_ == 0)
{
v_x_2857_ = v_tail_2860_;
goto _start;
}
else
{
return v___y_2862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___boxed(lean_object* v___x_2872_, lean_object* v___x_2873_, lean_object* v_a_2874_, lean_object* v___x_2875_, lean_object* v_x_2876_){
_start:
{
uint8_t v___x_96961__boxed_2877_; uint8_t v___x_96963__boxed_2878_; uint8_t v_res_2879_; lean_object* v_r_2880_; 
v___x_96961__boxed_2877_ = lean_unbox(v___x_2873_);
v___x_96963__boxed_2878_ = lean_unbox(v___x_2875_);
v_res_2879_ = l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(v___x_2872_, v___x_96961__boxed_2877_, v_a_2874_, v___x_96963__boxed_2878_, v_x_2876_);
lean_dec(v_x_2876_);
lean_dec_ref(v_a_2874_);
lean_dec_ref(v___x_2872_);
v_r_2880_ = lean_box(v_res_2879_);
return v_r_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(lean_object* v_as_2881_, size_t v_i_2882_, size_t v_stop_2883_, lean_object* v_b_2884_){
_start:
{
uint8_t v___x_2885_; 
v___x_2885_ = lean_usize_dec_eq(v_i_2882_, v_stop_2883_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; size_t v___x_2889_; size_t v___x_2890_; 
v___x_2886_ = lean_array_uget_borrowed(v_as_2881_, v_i_2882_);
v___x_2887_ = l_Lean_PersistentArray_toArray___redArg(v___x_2886_);
v___x_2888_ = l_Array_append___redArg(v_b_2884_, v___x_2887_);
lean_dec_ref(v___x_2887_);
v___x_2889_ = ((size_t)1ULL);
v___x_2890_ = lean_usize_add(v_i_2882_, v___x_2889_);
v_i_2882_ = v___x_2890_;
v_b_2884_ = v___x_2888_;
goto _start;
}
else
{
return v_b_2884_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___boxed(lean_object* v_as_2892_, lean_object* v_i_2893_, lean_object* v_stop_2894_, lean_object* v_b_2895_){
_start:
{
size_t v_i_boxed_2896_; size_t v_stop_boxed_2897_; lean_object* v_res_2898_; 
v_i_boxed_2896_ = lean_unbox_usize(v_i_2893_);
lean_dec(v_i_2893_);
v_stop_boxed_2897_ = lean_unbox_usize(v_stop_2894_);
lean_dec(v_stop_2894_);
v_res_2898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_as_2892_, v_i_boxed_2896_, v_stop_boxed_2897_, v_b_2895_);
lean_dec_ref(v_as_2892_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26(lean_object* v_x_2899_, lean_object* v_x_2900_){
_start:
{
if (lean_obj_tag(v_x_2899_) == 0)
{
lean_object* v_cs_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; uint8_t v___x_2904_; 
v_cs_2901_ = lean_ctor_get(v_x_2899_, 0);
v___x_2902_ = lean_unsigned_to_nat(0u);
v___x_2903_ = lean_array_get_size(v_cs_2901_);
v___x_2904_ = lean_nat_dec_lt(v___x_2902_, v___x_2903_);
if (v___x_2904_ == 0)
{
return v_x_2900_;
}
else
{
size_t v___x_2905_; size_t v___x_2906_; lean_object* v___x_2907_; 
v___x_2905_ = ((size_t)0ULL);
v___x_2906_ = lean_usize_of_nat(v___x_2903_);
v___x_2907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32(v_cs_2901_, v___x_2905_, v___x_2906_, v_x_2900_);
return v___x_2907_;
}
}
else
{
lean_object* v_vs_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; 
v_vs_2908_ = lean_ctor_get(v_x_2899_, 0);
v___x_2909_ = lean_unsigned_to_nat(0u);
v___x_2910_ = lean_array_get_size(v_vs_2908_);
v___x_2911_ = lean_nat_dec_lt(v___x_2909_, v___x_2910_);
if (v___x_2911_ == 0)
{
return v_x_2900_;
}
else
{
size_t v___x_2912_; size_t v___x_2913_; lean_object* v___x_2914_; 
v___x_2912_ = ((size_t)0ULL);
v___x_2913_ = lean_usize_of_nat(v___x_2910_);
v___x_2914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_vs_2908_, v___x_2912_, v___x_2913_, v_x_2900_);
return v___x_2914_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32(lean_object* v_as_2915_, size_t v_i_2916_, size_t v_stop_2917_, lean_object* v_b_2918_){
_start:
{
uint8_t v___x_2919_; 
v___x_2919_ = lean_usize_dec_eq(v_i_2916_, v_stop_2917_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; lean_object* v___x_2921_; size_t v___x_2922_; size_t v___x_2923_; 
v___x_2920_ = lean_array_uget_borrowed(v_as_2915_, v_i_2916_);
v___x_2921_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26(v___x_2920_, v_b_2918_);
v___x_2922_ = ((size_t)1ULL);
v___x_2923_ = lean_usize_add(v_i_2916_, v___x_2922_);
v_i_2916_ = v___x_2923_;
v_b_2918_ = v___x_2921_;
goto _start;
}
else
{
return v_b_2918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32___boxed(lean_object* v_as_2925_, lean_object* v_i_2926_, lean_object* v_stop_2927_, lean_object* v_b_2928_){
_start:
{
size_t v_i_boxed_2929_; size_t v_stop_boxed_2930_; lean_object* v_res_2931_; 
v_i_boxed_2929_ = lean_unbox_usize(v_i_2926_);
lean_dec(v_i_2926_);
v_stop_boxed_2930_ = lean_unbox_usize(v_stop_2927_);
lean_dec(v_stop_2927_);
v_res_2931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32(v_as_2925_, v_i_boxed_2929_, v_stop_boxed_2930_, v_b_2928_);
lean_dec_ref(v_as_2925_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26___boxed(lean_object* v_x_2932_, lean_object* v_x_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26(v_x_2932_, v_x_2933_);
lean_dec_ref(v_x_2932_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(lean_object* v_x_2935_, size_t v_x_2936_, size_t v_x_2937_, lean_object* v_x_2938_){
_start:
{
if (lean_obj_tag(v_x_2935_) == 0)
{
lean_object* v_cs_2939_; lean_object* v___x_2940_; size_t v___x_2941_; lean_object* v_j_2942_; lean_object* v___x_2943_; size_t v___x_2944_; size_t v___x_2945_; size_t v___x_2946_; size_t v___x_2947_; size_t v___x_2948_; size_t v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v_cs_2939_ = lean_ctor_get(v_x_2935_, 0);
v___x_2940_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0);
v___x_2941_ = lean_usize_shift_right(v_x_2936_, v_x_2937_);
v_j_2942_ = lean_usize_to_nat(v___x_2941_);
v___x_2943_ = lean_array_get_borrowed(v___x_2940_, v_cs_2939_, v_j_2942_);
v___x_2944_ = ((size_t)1ULL);
v___x_2945_ = lean_usize_shift_left(v___x_2944_, v_x_2937_);
v___x_2946_ = lean_usize_sub(v___x_2945_, v___x_2944_);
v___x_2947_ = lean_usize_land(v_x_2936_, v___x_2946_);
v___x_2948_ = ((size_t)5ULL);
v___x_2949_ = lean_usize_sub(v_x_2937_, v___x_2948_);
v___x_2950_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(v___x_2943_, v___x_2947_, v___x_2949_, v_x_2938_);
v___x_2951_ = lean_unsigned_to_nat(1u);
v___x_2952_ = lean_nat_add(v_j_2942_, v___x_2951_);
lean_dec(v_j_2942_);
v___x_2953_ = lean_array_get_size(v_cs_2939_);
v___x_2954_ = lean_nat_dec_lt(v___x_2952_, v___x_2953_);
if (v___x_2954_ == 0)
{
lean_dec(v___x_2952_);
return v___x_2950_;
}
else
{
size_t v___x_2955_; size_t v___x_2956_; lean_object* v___x_2957_; 
v___x_2955_ = lean_usize_of_nat(v___x_2952_);
lean_dec(v___x_2952_);
v___x_2956_ = lean_usize_of_nat(v___x_2953_);
v___x_2957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32(v_cs_2939_, v___x_2955_, v___x_2956_, v___x_2950_);
return v___x_2957_;
}
}
else
{
lean_object* v_vs_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v_vs_2958_ = lean_ctor_get(v_x_2935_, 0);
v___x_2959_ = lean_usize_to_nat(v_x_2936_);
v___x_2960_ = lean_array_get_size(v_vs_2958_);
v___x_2961_ = lean_nat_dec_lt(v___x_2959_, v___x_2960_);
if (v___x_2961_ == 0)
{
lean_dec(v___x_2959_);
return v_x_2938_;
}
else
{
size_t v___x_2962_; size_t v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = lean_usize_of_nat(v___x_2959_);
lean_dec(v___x_2959_);
v___x_2963_ = lean_usize_of_nat(v___x_2960_);
v___x_2964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_vs_2958_, v___x_2962_, v___x_2963_, v_x_2938_);
return v___x_2964_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24___boxed(lean_object* v_x_2965_, lean_object* v_x_2966_, lean_object* v_x_2967_, lean_object* v_x_2968_){
_start:
{
size_t v_x_97065__boxed_2969_; size_t v_x_97066__boxed_2970_; lean_object* v_res_2971_; 
v_x_97065__boxed_2969_ = lean_unbox_usize(v_x_2966_);
lean_dec(v_x_2966_);
v_x_97066__boxed_2970_ = lean_unbox_usize(v_x_2967_);
lean_dec(v_x_2967_);
v_res_2971_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(v_x_2965_, v_x_97065__boxed_2969_, v_x_97066__boxed_2970_, v_x_2968_);
lean_dec_ref(v_x_2965_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(lean_object* v_t_2972_, lean_object* v_init_2973_, lean_object* v_start_2974_){
_start:
{
lean_object* v___x_2975_; uint8_t v___x_2976_; 
v___x_2975_ = lean_unsigned_to_nat(0u);
v___x_2976_ = lean_nat_dec_eq(v_start_2974_, v___x_2975_);
if (v___x_2976_ == 0)
{
lean_object* v_root_2977_; lean_object* v_tail_2978_; size_t v_shift_2979_; lean_object* v_tailOff_2980_; uint8_t v___x_2981_; 
v_root_2977_ = lean_ctor_get(v_t_2972_, 0);
v_tail_2978_ = lean_ctor_get(v_t_2972_, 1);
v_shift_2979_ = lean_ctor_get_usize(v_t_2972_, 4);
v_tailOff_2980_ = lean_ctor_get(v_t_2972_, 3);
v___x_2981_ = lean_nat_dec_le(v_tailOff_2980_, v_start_2974_);
if (v___x_2981_ == 0)
{
size_t v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; uint8_t v___x_2985_; 
v___x_2982_ = lean_usize_of_nat(v_start_2974_);
v___x_2983_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(v_root_2977_, v___x_2982_, v_shift_2979_, v_init_2973_);
v___x_2984_ = lean_array_get_size(v_tail_2978_);
v___x_2985_ = lean_nat_dec_lt(v___x_2975_, v___x_2984_);
if (v___x_2985_ == 0)
{
return v___x_2983_;
}
else
{
size_t v___x_2986_; size_t v___x_2987_; lean_object* v___x_2988_; 
v___x_2986_ = ((size_t)0ULL);
v___x_2987_ = lean_usize_of_nat(v___x_2984_);
v___x_2988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_tail_2978_, v___x_2986_, v___x_2987_, v___x_2983_);
return v___x_2988_;
}
}
else
{
lean_object* v___x_2989_; lean_object* v___x_2990_; uint8_t v___x_2991_; 
v___x_2989_ = lean_nat_sub(v_start_2974_, v_tailOff_2980_);
v___x_2990_ = lean_array_get_size(v_tail_2978_);
v___x_2991_ = lean_nat_dec_lt(v___x_2989_, v___x_2990_);
if (v___x_2991_ == 0)
{
lean_dec(v___x_2989_);
return v_init_2973_;
}
else
{
size_t v___x_2992_; size_t v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = lean_usize_of_nat(v___x_2989_);
lean_dec(v___x_2989_);
v___x_2993_ = lean_usize_of_nat(v___x_2990_);
v___x_2994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_tail_2978_, v___x_2992_, v___x_2993_, v_init_2973_);
return v___x_2994_;
}
}
}
else
{
lean_object* v_root_2995_; lean_object* v_tail_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; uint8_t v___x_2999_; 
v_root_2995_ = lean_ctor_get(v_t_2972_, 0);
v_tail_2996_ = lean_ctor_get(v_t_2972_, 1);
v___x_2997_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26(v_root_2995_, v_init_2973_);
v___x_2998_ = lean_array_get_size(v_tail_2996_);
v___x_2999_ = lean_nat_dec_lt(v___x_2975_, v___x_2998_);
if (v___x_2999_ == 0)
{
return v___x_2997_;
}
else
{
size_t v___x_3000_; size_t v___x_3001_; lean_object* v___x_3002_; 
v___x_3000_ = ((size_t)0ULL);
v___x_3001_ = lean_usize_of_nat(v___x_2998_);
v___x_3002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_tail_2996_, v___x_3000_, v___x_3001_, v___x_2997_);
return v___x_3002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10___boxed(lean_object* v_t_3003_, lean_object* v_init_3004_, lean_object* v_start_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v_t_3003_, v_init_3004_, v_start_3005_);
lean_dec(v_start_3005_);
lean_dec_ref(v_t_3003_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(lean_object* v_a_3007_, lean_object* v_a_3008_){
_start:
{
if (lean_obj_tag(v_a_3007_) == 0)
{
lean_object* v___x_3009_; 
v___x_3009_ = l_List_reverse___redArg(v_a_3008_);
return v___x_3009_;
}
else
{
lean_object* v_head_3010_; lean_object* v_tail_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3022_; 
v_head_3010_ = lean_ctor_get(v_a_3007_, 0);
v_tail_3011_ = lean_ctor_get(v_a_3007_, 1);
v_isSharedCheck_3022_ = !lean_is_exclusive(v_a_3007_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3013_ = v_a_3007_;
v_isShared_3014_ = v_isSharedCheck_3022_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_tail_3011_);
lean_inc(v_head_3010_);
lean_dec(v_a_3007_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3022_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3019_; 
v___x_3015_ = l_Nat_reprFast(v_head_3010_);
v___x_3016_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
v___x_3017_ = l_Lean_MessageData_ofFormat(v___x_3016_);
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 1, v_a_3008_);
lean_ctor_set(v___x_3013_, 0, v___x_3017_);
v___x_3019_ = v___x_3013_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3017_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_a_3008_);
v___x_3019_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
v_a_3007_ = v_tail_3011_;
v_a_3008_ = v___x_3019_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(lean_object* v___x_3023_, size_t v_sz_3024_, size_t v_i_3025_, lean_object* v_bs_3026_){
_start:
{
uint8_t v___x_3027_; 
v___x_3027_ = lean_usize_dec_lt(v_i_3025_, v_sz_3024_);
if (v___x_3027_ == 0)
{
return v_bs_3026_;
}
else
{
lean_object* v_v_3028_; lean_object* v___x_3029_; lean_object* v_bs_x27_3030_; lean_object* v___x_3031_; size_t v___x_3032_; size_t v___x_3033_; lean_object* v___x_3034_; 
v_v_3028_ = lean_array_uget(v_bs_3026_, v_i_3025_);
v___x_3029_ = lean_unsigned_to_nat(0u);
v_bs_x27_3030_ = lean_array_uset(v_bs_3026_, v_i_3025_, v___x_3029_);
v___x_3031_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(v_v_3028_, v___x_3023_);
v___x_3032_ = ((size_t)1ULL);
v___x_3033_ = lean_usize_add(v_i_3025_, v___x_3032_);
v___x_3034_ = lean_array_uset(v_bs_x27_3030_, v_i_3025_, v___x_3031_);
v_i_3025_ = v___x_3033_;
v_bs_3026_ = v___x_3034_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13___boxed(lean_object* v___x_3036_, lean_object* v_sz_3037_, lean_object* v_i_3038_, lean_object* v_bs_3039_){
_start:
{
size_t v_sz_boxed_3040_; size_t v_i_boxed_3041_; lean_object* v_res_3042_; 
v_sz_boxed_3040_ = lean_unbox_usize(v_sz_3037_);
lean_dec(v_sz_3037_);
v_i_boxed_3041_ = lean_unbox_usize(v_i_3038_);
lean_dec(v_i_3038_);
v_res_3042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v___x_3036_, v_sz_boxed_3040_, v_i_boxed_3041_, v_bs_3039_);
lean_dec_ref(v___x_3036_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(lean_object* v_as_3043_, size_t v_sz_3044_, size_t v_i_3045_, lean_object* v_b_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
uint8_t v___x_3058_; 
v___x_3058_ = lean_usize_dec_lt(v_i_3045_, v_sz_3044_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3059_, 0, v_b_3046_);
return v___x_3059_;
}
else
{
lean_object* v___x_3060_; lean_object* v_a_3061_; lean_object* v___x_3062_; 
v___x_3060_ = lean_box(0);
v_a_3061_ = lean_array_uget_borrowed(v_as_3043_, v_i_3045_);
lean_inc(v_a_3061_);
v___x_3062_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_assert(v_a_3061_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
if (lean_obj_tag(v___x_3062_) == 0)
{
size_t v___x_3063_; size_t v___x_3064_; 
lean_dec_ref_known(v___x_3062_, 1);
v___x_3063_ = ((size_t)1ULL);
v___x_3064_ = lean_usize_add(v_i_3045_, v___x_3063_);
v_i_3045_ = v___x_3064_;
v_b_3046_ = v___x_3060_;
goto _start;
}
else
{
return v___x_3062_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___boxed(lean_object* v_as_3066_, lean_object* v_sz_3067_, lean_object* v_i_3068_, lean_object* v_b_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
size_t v_sz_boxed_3081_; size_t v_i_boxed_3082_; lean_object* v_res_3083_; 
v_sz_boxed_3081_ = lean_unbox_usize(v_sz_3067_);
lean_dec(v_sz_3067_);
v_i_boxed_3082_ = lean_unbox_usize(v_i_3068_);
lean_dec(v_i_3068_);
v_res_3083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v_as_3066_, v_sz_boxed_3081_, v_i_boxed_3082_, v_b_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v_as_3066_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(lean_object* v_as_3084_, size_t v_sz_3085_, size_t v_i_3086_, lean_object* v_b_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
uint8_t v___x_3099_; 
v___x_3099_ = lean_usize_dec_lt(v_i_3086_, v_sz_3085_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3100_, 0, v_b_3087_);
return v___x_3100_;
}
else
{
lean_object* v___x_3101_; lean_object* v_a_3102_; lean_object* v___x_3103_; 
v___x_3101_ = lean_box(0);
v_a_3102_ = lean_array_uget_borrowed(v_as_3084_, v_i_3086_);
lean_inc(v___y_3097_);
lean_inc_ref(v___y_3096_);
lean_inc(v___y_3095_);
lean_inc_ref(v___y_3094_);
lean_inc(v___y_3093_);
lean_inc_ref(v___y_3092_);
lean_inc(v___y_3091_);
lean_inc_ref(v___y_3090_);
lean_inc(v___y_3089_);
lean_inc(v___y_3088_);
lean_inc(v_a_3102_);
v___x_3103_ = lean_grind_cutsat_assert_le(v_a_3102_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
if (lean_obj_tag(v___x_3103_) == 0)
{
size_t v___x_3104_; size_t v___x_3105_; 
lean_dec_ref_known(v___x_3103_, 1);
v___x_3104_ = ((size_t)1ULL);
v___x_3105_ = lean_usize_add(v_i_3086_, v___x_3104_);
v_i_3086_ = v___x_3105_;
v_b_3087_ = v___x_3101_;
goto _start;
}
else
{
return v___x_3103_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15___boxed(lean_object* v_as_3107_, lean_object* v_sz_3108_, lean_object* v_i_3109_, lean_object* v_b_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
size_t v_sz_boxed_3122_; size_t v_i_boxed_3123_; lean_object* v_res_3124_; 
v_sz_boxed_3122_ = lean_unbox_usize(v_sz_3108_);
lean_dec(v_sz_3108_);
v_i_boxed_3123_ = lean_unbox_usize(v_i_3109_);
lean_dec(v_i_3109_);
v_res_3124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v_as_3107_, v_sz_boxed_3122_, v_i_boxed_3123_, v_b_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v_as_3107_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(lean_object* v_as_3125_, size_t v_i_3126_, size_t v_stop_3127_, lean_object* v_b_3128_){
_start:
{
uint8_t v___x_3129_; 
v___x_3129_ = lean_usize_dec_eq(v_i_3126_, v_stop_3127_);
if (v___x_3129_ == 0)
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; size_t v___x_3133_; size_t v___x_3134_; 
v___x_3130_ = lean_array_uget_borrowed(v_as_3125_, v_i_3126_);
v___x_3131_ = l_Lean_PersistentArray_toArray___redArg(v___x_3130_);
v___x_3132_ = l_Array_append___redArg(v_b_3128_, v___x_3131_);
lean_dec_ref(v___x_3131_);
v___x_3133_ = ((size_t)1ULL);
v___x_3134_ = lean_usize_add(v_i_3126_, v___x_3133_);
v_i_3126_ = v___x_3134_;
v_b_3128_ = v___x_3132_;
goto _start;
}
else
{
return v_b_3128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30___boxed(lean_object* v_as_3136_, lean_object* v_i_3137_, lean_object* v_stop_3138_, lean_object* v_b_3139_){
_start:
{
size_t v_i_boxed_3140_; size_t v_stop_boxed_3141_; lean_object* v_res_3142_; 
v_i_boxed_3140_ = lean_unbox_usize(v_i_3137_);
lean_dec(v_i_3137_);
v_stop_boxed_3141_ = lean_unbox_usize(v_stop_3138_);
lean_dec(v_stop_3138_);
v_res_3142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_as_3136_, v_i_boxed_3140_, v_stop_boxed_3141_, v_b_3139_);
lean_dec_ref(v_as_3136_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31(lean_object* v_x_3143_, lean_object* v_x_3144_){
_start:
{
if (lean_obj_tag(v_x_3143_) == 0)
{
lean_object* v_cs_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; uint8_t v___x_3148_; 
v_cs_3145_ = lean_ctor_get(v_x_3143_, 0);
v___x_3146_ = lean_unsigned_to_nat(0u);
v___x_3147_ = lean_array_get_size(v_cs_3145_);
v___x_3148_ = lean_nat_dec_lt(v___x_3146_, v___x_3147_);
if (v___x_3148_ == 0)
{
return v_x_3144_;
}
else
{
size_t v___x_3149_; size_t v___x_3150_; lean_object* v___x_3151_; 
v___x_3149_ = ((size_t)0ULL);
v___x_3150_ = lean_usize_of_nat(v___x_3147_);
v___x_3151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38(v_cs_3145_, v___x_3149_, v___x_3150_, v_x_3144_);
return v___x_3151_;
}
}
else
{
lean_object* v_vs_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; uint8_t v___x_3155_; 
v_vs_3152_ = lean_ctor_get(v_x_3143_, 0);
v___x_3153_ = lean_unsigned_to_nat(0u);
v___x_3154_ = lean_array_get_size(v_vs_3152_);
v___x_3155_ = lean_nat_dec_lt(v___x_3153_, v___x_3154_);
if (v___x_3155_ == 0)
{
return v_x_3144_;
}
else
{
size_t v___x_3156_; size_t v___x_3157_; lean_object* v___x_3158_; 
v___x_3156_ = ((size_t)0ULL);
v___x_3157_ = lean_usize_of_nat(v___x_3154_);
v___x_3158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_vs_3152_, v___x_3156_, v___x_3157_, v_x_3144_);
return v___x_3158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38(lean_object* v_as_3159_, size_t v_i_3160_, size_t v_stop_3161_, lean_object* v_b_3162_){
_start:
{
uint8_t v___x_3163_; 
v___x_3163_ = lean_usize_dec_eq(v_i_3160_, v_stop_3161_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; lean_object* v___x_3165_; size_t v___x_3166_; size_t v___x_3167_; 
v___x_3164_ = lean_array_uget_borrowed(v_as_3159_, v_i_3160_);
v___x_3165_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31(v___x_3164_, v_b_3162_);
v___x_3166_ = ((size_t)1ULL);
v___x_3167_ = lean_usize_add(v_i_3160_, v___x_3166_);
v_i_3160_ = v___x_3167_;
v_b_3162_ = v___x_3165_;
goto _start;
}
else
{
return v_b_3162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38___boxed(lean_object* v_as_3169_, lean_object* v_i_3170_, lean_object* v_stop_3171_, lean_object* v_b_3172_){
_start:
{
size_t v_i_boxed_3173_; size_t v_stop_boxed_3174_; lean_object* v_res_3175_; 
v_i_boxed_3173_ = lean_unbox_usize(v_i_3170_);
lean_dec(v_i_3170_);
v_stop_boxed_3174_ = lean_unbox_usize(v_stop_3171_);
lean_dec(v_stop_3171_);
v_res_3175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38(v_as_3169_, v_i_boxed_3173_, v_stop_boxed_3174_, v_b_3172_);
lean_dec_ref(v_as_3169_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31___boxed(lean_object* v_x_3176_, lean_object* v_x_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31(v_x_3176_, v_x_3177_);
lean_dec_ref(v_x_3176_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29(lean_object* v_x_3179_, size_t v_x_3180_, size_t v_x_3181_, lean_object* v_x_3182_){
_start:
{
if (lean_obj_tag(v_x_3179_) == 0)
{
lean_object* v_cs_3183_; lean_object* v___x_3184_; size_t v___x_3185_; lean_object* v_j_3186_; lean_object* v___x_3187_; size_t v___x_3188_; size_t v___x_3189_; size_t v___x_3190_; size_t v___x_3191_; size_t v___x_3192_; size_t v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; 
v_cs_3183_ = lean_ctor_get(v_x_3179_, 0);
v___x_3184_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0);
v___x_3185_ = lean_usize_shift_right(v_x_3180_, v_x_3181_);
v_j_3186_ = lean_usize_to_nat(v___x_3185_);
v___x_3187_ = lean_array_get_borrowed(v___x_3184_, v_cs_3183_, v_j_3186_);
v___x_3188_ = ((size_t)1ULL);
v___x_3189_ = lean_usize_shift_left(v___x_3188_, v_x_3181_);
v___x_3190_ = lean_usize_sub(v___x_3189_, v___x_3188_);
v___x_3191_ = lean_usize_land(v_x_3180_, v___x_3190_);
v___x_3192_ = ((size_t)5ULL);
v___x_3193_ = lean_usize_sub(v_x_3181_, v___x_3192_);
v___x_3194_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29(v___x_3187_, v___x_3191_, v___x_3193_, v_x_3182_);
v___x_3195_ = lean_unsigned_to_nat(1u);
v___x_3196_ = lean_nat_add(v_j_3186_, v___x_3195_);
lean_dec(v_j_3186_);
v___x_3197_ = lean_array_get_size(v_cs_3183_);
v___x_3198_ = lean_nat_dec_lt(v___x_3196_, v___x_3197_);
if (v___x_3198_ == 0)
{
lean_dec(v___x_3196_);
return v___x_3194_;
}
else
{
size_t v___x_3199_; size_t v___x_3200_; lean_object* v___x_3201_; 
v___x_3199_ = lean_usize_of_nat(v___x_3196_);
lean_dec(v___x_3196_);
v___x_3200_ = lean_usize_of_nat(v___x_3197_);
v___x_3201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38(v_cs_3183_, v___x_3199_, v___x_3200_, v___x_3194_);
return v___x_3201_;
}
}
else
{
lean_object* v_vs_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; uint8_t v___x_3205_; 
v_vs_3202_ = lean_ctor_get(v_x_3179_, 0);
v___x_3203_ = lean_usize_to_nat(v_x_3180_);
v___x_3204_ = lean_array_get_size(v_vs_3202_);
v___x_3205_ = lean_nat_dec_lt(v___x_3203_, v___x_3204_);
if (v___x_3205_ == 0)
{
lean_dec(v___x_3203_);
return v_x_3182_;
}
else
{
size_t v___x_3206_; size_t v___x_3207_; lean_object* v___x_3208_; 
v___x_3206_ = lean_usize_of_nat(v___x_3203_);
lean_dec(v___x_3203_);
v___x_3207_ = lean_usize_of_nat(v___x_3204_);
v___x_3208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_vs_3202_, v___x_3206_, v___x_3207_, v_x_3182_);
return v___x_3208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29___boxed(lean_object* v_x_3209_, lean_object* v_x_3210_, lean_object* v_x_3211_, lean_object* v_x_3212_){
_start:
{
size_t v_x_97379__boxed_3213_; size_t v_x_97380__boxed_3214_; lean_object* v_res_3215_; 
v_x_97379__boxed_3213_ = lean_unbox_usize(v_x_3210_);
lean_dec(v_x_3210_);
v_x_97380__boxed_3214_ = lean_unbox_usize(v_x_3211_);
lean_dec(v_x_3211_);
v_res_3215_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29(v_x_3209_, v_x_97379__boxed_3213_, v_x_97380__boxed_3214_, v_x_3212_);
lean_dec_ref(v_x_3209_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(lean_object* v_t_3216_, lean_object* v_init_3217_, lean_object* v_start_3218_){
_start:
{
lean_object* v___x_3219_; uint8_t v___x_3220_; 
v___x_3219_ = lean_unsigned_to_nat(0u);
v___x_3220_ = lean_nat_dec_eq(v_start_3218_, v___x_3219_);
if (v___x_3220_ == 0)
{
lean_object* v_root_3221_; lean_object* v_tail_3222_; size_t v_shift_3223_; lean_object* v_tailOff_3224_; uint8_t v___x_3225_; 
v_root_3221_ = lean_ctor_get(v_t_3216_, 0);
v_tail_3222_ = lean_ctor_get(v_t_3216_, 1);
v_shift_3223_ = lean_ctor_get_usize(v_t_3216_, 4);
v_tailOff_3224_ = lean_ctor_get(v_t_3216_, 3);
v___x_3225_ = lean_nat_dec_le(v_tailOff_3224_, v_start_3218_);
if (v___x_3225_ == 0)
{
size_t v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; uint8_t v___x_3229_; 
v___x_3226_ = lean_usize_of_nat(v_start_3218_);
v___x_3227_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29(v_root_3221_, v___x_3226_, v_shift_3223_, v_init_3217_);
v___x_3228_ = lean_array_get_size(v_tail_3222_);
v___x_3229_ = lean_nat_dec_lt(v___x_3219_, v___x_3228_);
if (v___x_3229_ == 0)
{
return v___x_3227_;
}
else
{
size_t v___x_3230_; size_t v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = ((size_t)0ULL);
v___x_3231_ = lean_usize_of_nat(v___x_3228_);
v___x_3232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_tail_3222_, v___x_3230_, v___x_3231_, v___x_3227_);
return v___x_3232_;
}
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; uint8_t v___x_3235_; 
v___x_3233_ = lean_nat_sub(v_start_3218_, v_tailOff_3224_);
v___x_3234_ = lean_array_get_size(v_tail_3222_);
v___x_3235_ = lean_nat_dec_lt(v___x_3233_, v___x_3234_);
if (v___x_3235_ == 0)
{
lean_dec(v___x_3233_);
return v_init_3217_;
}
else
{
size_t v___x_3236_; size_t v___x_3237_; lean_object* v___x_3238_; 
v___x_3236_ = lean_usize_of_nat(v___x_3233_);
lean_dec(v___x_3233_);
v___x_3237_ = lean_usize_of_nat(v___x_3234_);
v___x_3238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_tail_3222_, v___x_3236_, v___x_3237_, v_init_3217_);
return v___x_3238_;
}
}
}
else
{
lean_object* v_root_3239_; lean_object* v_tail_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; uint8_t v___x_3243_; 
v_root_3239_ = lean_ctor_get(v_t_3216_, 0);
v_tail_3240_ = lean_ctor_get(v_t_3216_, 1);
v___x_3241_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31(v_root_3239_, v_init_3217_);
v___x_3242_ = lean_array_get_size(v_tail_3240_);
v___x_3243_ = lean_nat_dec_lt(v___x_3219_, v___x_3242_);
if (v___x_3243_ == 0)
{
return v___x_3241_;
}
else
{
size_t v___x_3244_; size_t v___x_3245_; lean_object* v___x_3246_; 
v___x_3244_ = ((size_t)0ULL);
v___x_3245_ = lean_usize_of_nat(v___x_3242_);
v___x_3246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_tail_3240_, v___x_3244_, v___x_3245_, v___x_3241_);
return v___x_3246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12___boxed(lean_object* v_t_3247_, lean_object* v_init_3248_, lean_object* v_start_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v_t_3247_, v_init_3248_, v_start_3249_);
lean_dec(v_start_3249_);
lean_dec_ref(v_t_3247_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(lean_object* v_msgData_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v___x_3257_; lean_object* v_env_3258_; uint8_t v___x_3259_; lean_object* v_env_3260_; lean_object* v___x_3261_; lean_object* v_toCold_3262_; lean_object* v_mctx_3263_; lean_object* v_lctx_3264_; lean_object* v_options_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3257_ = lean_st_ref_get(v___y_3255_);
v_env_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc_ref(v_env_3258_);
lean_dec(v___x_3257_);
v___x_3259_ = 0;
v_env_3260_ = l_Lean_Environment_setRecordingDeps(v_env_3258_, v___x_3259_);
v___x_3261_ = lean_st_ref_get(v___y_3253_);
v_toCold_3262_ = lean_ctor_get(v___y_3254_, 0);
v_mctx_3263_ = lean_ctor_get(v___x_3261_, 0);
lean_inc_ref(v_mctx_3263_);
lean_dec(v___x_3261_);
v_lctx_3264_ = lean_ctor_get(v___y_3252_, 2);
v_options_3265_ = lean_ctor_get(v_toCold_3262_, 2);
lean_inc_ref(v_options_3265_);
lean_inc_ref(v_lctx_3264_);
v___x_3266_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3266_, 0, v_env_3260_);
lean_ctor_set(v___x_3266_, 1, v_mctx_3263_);
lean_ctor_set(v___x_3266_, 2, v_lctx_3264_);
lean_ctor_set(v___x_3266_, 3, v_options_3265_);
v___x_3267_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
lean_ctor_set(v___x_3267_, 1, v_msgData_3251_);
v___x_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38___boxed(lean_object* v_msgData_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(v_msgData_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
return v_res_3275_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0(void){
_start:
{
lean_object* v___x_3276_; double v___x_3277_; 
v___x_3276_ = lean_unsigned_to_nat(0u);
v___x_3277_ = lean_float_of_nat(v___x_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(lean_object* v_cls_3281_, lean_object* v_msg_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v_ref_3288_; lean_object* v___x_3289_; lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3335_; 
v_ref_3288_ = lean_ctor_get(v___y_3285_, 2);
v___x_3289_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(v_msg_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3335_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3335_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3294_; lean_object* v_traceState_3295_; lean_object* v_env_3296_; lean_object* v_nextMacroScope_3297_; lean_object* v_ngen_3298_; lean_object* v_auxDeclNGen_3299_; lean_object* v_cache_3300_; lean_object* v_recordedDeps_3301_; lean_object* v_messages_3302_; lean_object* v_infoState_3303_; lean_object* v_snapshotTasks_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3334_; 
v___x_3294_ = lean_st_ref_take(v___y_3286_);
v_traceState_3295_ = lean_ctor_get(v___x_3294_, 4);
v_env_3296_ = lean_ctor_get(v___x_3294_, 0);
v_nextMacroScope_3297_ = lean_ctor_get(v___x_3294_, 1);
v_ngen_3298_ = lean_ctor_get(v___x_3294_, 2);
v_auxDeclNGen_3299_ = lean_ctor_get(v___x_3294_, 3);
v_cache_3300_ = lean_ctor_get(v___x_3294_, 5);
v_recordedDeps_3301_ = lean_ctor_get(v___x_3294_, 6);
v_messages_3302_ = lean_ctor_get(v___x_3294_, 7);
v_infoState_3303_ = lean_ctor_get(v___x_3294_, 8);
v_snapshotTasks_3304_ = lean_ctor_get(v___x_3294_, 9);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3306_ = v___x_3294_;
v_isShared_3307_ = v_isSharedCheck_3334_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_snapshotTasks_3304_);
lean_inc(v_infoState_3303_);
lean_inc(v_messages_3302_);
lean_inc(v_recordedDeps_3301_);
lean_inc(v_cache_3300_);
lean_inc(v_traceState_3295_);
lean_inc(v_auxDeclNGen_3299_);
lean_inc(v_ngen_3298_);
lean_inc(v_nextMacroScope_3297_);
lean_inc(v_env_3296_);
lean_dec(v___x_3294_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3334_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
uint64_t v_tid_3308_; lean_object* v_traces_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3333_; 
v_tid_3308_ = lean_ctor_get_uint64(v_traceState_3295_, sizeof(void*)*1);
v_traces_3309_ = lean_ctor_get(v_traceState_3295_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v_traceState_3295_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3311_ = v_traceState_3295_;
v_isShared_3312_ = v_isSharedCheck_3333_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_traces_3309_);
lean_dec(v_traceState_3295_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3333_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; double v___x_3315_; uint8_t v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
v___x_3313_ = lean_box(0);
v___x_3314_ = lean_box(0);
v___x_3315_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0);
v___x_3316_ = 0;
v___x_3317_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__1));
v___x_3318_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3318_, 0, v_cls_3281_);
lean_ctor_set(v___x_3318_, 1, v___x_3314_);
lean_ctor_set(v___x_3318_, 2, v___x_3317_);
lean_ctor_set_float(v___x_3318_, sizeof(void*)*3, v___x_3315_);
lean_ctor_set_float(v___x_3318_, sizeof(void*)*3 + 8, v___x_3315_);
lean_ctor_set_uint8(v___x_3318_, sizeof(void*)*3 + 16, v___x_3316_);
v___x_3319_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__2));
v___x_3320_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3318_);
lean_ctor_set(v___x_3320_, 1, v_a_3290_);
lean_ctor_set(v___x_3320_, 2, v___x_3319_);
lean_inc(v_ref_3288_);
v___x_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3321_, 0, v_ref_3288_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
v___x_3322_ = l_Lean_PersistentArray_push___redArg(v_traces_3309_, v___x_3321_);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 0, v___x_3322_);
v___x_3324_ = v___x_3311_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3322_);
lean_ctor_set_uint64(v_reuseFailAlloc_3332_, sizeof(void*)*1, v_tid_3308_);
v___x_3324_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v___x_3326_; 
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v___x_3324_);
v___x_3326_ = v___x_3306_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_env_3296_);
lean_ctor_set(v_reuseFailAlloc_3331_, 1, v_nextMacroScope_3297_);
lean_ctor_set(v_reuseFailAlloc_3331_, 2, v_ngen_3298_);
lean_ctor_set(v_reuseFailAlloc_3331_, 3, v_auxDeclNGen_3299_);
lean_ctor_set(v_reuseFailAlloc_3331_, 4, v___x_3324_);
lean_ctor_set(v_reuseFailAlloc_3331_, 5, v_cache_3300_);
lean_ctor_set(v_reuseFailAlloc_3331_, 6, v_recordedDeps_3301_);
lean_ctor_set(v_reuseFailAlloc_3331_, 7, v_messages_3302_);
lean_ctor_set(v_reuseFailAlloc_3331_, 8, v_infoState_3303_);
lean_ctor_set(v_reuseFailAlloc_3331_, 9, v_snapshotTasks_3304_);
v___x_3326_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
lean_object* v___x_3327_; lean_object* v___x_3329_; 
v___x_3327_ = lean_st_ref_put(v___y_3286_, v___x_3326_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3313_);
v___x_3329_ = v___x_3292_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3313_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___boxed(lean_object* v_cls_3336_, lean_object* v_msg_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v_cls_3336_, v_msg_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
return v_res_3343_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3(void){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2));
v___x_3349_ = l_Lean_stringToMessageData(v___x_3348_);
return v___x_3349_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11(void){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3363_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10));
v___x_3364_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1));
v___x_3365_ = l_Lean_Name_append(v___x_3364_, v___x_3363_);
return v___x_3365_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13(void){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12));
v___x_3368_ = l_Lean_stringToMessageData(v___x_3367_);
return v___x_3368_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15(void){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3373_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14));
v___x_3374_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1));
v___x_3375_ = l_Lean_Name_append(v___x_3374_, v___x_3373_);
return v___x_3375_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17(void){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__16));
v___x_3378_ = l_Lean_stringToMessageData(v___x_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3390_ = lean_unsigned_to_nat(0u);
v___x_3391_ = l_Lean_instInhabitedExpr;
v___x_3392_ = lean_box(0);
v___x_3393_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3379_, v_a_3387_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3534_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3396_ = v___x_3393_;
v_isShared_3397_ = v_isSharedCheck_3534_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3393_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3534_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v_vars_3398_; lean_object* v_varsHistory_3399_; lean_object* v_dvds_3400_; lean_object* v_lowers_3401_; lean_object* v_uppers_3402_; lean_object* v_diseqs_3403_; uint8_t v___x_3404_; 
v_vars_3398_ = lean_ctor_get(v_a_3394_, 0);
lean_inc_ref(v_vars_3398_);
v_varsHistory_3399_ = lean_ctor_get(v_a_3394_, 2);
lean_inc_ref(v_varsHistory_3399_);
v_dvds_3400_ = lean_ctor_get(v_a_3394_, 5);
lean_inc_ref(v_dvds_3400_);
v_lowers_3401_ = lean_ctor_get(v_a_3394_, 6);
lean_inc_ref(v_lowers_3401_);
v_uppers_3402_ = lean_ctor_get(v_a_3394_, 7);
lean_inc_ref(v_uppers_3402_);
v_diseqs_3403_ = lean_ctor_get(v_a_3394_, 8);
lean_inc_ref(v_diseqs_3403_);
lean_dec(v_a_3394_);
v___x_3404_ = l_Lean_PersistentArray_isEmpty___redArg(v_vars_3398_);
if (v___x_3404_ == 0)
{
lean_object* v___x_3405_; 
lean_del_object(v___x_3396_);
v___x_3405_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3407_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v___x_3407_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(v_a_3406_, v_a_3379_, v_a_3387_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3513_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3410_ = v___x_3407_;
v_isShared_3411_ = v_isSharedCheck_3513_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3513_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v_size_3412_; lean_object* v___x_3413_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v_options_3425_; lean_object* v_inheritedTraceOptions_3426_; lean_object* v___y_3427_; uint8_t v___x_3440_; lean_object* v___x_3441_; uint8_t v___x_3442_; 
v_size_3412_ = lean_ctor_get(v_vars_3398_, 2);
lean_inc(v_size_3412_);
lean_dec_ref(v_vars_3398_);
v___x_3413_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_a_3408_);
v___x_3440_ = l_Lean_PersistentArray_isEmpty___redArg(v_varsHistory_3399_);
v___x_3441_ = l_List_range(v_size_3412_);
v___x_3442_ = l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(v___x_3413_, v___x_3440_, v_a_3406_, v___x_3404_, v___x_3441_);
lean_dec(v___x_3441_);
lean_dec(v_a_3406_);
if (v___x_3442_ == 0)
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
lean_dec_ref(v___x_3413_);
lean_dec(v_a_3408_);
lean_dec_ref(v_diseqs_3403_);
lean_dec_ref(v_uppers_3402_);
lean_dec_ref(v_lowers_3401_);
lean_dec_ref(v_dvds_3400_);
lean_dec_ref(v_varsHistory_3399_);
v___x_3443_ = lean_box(0);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 0, v___x_3443_);
v___x_3445_ = v___x_3410_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
else
{
lean_object* v_toCold_3447_; lean_object* v_options_3448_; lean_object* v_inheritedTraceOptions_3449_; uint8_t v_hasTrace_3450_; lean_object* v___f_3451_; lean_object* v___f_3452_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; 
lean_del_object(v___x_3410_);
v_toCold_3447_ = lean_ctor_get(v_a_3387_, 0);
v_options_3448_ = lean_ctor_get(v_toCold_3447_, 2);
v_inheritedTraceOptions_3449_ = lean_ctor_get(v_toCold_3447_, 11);
v_hasTrace_3450_ = lean_ctor_get_uint8(v_options_3448_, sizeof(void*)*1);
lean_inc_ref_n(v___x_3413_, 2);
v___f_3451_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3451_, 0, v___x_3390_);
lean_closure_set(v___f_3451_, 1, v___x_3413_);
lean_inc(v_a_3408_);
v___f_3452_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed), 6, 5);
lean_closure_set(v___f_3452_, 0, v___x_3391_);
lean_closure_set(v___f_3452_, 1, v_a_3408_);
lean_closure_set(v___f_3452_, 2, v___f_3451_);
lean_closure_set(v___f_3452_, 3, v___x_3392_);
lean_closure_set(v___f_3452_, 4, v___x_3413_);
if (v_hasTrace_3450_ == 0)
{
lean_dec_ref(v_varsHistory_3399_);
v___y_3454_ = v_a_3379_;
v___y_3455_ = v_a_3380_;
v___y_3456_ = v_a_3381_;
v___y_3457_ = v_a_3382_;
v___y_3458_ = v_a_3383_;
v___y_3459_ = v_a_3384_;
v___y_3460_ = v_a_3385_;
v___y_3461_ = v_a_3386_;
v___y_3462_ = v_a_3387_;
v___y_3463_ = v_a_3388_;
goto v___jp_3453_;
}
else
{
lean_object* v___x_3501_; lean_object* v___x_3502_; uint8_t v___x_3503_; 
v___x_3501_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14));
v___x_3502_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15);
v___x_3503_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3449_, v_options_3448_, v___x_3502_);
if (v___x_3503_ == 0)
{
lean_dec_ref(v_varsHistory_3399_);
v___y_3454_ = v_a_3379_;
v___y_3455_ = v_a_3380_;
v___y_3456_ = v_a_3381_;
v___y_3457_ = v_a_3382_;
v___y_3458_ = v_a_3383_;
v___y_3459_ = v_a_3384_;
v___y_3460_ = v_a_3385_;
v___y_3461_ = v_a_3386_;
v___y_3462_ = v_a_3387_;
v___y_3463_ = v_a_3388_;
goto v___jp_3453_;
}
else
{
lean_object* v_size_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v_size_3504_ = lean_ctor_get(v_varsHistory_3399_, 2);
lean_inc(v_size_3504_);
lean_dec_ref(v_varsHistory_3399_);
v___x_3505_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17);
v___x_3506_ = lean_unsigned_to_nat(1u);
v___x_3507_ = lean_nat_add(v_size_3504_, v___x_3506_);
lean_dec(v_size_3504_);
v___x_3508_ = l_Nat_reprFast(v___x_3507_);
v___x_3509_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
v___x_3510_ = l_Lean_MessageData_ofFormat(v___x_3509_);
v___x_3511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3505_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
v___x_3512_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v___x_3501_, v___x_3511_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_dec_ref_known(v___x_3512_, 1);
v___y_3454_ = v_a_3379_;
v___y_3455_ = v_a_3380_;
v___y_3456_ = v_a_3381_;
v___y_3457_ = v_a_3382_;
v___y_3458_ = v_a_3383_;
v___y_3459_ = v_a_3384_;
v___y_3460_ = v_a_3385_;
v___y_3461_ = v_a_3386_;
v___y_3462_ = v_a_3387_;
v___y_3463_ = v_a_3388_;
goto v___jp_3453_;
}
else
{
lean_dec_ref(v___f_3452_);
lean_dec_ref(v___x_3413_);
lean_dec(v_a_3408_);
lean_dec_ref(v_diseqs_3403_);
lean_dec_ref(v_uppers_3402_);
lean_dec_ref(v_lowers_3401_);
lean_dec_ref(v_dvds_3400_);
return v___x_3512_;
}
}
}
v___jp_3453_:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v___x_3465_; lean_object* v___x_3466_; size_t v_sz_3467_; size_t v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; size_t v_sz_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; size_t v_sz_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
lean_dec_ref_known(v___x_3464_, 1);
v___x_3465_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7));
v___x_3466_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_dvds_3400_, v___x_3465_, v___x_3390_);
lean_dec_ref(v_dvds_3400_);
v_sz_3467_ = lean_array_size(v___x_3466_);
v___x_3468_ = ((size_t)0ULL);
v___x_3469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v___x_3413_, v_sz_3467_, v___x_3468_, v___x_3466_);
v___x_3470_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v_lowers_3401_, v___x_3465_, v___x_3390_);
lean_dec_ref(v_lowers_3401_);
v___x_3471_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v_uppers_3402_, v___x_3470_, v___x_3390_);
lean_dec_ref(v_uppers_3402_);
v_sz_3472_ = lean_array_size(v___x_3471_);
v___x_3473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v___x_3413_, v_sz_3472_, v___x_3468_, v___x_3471_);
v___x_3474_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v_diseqs_3403_, v___x_3465_, v___x_3390_);
lean_dec_ref(v_diseqs_3403_);
v_sz_3475_ = lean_array_size(v___x_3474_);
v___x_3476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v___x_3413_, v_sz_3475_, v___x_3468_, v___x_3474_);
v___x_3477_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3478_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3477_, v___f_3452_, v___y_3454_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v___x_3479_; size_t v_sz_3480_; lean_object* v___x_3481_; 
lean_dec_ref_known(v___x_3478_, 1);
v___x_3479_ = lean_box(0);
v_sz_3480_ = lean_array_size(v___x_3469_);
v___x_3481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v___x_3469_, v_sz_3480_, v___x_3468_, v___x_3479_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
lean_dec_ref(v___x_3469_);
if (lean_obj_tag(v___x_3481_) == 0)
{
size_t v_sz_3482_; lean_object* v___x_3483_; 
lean_dec_ref_known(v___x_3481_, 1);
v_sz_3482_ = lean_array_size(v___x_3473_);
v___x_3483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v___x_3473_, v_sz_3482_, v___x_3468_, v___x_3479_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
lean_dec_ref(v___x_3473_);
if (lean_obj_tag(v___x_3483_) == 0)
{
size_t v_sz_3484_; lean_object* v___x_3485_; 
lean_dec_ref_known(v___x_3483_, 1);
v_sz_3484_ = lean_array_size(v___x_3476_);
v___x_3485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v___x_3476_, v_sz_3484_, v___x_3468_, v___x_3479_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
lean_dec_ref(v___x_3476_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_toCold_3486_; lean_object* v_options_3487_; uint8_t v_hasTrace_3488_; 
lean_dec_ref_known(v___x_3485_, 1);
v_toCold_3486_ = lean_ctor_get(v___y_3462_, 0);
v_options_3487_ = lean_ctor_get(v_toCold_3486_, 2);
v_hasTrace_3488_ = lean_ctor_get_uint8(v_options_3487_, sizeof(void*)*1);
if (v_hasTrace_3488_ == 0)
{
lean_object* v___x_3489_; 
lean_dec_ref(v___x_3413_);
lean_dec(v_a_3408_);
v___x_3489_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
return v___x_3489_;
}
else
{
lean_object* v_inheritedTraceOptions_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; uint8_t v___x_3493_; 
v_inheritedTraceOptions_3490_ = lean_ctor_get(v_toCold_3486_, 11);
v___x_3491_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10));
v___x_3492_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11);
v___x_3493_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3490_, v_options_3487_, v___x_3492_);
if (v___x_3493_ == 0)
{
lean_dec(v_a_3408_);
v___y_3415_ = v___x_3491_;
v___y_3416_ = v___y_3454_;
v___y_3417_ = v___y_3455_;
v___y_3418_ = v___y_3456_;
v___y_3419_ = v___y_3457_;
v___y_3420_ = v___y_3458_;
v___y_3421_ = v___y_3459_;
v___y_3422_ = v___y_3460_;
v___y_3423_ = v___y_3461_;
v___y_3424_ = v___y_3462_;
v_options_3425_ = v_options_3487_;
v_inheritedTraceOptions_3426_ = v_inheritedTraceOptions_3490_;
v___y_3427_ = v___y_3463_;
goto v___jp_3414_;
}
else
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3494_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13);
v___x_3495_ = lean_array_to_list(v_a_3408_);
v___x_3496_ = lean_box(0);
v___x_3497_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(v___x_3495_, v___x_3496_);
v___x_3498_ = l_Lean_MessageData_ofList(v___x_3497_);
v___x_3499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3494_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
v___x_3500_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v___x_3491_, v___x_3499_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_dec_ref_known(v___x_3500_, 1);
v___y_3415_ = v___x_3491_;
v___y_3416_ = v___y_3454_;
v___y_3417_ = v___y_3455_;
v___y_3418_ = v___y_3456_;
v___y_3419_ = v___y_3457_;
v___y_3420_ = v___y_3458_;
v___y_3421_ = v___y_3459_;
v___y_3422_ = v___y_3460_;
v___y_3423_ = v___y_3461_;
v___y_3424_ = v___y_3462_;
v_options_3425_ = v_options_3487_;
v_inheritedTraceOptions_3426_ = v_inheritedTraceOptions_3490_;
v___y_3427_ = v___y_3463_;
goto v___jp_3414_;
}
else
{
lean_dec_ref(v___x_3413_);
return v___x_3500_;
}
}
}
}
else
{
lean_dec_ref(v___x_3413_);
lean_dec(v_a_3408_);
return v___x_3485_;
}
}
else
{
lean_dec_ref(v___x_3476_);
lean_dec_ref(v___x_3413_);
lean_dec(v_a_3408_);
return v___x_3483_;
}
}
else
{
lean_dec_ref(v___x_3476_);
lean_dec_ref(v___x_3473_);
lean_dec_ref(v___x_3413_);
lean_dec(v_a_3408_);
return v___x_3481_;
}
}
else
{
lean_dec_ref(v___x_3476_);
lean_dec_ref(v___x_3473_);
lean_dec_ref(v___x_3469_);
lean_dec_ref(v___x_3413_);
lean_dec(v_a_3408_);
return v___x_3478_;
}
}
else
{
lean_dec_ref(v___f_3452_);
lean_dec_ref(v___x_3413_);
lean_dec(v_a_3408_);
lean_dec_ref(v_diseqs_3403_);
lean_dec_ref(v_uppers_3402_);
lean_dec_ref(v_lowers_3401_);
lean_dec_ref(v_dvds_3400_);
return v___x_3464_;
}
}
}
v___jp_3414_:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; 
v___x_3428_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1));
lean_inc(v___y_3415_);
v___x_3429_ = l_Lean_Name_append(v___x_3428_, v___y_3415_);
v___x_3430_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3426_, v_options_3425_, v___x_3429_);
lean_dec(v___x_3429_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3431_; 
lean_dec(v___y_3415_);
lean_dec_ref(v___x_3413_);
v___x_3431_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3427_);
return v___x_3431_;
}
else
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3432_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3);
v___x_3433_ = lean_array_to_list(v___x_3413_);
v___x_3434_ = lean_box(0);
v___x_3435_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(v___x_3433_, v___x_3434_);
v___x_3436_ = l_Lean_MessageData_ofList(v___x_3435_);
v___x_3437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3432_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
v___x_3438_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v___y_3415_, v___x_3437_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3427_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v___x_3439_; 
lean_dec_ref_known(v___x_3438_, 1);
v___x_3439_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3427_);
return v___x_3439_;
}
else
{
return v___x_3438_;
}
}
}
}
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
lean_dec(v_a_3406_);
lean_dec_ref(v_diseqs_3403_);
lean_dec_ref(v_uppers_3402_);
lean_dec_ref(v_lowers_3401_);
lean_dec_ref(v_dvds_3400_);
lean_dec_ref(v_varsHistory_3399_);
lean_dec_ref(v_vars_3398_);
v_a_3514_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3407_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3407_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
lean_dec_ref(v_diseqs_3403_);
lean_dec_ref(v_uppers_3402_);
lean_dec_ref(v_lowers_3401_);
lean_dec_ref(v_dvds_3400_);
lean_dec_ref(v_varsHistory_3399_);
lean_dec_ref(v_vars_3398_);
v_a_3522_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___x_3405_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3405_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
else
{
lean_object* v___x_3530_; lean_object* v___x_3532_; 
lean_dec_ref(v_diseqs_3403_);
lean_dec_ref(v_uppers_3402_);
lean_dec_ref(v_lowers_3401_);
lean_dec_ref(v_dvds_3400_);
lean_dec_ref(v_varsHistory_3399_);
lean_dec_ref(v_vars_3398_);
v___x_3530_ = lean_box(0);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3530_);
v___x_3532_ = v___x_3396_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
v_a_3535_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3393_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3393_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___boxed(lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
lean_dec(v_a_3552_);
lean_dec_ref(v_a_3551_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
lean_dec(v_a_3548_);
lean_dec_ref(v_a_3547_);
lean_dec(v_a_3546_);
lean_dec_ref(v_a_3545_);
lean_dec(v_a_3544_);
lean_dec(v_a_3543_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(lean_object* v_00_u03b2_3555_, lean_object* v_00_u03c3_3556_, lean_object* v_pm_3557_, lean_object* v_f_3558_){
_start:
{
lean_object* v___x_3559_; 
v___x_3559_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg(v_pm_3557_, v_f_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18(lean_object* v_cls_3560_, lean_object* v_msg_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v_cls_3560_, v_msg_3561_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___boxed(lean_object* v_cls_3574_, lean_object* v_msg_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18(v_cls_3574_, v_msg_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec(v___y_3576_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___redArg(lean_object* v_pm_3588_, lean_object* v_f_3589_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(v_f_3589_, v_pm_3588_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1(lean_object* v_00_u03b2_3591_, lean_object* v_00_u03c3_3592_, lean_object* v_pm_3593_, lean_object* v_f_3594_){
_start:
{
lean_object* v___x_3595_; 
v___x_3595_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(v_f_3594_, v_pm_3593_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_3596_, lean_object* v_00_u03b2_3597_, lean_object* v_00_u03c3_3598_, lean_object* v_f_3599_, lean_object* v_n_3600_){
_start:
{
lean_object* v___x_3601_; 
v___x_3601_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(v_f_3599_, v_n_3600_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21(lean_object* v_00_u03b1_3602_, lean_object* v_00_u03b2_3603_, lean_object* v_00_u03c3_3604_, lean_object* v_f_3605_, size_t v_sz_3606_, size_t v_i_3607_, lean_object* v_bs_3608_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg(v_f_3605_, v_sz_3606_, v_i_3607_, v_bs_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___boxed(lean_object* v_00_u03b1_3610_, lean_object* v_00_u03b2_3611_, lean_object* v_00_u03c3_3612_, lean_object* v_f_3613_, lean_object* v_sz_3614_, lean_object* v_i_3615_, lean_object* v_bs_3616_){
_start:
{
size_t v_sz_boxed_3617_; size_t v_i_boxed_3618_; lean_object* v_res_3619_; 
v_sz_boxed_3617_ = lean_unbox_usize(v_sz_3614_);
lean_dec(v_sz_3614_);
v_i_boxed_3618_ = lean_unbox_usize(v_i_3615_);
lean_dec(v_i_3615_);
v_res_3619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21(v_00_u03b1_3610_, v_00_u03b2_3611_, v_00_u03c3_3612_, v_f_3613_, v_sz_boxed_3617_, v_i_boxed_3618_, v_bs_3616_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22(lean_object* v_00_u03b1_3620_, lean_object* v_00_u03b2_3621_, lean_object* v_f_3622_, lean_object* v_as_3623_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg(v_f_3622_, v_as_3623_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___boxed(lean_object* v_00_u03b1_3625_, lean_object* v_00_u03b2_3626_, lean_object* v_f_3627_, lean_object* v_as_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22(v_00_u03b1_3625_, v_00_u03b2_3626_, v_f_3627_, v_as_3628_);
lean_dec_ref(v_as_3628_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42(lean_object* v_00_u03b1_3630_, lean_object* v_00_u03b2_3631_, lean_object* v_f_3632_, lean_object* v_as_3633_, lean_object* v_i_3634_, lean_object* v_acc_3635_, lean_object* v_hle_3636_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg(v_f_3632_, v_as_3633_, v_i_3634_, v_acc_3635_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___boxed(lean_object* v_00_u03b1_3638_, lean_object* v_00_u03b2_3639_, lean_object* v_f_3640_, lean_object* v_as_3641_, lean_object* v_i_3642_, lean_object* v_acc_3643_, lean_object* v_hle_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42(v_00_u03b1_3638_, v_00_u03b2_3639_, v_f_3640_, v_as_3641_, v_i_3642_, v_acc_3643_, v_hle_3644_);
lean_dec_ref(v_as_3641_);
return v_res_3645_;
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
