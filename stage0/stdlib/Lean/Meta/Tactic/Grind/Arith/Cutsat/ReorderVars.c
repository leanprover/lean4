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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_norm(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Int_Linear_instBEqPoly_beq(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Int_Linear_Poly_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_reorder___boxed(lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "search"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reorder"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value),LEAN_SCALAR_PTR_LITERAL(116, 65, 210, 255, 142, 133, 148, 120)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value),LEAN_SCALAR_PTR_LITERAL(236, 159, 191, 181, 87, 7, 198, 44)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "old2new: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "new2old: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_v_16_; lean_object* v_maxLowerCoeff_17_; lean_object* v_xs_x27_18_; lean_object* v___y_20_; uint8_t v___x_32_; 
v_v_16_ = lean_array_fget(v_a_7_, v_x_6_);
v_maxLowerCoeff_17_ = lean_ctor_get(v_v_16_, 0);
v_xs_x27_18_ = lean_array_fset(v_a_7_, v_x_6_, v___x_9_);
v___x_32_ = lean_nat_dec_le(v_a_5_, v_maxLowerCoeff_17_);
if (v___x_32_ == 0)
{
v___y_20_ = v_a_5_;
goto v___jp_19_;
}
else
{
lean_dec(v_a_5_);
lean_inc(v_maxLowerCoeff_17_);
v___y_20_ = v_maxLowerCoeff_17_;
goto v___jp_19_;
}
v___jp_19_:
{
lean_object* v_maxUpperCoeff_21_; lean_object* v_maxDvdCoeff_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_30_; 
v_maxUpperCoeff_21_ = lean_ctor_get(v_v_16_, 1);
v_maxDvdCoeff_22_ = lean_ctor_get(v_v_16_, 2);
v_isSharedCheck_30_ = !lean_is_exclusive(v_v_16_);
if (v_isSharedCheck_30_ == 0)
{
lean_object* v_unused_31_; 
v_unused_31_ = lean_ctor_get(v_v_16_, 0);
lean_dec(v_unused_31_);
v___x_24_ = v_v_16_;
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_maxDvdCoeff_22_);
lean_inc(v_maxUpperCoeff_21_);
lean_dec(v_v_16_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 0, v___y_20_);
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___y_20_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_maxUpperCoeff_21_);
lean_ctor_set(v_reuseFailAlloc_29_, 2, v_maxDvdCoeff_22_);
v___x_27_ = v_reuseFailAlloc_29_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
lean_object* v___x_28_; 
v___x_28_ = lean_array_fset(v_xs_x27_18_, v_x_6_, v___x_27_);
v___y_11_ = v___x_28_;
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
lean_object* v_v_79_; lean_object* v_maxLowerCoeff_80_; lean_object* v_maxUpperCoeff_81_; lean_object* v_maxDvdCoeff_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_94_; 
v_v_79_ = lean_array_fget(v_a_70_, v_x_69_);
v_maxLowerCoeff_80_ = lean_ctor_get(v_v_79_, 0);
v_maxUpperCoeff_81_ = lean_ctor_get(v_v_79_, 1);
v_maxDvdCoeff_82_ = lean_ctor_get(v_v_79_, 2);
v_isSharedCheck_94_ = !lean_is_exclusive(v_v_79_);
if (v_isSharedCheck_94_ == 0)
{
v___x_84_ = v_v_79_;
v_isShared_85_ = v_isSharedCheck_94_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_maxDvdCoeff_82_);
lean_inc(v_maxUpperCoeff_81_);
lean_inc(v_maxLowerCoeff_80_);
lean_dec(v_v_79_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_94_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v_xs_x27_86_; lean_object* v___y_88_; uint8_t v___x_93_; 
v_xs_x27_86_ = lean_array_fset(v_a_70_, v_x_69_, v___x_72_);
v___x_93_ = lean_nat_dec_le(v_a_68_, v_maxUpperCoeff_81_);
if (v___x_93_ == 0)
{
lean_dec(v_maxUpperCoeff_81_);
v___y_88_ = v_a_68_;
goto v___jp_87_;
}
else
{
lean_dec(v_a_68_);
v___y_88_ = v_maxUpperCoeff_81_;
goto v___jp_87_;
}
v___jp_87_:
{
lean_object* v___x_90_; 
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v___y_88_);
v___x_90_ = v___x_84_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_maxLowerCoeff_80_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v___y_88_);
lean_ctor_set(v_reuseFailAlloc_92_, 2, v_maxDvdCoeff_82_);
v___x_90_ = v_reuseFailAlloc_92_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; 
v___x_91_ = lean_array_fset(v_xs_x27_86_, v_x_69_, v___x_90_);
v___y_74_ = v___x_91_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg___boxed(lean_object* v_a_95_, lean_object* v_x_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_95_, v_x_96_, v_a_97_);
lean_dec(v_x_96_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(lean_object* v_a_100_, lean_object* v_x_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_100_, v_x_101_, v_a_102_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___boxed(lean_object* v_a_115_, lean_object* v_x_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(v_a_115_, v_x_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec(v_a_118_);
lean_dec(v_x_116_);
return v_res_129_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_nat_to_int(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(lean_object* v_a_132_, lean_object* v_x_133_, lean_object* v_a_134_){
_start:
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0);
v___x_137_ = lean_int_dec_lt(v_a_132_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_nat_abs(v_a_132_);
v___x_139_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v___x_138_, v_x_133_, v_a_134_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_nat_abs(v_a_132_);
v___x_141_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v___x_140_, v_x_133_, v_a_134_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___boxed(lean_object* v_a_142_, lean_object* v_x_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_142_, v_x_143_, v_a_144_);
lean_dec(v_x_143_);
lean_dec(v_a_142_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(lean_object* v_a_147_, lean_object* v_x_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_147_, v_x_148_, v_a_149_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___boxed(lean_object* v_a_162_, lean_object* v_x_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(v_a_162_, v_x_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec(v_a_165_);
lean_dec(v_x_163_);
lean_dec(v_a_162_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(lean_object* v_a_177_, lean_object* v_x_178_, lean_object* v_a_179_){
_start:
{
lean_object* v___x_181_; lean_object* v___y_183_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_181_ = lean_box(0);
v___x_186_ = lean_array_get_size(v_a_179_);
v___x_187_ = lean_nat_dec_lt(v_x_178_, v___x_186_);
if (v___x_187_ == 0)
{
lean_dec(v_a_177_);
v___y_183_ = v_a_179_;
goto v___jp_182_;
}
else
{
lean_object* v_v_188_; lean_object* v_maxLowerCoeff_189_; lean_object* v_maxUpperCoeff_190_; lean_object* v_maxDvdCoeff_191_; lean_object* v_xs_x27_192_; uint8_t v___x_193_; 
v_v_188_ = lean_array_fget(v_a_179_, v_x_178_);
v_maxLowerCoeff_189_ = lean_ctor_get(v_v_188_, 0);
v_maxUpperCoeff_190_ = lean_ctor_get(v_v_188_, 1);
v_maxDvdCoeff_191_ = lean_ctor_get(v_v_188_, 2);
v_xs_x27_192_ = lean_array_fset(v_a_179_, v_x_178_, v___x_181_);
v___x_193_ = lean_nat_dec_le(v_a_177_, v_maxDvdCoeff_191_);
if (v___x_193_ == 0)
{
lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_201_; 
lean_inc(v_maxUpperCoeff_190_);
lean_inc(v_maxLowerCoeff_189_);
v_isSharedCheck_201_ = !lean_is_exclusive(v_v_188_);
if (v_isSharedCheck_201_ == 0)
{
lean_object* v_unused_202_; lean_object* v_unused_203_; lean_object* v_unused_204_; 
v_unused_202_ = lean_ctor_get(v_v_188_, 2);
lean_dec(v_unused_202_);
v_unused_203_ = lean_ctor_get(v_v_188_, 1);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_v_188_, 0);
lean_dec(v_unused_204_);
v___x_195_ = v_v_188_;
v_isShared_196_ = v_isSharedCheck_201_;
goto v_resetjp_194_;
}
else
{
lean_dec(v_v_188_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_201_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 2, v_a_177_);
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_maxLowerCoeff_189_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_maxUpperCoeff_190_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_a_177_);
v___x_198_ = v_reuseFailAlloc_200_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; 
v___x_199_ = lean_array_fset(v_xs_x27_192_, v_x_178_, v___x_198_);
v___y_183_ = v___x_199_;
goto v___jp_182_;
}
}
}
else
{
lean_object* v___x_205_; 
lean_dec(v_a_177_);
v___x_205_ = lean_array_fset(v_xs_x27_192_, v_x_178_, v_v_188_);
v___y_183_ = v___x_205_;
goto v___jp_182_;
}
}
v___jp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_181_);
lean_ctor_set(v___x_184_, 1, v___y_183_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg___boxed(lean_object* v_a_206_, lean_object* v_x_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_206_, v_x_207_, v_a_208_);
lean_dec(v_x_207_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(lean_object* v_a_211_, lean_object* v_x_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_211_, v_x_212_, v_a_213_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___boxed(lean_object* v_a_226_, lean_object* v_x_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(v_a_226_, v_x_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
lean_dec(v_a_230_);
lean_dec(v_a_229_);
lean_dec(v_x_227_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
if (lean_obj_tag(v_a_241_) == 0)
{
lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_252_; 
v_isSharedCheck_252_ = !lean_is_exclusive(v_a_241_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; 
v_unused_253_ = lean_ctor_get(v_a_241_, 0);
lean_dec(v_unused_253_);
v___x_245_ = v_a_241_;
v_isShared_246_ = v_isSharedCheck_252_;
goto v_resetjp_244_;
}
else
{
lean_dec(v_a_241_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_252_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_247_ = lean_box(0);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v_a_242_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_248_);
v___x_250_ = v___x_245_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
else
{
lean_object* v_k_254_; lean_object* v_v_255_; lean_object* v_p_256_; lean_object* v___x_257_; lean_object* v_a_258_; lean_object* v_snd_259_; 
v_k_254_ = lean_ctor_get(v_a_241_, 0);
lean_inc(v_k_254_);
v_v_255_ = lean_ctor_get(v_a_241_, 1);
lean_inc(v_v_255_);
v_p_256_ = lean_ctor_get(v_a_241_, 2);
lean_inc_ref(v_p_256_);
lean_dec_ref(v_a_241_);
v___x_257_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_k_254_, v_v_255_, v_a_242_);
lean_dec(v_v_255_);
lean_dec(v_k_254_);
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref(v___x_257_);
v_snd_259_ = lean_ctor_get(v_a_258_, 1);
lean_inc(v_snd_259_);
lean_dec(v_a_258_);
v_a_241_ = v_p_256_;
v_a_242_ = v_snd_259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg___boxed(lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_261_, v_a_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_265_, v_a_266_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___boxed(lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec(v_a_281_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(lean_object* v_as_296_, size_t v_sz_297_, size_t v_i_298_, lean_object* v_b_299_, lean_object* v___y_300_){
_start:
{
uint8_t v___x_302_; 
v___x_302_ = lean_usize_dec_lt(v_i_298_, v_sz_297_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v_b_299_);
lean_ctor_set(v___x_303_, 1, v___y_300_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v_a_305_; lean_object* v_p_306_; lean_object* v___x_307_; 
lean_dec_ref(v_b_299_);
v_a_305_ = lean_array_uget_borrowed(v_as_296_, v_i_298_);
v_p_306_ = lean_ctor_get(v_a_305_, 0);
lean_inc_ref(v_p_306_);
v___x_307_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_306_, v___y_300_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v_snd_309_; lean_object* v___x_310_; size_t v___x_311_; size_t v___x_312_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref(v___x_307_);
v_snd_309_ = lean_ctor_get(v_a_308_, 1);
lean_inc(v_snd_309_);
lean_dec(v_a_308_);
v___x_310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_311_ = ((size_t)1ULL);
v___x_312_ = lean_usize_add(v_i_298_, v___x_311_);
v_i_298_ = v___x_312_;
v_b_299_ = v___x_310_;
v___y_300_ = v_snd_309_;
goto _start;
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
v_a_314_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_307_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_307_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_as_322_, lean_object* v_sz_323_, lean_object* v_i_324_, lean_object* v_b_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
size_t v_sz_boxed_328_; size_t v_i_boxed_329_; lean_object* v_res_330_; 
v_sz_boxed_328_ = lean_unbox_usize(v_sz_323_);
lean_dec(v_sz_323_);
v_i_boxed_329_ = lean_unbox_usize(v_i_324_);
lean_dec(v_i_324_);
v_res_330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_322_, v_sz_boxed_328_, v_i_boxed_329_, v_b_325_, v___y_326_);
lean_dec_ref(v_as_322_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(lean_object* v_as_331_, size_t v_sz_332_, size_t v_i_333_, lean_object* v_b_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
uint8_t v___x_347_; 
v___x_347_ = lean_usize_dec_lt(v_i_333_, v_sz_332_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v_b_334_);
lean_ctor_set(v___x_348_, 1, v___y_335_);
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
else
{
lean_object* v_a_350_; lean_object* v_p_351_; lean_object* v___x_352_; 
lean_dec_ref(v_b_334_);
v_a_350_ = lean_array_uget_borrowed(v_as_331_, v_i_333_);
v_p_351_ = lean_ctor_get(v_a_350_, 0);
lean_inc_ref(v_p_351_);
v___x_352_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_351_, v___y_335_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v_snd_354_; lean_object* v___x_355_; size_t v___x_356_; size_t v___x_357_; lean_object* v___x_358_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref(v___x_352_);
v_snd_354_ = lean_ctor_get(v_a_353_, 1);
lean_inc(v_snd_354_);
lean_dec(v_a_353_);
v___x_355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_356_ = ((size_t)1ULL);
v___x_357_ = lean_usize_add(v_i_333_, v___x_356_);
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_331_, v_sz_332_, v___x_357_, v___x_355_, v_snd_354_);
return v___x_358_;
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_a_359_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_352_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_352_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1___boxed(lean_object* v_as_367_, lean_object* v_sz_368_, lean_object* v_i_369_, lean_object* v_b_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
size_t v_sz_boxed_383_; size_t v_i_boxed_384_; lean_object* v_res_385_; 
v_sz_boxed_383_ = lean_unbox_usize(v_sz_368_);
lean_dec(v_sz_368_);
v_i_boxed_384_ = lean_unbox_usize(v_i_369_);
lean_dec(v_i_369_);
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_as_367_, v_sz_boxed_383_, v_i_boxed_384_, v_b_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v_as_367_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_as_389_, size_t v_sz_390_, size_t v_i_391_, lean_object* v_b_392_, lean_object* v___y_393_){
_start:
{
uint8_t v___x_395_; 
v___x_395_ = lean_usize_dec_lt(v_i_391_, v_sz_390_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v_b_392_);
lean_ctor_set(v___x_396_, 1, v___y_393_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
else
{
lean_object* v_a_398_; lean_object* v_p_399_; lean_object* v___x_400_; 
lean_dec_ref(v_b_392_);
v_a_398_ = lean_array_uget_borrowed(v_as_389_, v_i_391_);
v_p_399_ = lean_ctor_get(v_a_398_, 0);
lean_inc_ref(v_p_399_);
v___x_400_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_399_, v___y_393_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v_snd_402_; lean_object* v___x_403_; size_t v___x_404_; size_t v___x_405_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref(v___x_400_);
v_snd_402_ = lean_ctor_get(v_a_401_, 1);
lean_inc(v_snd_402_);
lean_dec(v_a_401_);
v___x_403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0));
v___x_404_ = ((size_t)1ULL);
v___x_405_ = lean_usize_add(v_i_391_, v___x_404_);
v_i_391_ = v___x_405_;
v_b_392_ = v___x_403_;
v___y_393_ = v_snd_402_;
goto _start;
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_400_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_400_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_as_415_, lean_object* v_sz_416_, lean_object* v_i_417_, lean_object* v_b_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
size_t v_sz_boxed_421_; size_t v_i_boxed_422_; lean_object* v_res_423_; 
v_sz_boxed_421_ = lean_unbox_usize(v_sz_416_);
lean_dec(v_sz_416_);
v_i_boxed_422_ = lean_unbox_usize(v_i_417_);
lean_dec(v_i_417_);
v_res_423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_415_, v_sz_boxed_421_, v_i_boxed_422_, v_b_418_, v___y_419_);
lean_dec_ref(v_as_415_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(lean_object* v_as_424_, size_t v_sz_425_, size_t v_i_426_, lean_object* v_b_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = lean_usize_dec_lt(v_i_426_, v_sz_425_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v_b_427_);
lean_ctor_set(v___x_441_, 1, v___y_428_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
else
{
lean_object* v_a_443_; lean_object* v_p_444_; lean_object* v___x_445_; 
lean_dec_ref(v_b_427_);
v_a_443_ = lean_array_uget_borrowed(v_as_424_, v_i_426_);
v_p_444_ = lean_ctor_get(v_a_443_, 0);
lean_inc_ref(v_p_444_);
v___x_445_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_444_, v___y_428_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v_snd_447_; lean_object* v___x_448_; size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref(v___x_445_);
v_snd_447_ = lean_ctor_get(v_a_446_, 1);
lean_inc(v_snd_447_);
lean_dec(v_a_446_);
v___x_448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0));
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_426_, v___x_449_);
v___x_451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_424_, v_sz_425_, v___x_450_, v___x_448_, v_snd_447_);
return v___x_451_;
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
v_a_452_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_445_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_445_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2___boxed(lean_object* v_as_460_, lean_object* v_sz_461_, lean_object* v_i_462_, lean_object* v_b_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
size_t v_sz_boxed_476_; size_t v_i_boxed_477_; lean_object* v_res_478_; 
v_sz_boxed_476_ = lean_unbox_usize(v_sz_461_);
lean_dec(v_sz_461_);
v_i_boxed_477_ = lean_unbox_usize(v_i_462_);
lean_dec(v_i_462_);
v_res_478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_as_460_, v_sz_boxed_476_, v_i_boxed_477_, v_b_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v_as_460_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(lean_object* v_init_479_, lean_object* v_n_480_, lean_object* v_b_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
if (lean_obj_tag(v_n_480_) == 0)
{
lean_object* v_cs_494_; lean_object* v___x_495_; lean_object* v___x_496_; size_t v_sz_497_; size_t v___x_498_; lean_object* v___x_499_; 
v_cs_494_ = lean_ctor_get(v_n_480_, 0);
v___x_495_ = lean_box(0);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v_b_481_);
v_sz_497_ = lean_array_size(v_cs_494_);
v___x_498_ = ((size_t)0ULL);
v___x_499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_479_, v_cs_494_, v_sz_497_, v___x_498_, v___x_496_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_534_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_534_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_534_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_534_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v_fst_504_; lean_object* v_fst_505_; 
v_fst_504_ = lean_ctor_get(v_a_500_, 0);
lean_inc(v_fst_504_);
v_fst_505_ = lean_ctor_get(v_fst_504_, 0);
if (lean_obj_tag(v_fst_505_) == 0)
{
lean_object* v_snd_506_; lean_object* v_snd_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_518_; 
v_snd_506_ = lean_ctor_get(v_a_500_, 1);
lean_inc(v_snd_506_);
lean_dec(v_a_500_);
v_snd_507_ = lean_ctor_get(v_fst_504_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_fst_504_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v_fst_504_, 0);
lean_dec(v_unused_519_);
v___x_509_ = v_fst_504_;
v_isShared_510_ = v_isSharedCheck_518_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snd_507_);
lean_dec(v_fst_504_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_518_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v_snd_507_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v_snd_506_);
lean_ctor_set(v___x_509_, 0, v___x_511_);
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_snd_506_);
v___x_513_ = v_reuseFailAlloc_517_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_515_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_513_);
v___x_515_ = v___x_502_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_531_; 
lean_inc_ref(v_fst_505_);
v_isSharedCheck_531_ = !lean_is_exclusive(v_fst_504_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; lean_object* v_unused_533_; 
v_unused_532_ = lean_ctor_get(v_fst_504_, 1);
lean_dec(v_unused_532_);
v_unused_533_ = lean_ctor_get(v_fst_504_, 0);
lean_dec(v_unused_533_);
v___x_521_ = v_fst_504_;
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
else
{
lean_dec(v_fst_504_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v_snd_523_; lean_object* v_val_524_; lean_object* v___x_526_; 
v_snd_523_ = lean_ctor_get(v_a_500_, 1);
lean_inc(v_snd_523_);
lean_dec(v_a_500_);
v_val_524_ = lean_ctor_get(v_fst_505_, 0);
lean_inc(v_val_524_);
lean_dec_ref(v_fst_505_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v_snd_523_);
lean_ctor_set(v___x_521_, 0, v_val_524_);
v___x_526_ = v___x_521_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_val_524_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_snd_523_);
v___x_526_ = v_reuseFailAlloc_530_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_528_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_526_);
v___x_528_ = v___x_502_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
v_a_535_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_499_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_499_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_object* v_vs_543_; lean_object* v___x_544_; lean_object* v___x_545_; size_t v_sz_546_; size_t v___x_547_; lean_object* v___x_548_; 
v_vs_543_ = lean_ctor_get(v_n_480_, 0);
v___x_544_ = lean_box(0);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v_b_481_);
v_sz_546_ = lean_array_size(v_vs_543_);
v___x_547_ = ((size_t)0ULL);
v___x_548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_vs_543_, v_sz_546_, v___x_547_, v___x_545_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_583_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_583_ == 0)
{
v___x_551_ = v___x_548_;
v_isShared_552_ = v_isSharedCheck_583_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_583_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v_fst_553_; lean_object* v_fst_554_; 
v_fst_553_ = lean_ctor_get(v_a_549_, 0);
lean_inc(v_fst_553_);
v_fst_554_ = lean_ctor_get(v_fst_553_, 0);
if (lean_obj_tag(v_fst_554_) == 0)
{
lean_object* v_snd_555_; lean_object* v_snd_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_567_; 
v_snd_555_ = lean_ctor_get(v_a_549_, 1);
lean_inc(v_snd_555_);
lean_dec(v_a_549_);
v_snd_556_ = lean_ctor_get(v_fst_553_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_fst_553_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v_fst_553_, 0);
lean_dec(v_unused_568_);
v___x_558_ = v_fst_553_;
v_isShared_559_ = v_isSharedCheck_567_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_snd_556_);
lean_dec(v_fst_553_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_567_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v_snd_556_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v_snd_555_);
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_snd_555_);
v___x_562_ = v_reuseFailAlloc_566_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_564_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_562_);
v___x_564_ = v___x_551_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
else
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_580_; 
lean_inc_ref(v_fst_554_);
v_isSharedCheck_580_ = !lean_is_exclusive(v_fst_553_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; lean_object* v_unused_582_; 
v_unused_581_ = lean_ctor_get(v_fst_553_, 1);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_fst_553_, 0);
lean_dec(v_unused_582_);
v___x_570_ = v_fst_553_;
v_isShared_571_ = v_isSharedCheck_580_;
goto v_resetjp_569_;
}
else
{
lean_dec(v_fst_553_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_580_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_snd_572_; lean_object* v_val_573_; lean_object* v___x_575_; 
v_snd_572_ = lean_ctor_get(v_a_549_, 1);
lean_inc(v_snd_572_);
lean_dec(v_a_549_);
v_val_573_ = lean_ctor_get(v_fst_554_, 0);
lean_inc(v_val_573_);
lean_dec_ref(v_fst_554_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v_snd_572_);
lean_ctor_set(v___x_570_, 0, v_val_573_);
v___x_575_ = v___x_570_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_val_573_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_snd_572_);
v___x_575_ = v_reuseFailAlloc_579_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_577_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_575_);
v___x_577_ = v___x_551_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
v_a_584_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_548_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_548_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(lean_object* v_init_592_, lean_object* v_as_593_, size_t v_sz_594_, size_t v_i_595_, lean_object* v_b_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = lean_usize_dec_lt(v_i_595_, v_sz_594_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v_b_596_);
lean_ctor_set(v___x_610_, 1, v___y_597_);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
else
{
lean_object* v_snd_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_662_; 
v_snd_612_ = lean_ctor_get(v_b_596_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_b_596_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v_b_596_, 0);
lean_dec(v_unused_663_);
v___x_614_ = v_b_596_;
v_isShared_615_ = v_isSharedCheck_662_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_snd_612_);
lean_dec(v_b_596_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_662_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_a_616_; lean_object* v___x_617_; 
v_a_616_ = lean_array_uget_borrowed(v_as_593_, v_i_595_);
lean_inc(v_snd_612_);
v___x_617_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_592_, v_a_616_, v_snd_612_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_653_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_653_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_653_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_653_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v_fst_622_; 
v_fst_622_ = lean_ctor_get(v_a_618_, 0);
lean_inc(v_fst_622_);
if (lean_obj_tag(v_fst_622_) == 0)
{
lean_object* v_snd_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_637_; 
v_snd_623_ = lean_ctor_get(v_a_618_, 1);
v_isSharedCheck_637_ = !lean_is_exclusive(v_a_618_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; 
v_unused_638_ = lean_ctor_get(v_a_618_, 0);
lean_dec(v_unused_638_);
v___x_625_ = v_a_618_;
v_isShared_626_ = v_isSharedCheck_637_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_snd_623_);
lean_dec(v_a_618_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_637_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v_fst_622_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v_snd_612_);
lean_ctor_set(v___x_625_, 0, v___x_627_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_snd_612_);
v___x_629_ = v_reuseFailAlloc_636_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v_snd_623_);
lean_ctor_set(v___x_614_, 0, v___x_629_);
v___x_631_ = v___x_614_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_snd_623_);
v___x_631_ = v_reuseFailAlloc_635_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_631_);
v___x_633_ = v___x_620_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
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
}
else
{
lean_object* v_snd_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_651_; 
lean_del_object(v___x_620_);
lean_del_object(v___x_614_);
lean_dec(v_snd_612_);
v_snd_639_ = lean_ctor_get(v_a_618_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_a_618_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v_a_618_, 0);
lean_dec(v_unused_652_);
v___x_641_ = v_a_618_;
v_isShared_642_ = v_isSharedCheck_651_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_snd_639_);
lean_dec(v_a_618_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_651_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_a_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v_a_643_ = lean_ctor_get(v_fst_622_, 0);
lean_inc(v_a_643_);
lean_dec_ref(v_fst_622_);
v___x_644_ = lean_box(0);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v_a_643_);
lean_ctor_set(v___x_641_, 0, v___x_644_);
v___x_646_ = v___x_641_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_a_643_);
v___x_646_ = v_reuseFailAlloc_650_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
size_t v___x_647_; size_t v___x_648_; 
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_add(v_i_595_, v___x_647_);
v_i_595_ = v___x_648_;
v_b_596_ = v___x_646_;
v___y_597_ = v_snd_639_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_del_object(v___x_614_);
lean_dec(v_snd_612_);
v_a_654_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_617_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_617_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_664_ = _args[0];
lean_object* v_as_665_ = _args[1];
lean_object* v_sz_666_ = _args[2];
lean_object* v_i_667_ = _args[3];
lean_object* v_b_668_ = _args[4];
lean_object* v___y_669_ = _args[5];
lean_object* v___y_670_ = _args[6];
lean_object* v___y_671_ = _args[7];
lean_object* v___y_672_ = _args[8];
lean_object* v___y_673_ = _args[9];
lean_object* v___y_674_ = _args[10];
lean_object* v___y_675_ = _args[11];
lean_object* v___y_676_ = _args[12];
lean_object* v___y_677_ = _args[13];
lean_object* v___y_678_ = _args[14];
lean_object* v___y_679_ = _args[15];
lean_object* v___y_680_ = _args[16];
_start:
{
size_t v_sz_boxed_681_; size_t v_i_boxed_682_; lean_object* v_res_683_; 
v_sz_boxed_681_ = lean_unbox_usize(v_sz_666_);
lean_dec(v_sz_666_);
v_i_boxed_682_ = lean_unbox_usize(v_i_667_);
lean_dec(v_i_667_);
v_res_683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_664_, v_as_665_, v_sz_boxed_681_, v_i_boxed_682_, v_b_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v_as_665_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0___boxed(lean_object* v_init_684_, lean_object* v_n_685_, lean_object* v_b_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_684_, v_n_685_, v_b_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v_n_685_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(lean_object* v_t_700_, lean_object* v_init_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_b_715_; lean_object* v___y_716_; lean_object* v_root_719_; lean_object* v_tail_720_; lean_object* v___x_721_; 
v_root_719_ = lean_ctor_get(v_t_700_, 0);
v_tail_720_ = lean_ctor_get(v_t_700_, 1);
v___x_721_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_701_, v_root_719_, v_init_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v_fst_723_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref(v___x_721_);
v_fst_723_ = lean_ctor_get(v_a_722_, 0);
lean_inc(v_fst_723_);
if (lean_obj_tag(v_fst_723_) == 0)
{
lean_object* v_snd_724_; lean_object* v_a_725_; 
v_snd_724_ = lean_ctor_get(v_a_722_, 1);
lean_inc(v_snd_724_);
lean_dec(v_a_722_);
v_a_725_ = lean_ctor_get(v_fst_723_, 0);
lean_inc(v_a_725_);
lean_dec_ref(v_fst_723_);
v_b_715_ = v_a_725_;
v___y_716_ = v_snd_724_;
goto v___jp_714_;
}
else
{
lean_object* v_snd_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_768_; 
v_snd_726_ = lean_ctor_get(v_a_722_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v_a_722_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v_a_722_, 0);
lean_dec(v_unused_769_);
v___x_728_ = v_a_722_;
v_isShared_729_ = v_isSharedCheck_768_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_snd_726_);
lean_dec(v_a_722_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_768_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v_a_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v_a_730_ = lean_ctor_get(v_fst_723_, 0);
lean_inc(v_a_730_);
lean_dec_ref(v_fst_723_);
v___x_731_ = lean_box(0);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v_a_730_);
lean_ctor_set(v___x_728_, 0, v___x_731_);
v___x_733_ = v___x_728_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_a_730_);
v___x_733_ = v_reuseFailAlloc_767_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
size_t v_sz_734_; size_t v___x_735_; lean_object* v___x_736_; 
v_sz_734_ = lean_array_size(v_tail_720_);
v___x_735_ = ((size_t)0ULL);
v___x_736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_tail_720_, v_sz_734_, v___x_735_, v___x_733_, v_snd_726_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_758_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_758_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_758_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_758_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v_fst_741_; lean_object* v_fst_742_; 
v_fst_741_ = lean_ctor_get(v_a_737_, 0);
lean_inc(v_fst_741_);
v_fst_742_ = lean_ctor_get(v_fst_741_, 0);
if (lean_obj_tag(v_fst_742_) == 0)
{
lean_object* v_snd_743_; lean_object* v_snd_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_754_; 
v_snd_743_ = lean_ctor_get(v_a_737_, 1);
lean_inc(v_snd_743_);
lean_dec(v_a_737_);
v_snd_744_ = lean_ctor_get(v_fst_741_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v_fst_741_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v_fst_741_, 0);
lean_dec(v_unused_755_);
v___x_746_ = v_fst_741_;
v_isShared_747_ = v_isSharedCheck_754_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_snd_744_);
lean_dec(v_fst_741_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_754_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v_snd_743_);
lean_ctor_set(v___x_746_, 0, v_snd_744_);
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_snd_744_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_snd_743_);
v___x_749_ = v_reuseFailAlloc_753_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_749_);
v___x_751_ = v___x_739_;
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
else
{
lean_object* v_snd_756_; lean_object* v_val_757_; 
lean_inc_ref(v_fst_742_);
lean_dec(v_fst_741_);
lean_del_object(v___x_739_);
v_snd_756_ = lean_ctor_get(v_a_737_, 1);
lean_inc(v_snd_756_);
lean_dec(v_a_737_);
v_val_757_ = lean_ctor_get(v_fst_742_, 0);
lean_inc(v_val_757_);
lean_dec_ref(v_fst_742_);
v_b_715_ = v_val_757_;
v___y_716_ = v_snd_756_;
goto v___jp_714_;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
v_a_759_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_736_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_736_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
v_a_770_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_721_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_721_);
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
v___jp_714_:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v_b_715_);
lean_ctor_set(v___x_717_, 1, v___y_716_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0___boxed(lean_object* v_t_778_, lean_object* v_init_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v_t_778_, v_init_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v_t_778_);
return v_res_792_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(lean_object* v_xs_793_, lean_object* v_i_794_){
_start:
{
lean_object* v_size_795_; uint8_t v___x_796_; 
v_size_795_ = lean_ctor_get(v_xs_793_, 2);
v___x_796_ = lean_nat_dec_lt(v_i_794_, v_size_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0___boxed(lean_object* v_xs_797_, lean_object* v_i_798_){
_start:
{
uint8_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_xs_797_, v_i_798_);
lean_dec(v_i_798_);
lean_dec_ref(v_xs_797_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(lean_object* v_a_802_, lean_object* v_range_803_, lean_object* v_b_804_, lean_object* v_i_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_stop_818_; lean_object* v_step_819_; uint8_t v___x_820_; 
v_stop_818_ = lean_ctor_get(v_range_803_, 1);
v_step_819_ = lean_ctor_get(v_range_803_, 2);
v___x_820_ = lean_nat_dec_lt(v_i_805_, v_stop_818_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec(v_i_805_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_b_804_);
lean_ctor_set(v___x_821_, 1, v___y_806_);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
else
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_i_805_, v___y_807_, v___y_815_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_825_; lean_object* v_snd_827_; lean_object* v___y_831_; lean_object* v___y_832_; uint8_t v___x_839_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref(v___x_823_);
v___x_825_ = lean_box(0);
v___x_839_ = lean_unbox(v_a_824_);
lean_dec(v_a_824_);
if (v___x_839_ == 0)
{
lean_object* v_dvds_840_; lean_object* v_lowers_841_; lean_object* v_uppers_842_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___x_854_; lean_object* v___y_856_; uint8_t v___x_863_; 
v_dvds_840_ = lean_ctor_get(v_a_802_, 6);
v_lowers_841_ = lean_ctor_get(v_a_802_, 7);
v_uppers_842_ = lean_ctor_get(v_a_802_, 8);
v___x_854_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0);
v___x_863_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_lowers_841_, v_i_805_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; 
v___x_864_ = l_outOfBounds___redArg(v___x_854_);
v___y_856_ = v___x_864_;
goto v___jp_855_;
}
else
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_PersistentArray_get_x21___redArg(v___x_854_, v_lowers_841_, v_i_805_);
v___y_856_ = v___x_865_;
goto v___jp_855_;
}
v___jp_843_:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v___y_845_, v___x_825_, v___y_844_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec_ref(v___y_845_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v_snd_848_; lean_object* v_size_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref(v___x_846_);
v_snd_848_ = lean_ctor_get(v_a_847_, 1);
lean_inc(v_snd_848_);
lean_dec(v_a_847_);
v_size_849_ = lean_ctor_get(v_dvds_840_, 2);
v___x_850_ = lean_box(0);
v___x_851_ = lean_nat_dec_lt(v_i_805_, v_size_849_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; 
v___x_852_ = l_outOfBounds___redArg(v___x_850_);
v___y_831_ = v_snd_848_;
v___y_832_ = v___x_852_;
goto v___jp_830_;
}
else
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_PersistentArray_get_x21___redArg(v___x_850_, v_dvds_840_, v_i_805_);
v___y_831_ = v_snd_848_;
v___y_832_ = v___x_853_;
goto v___jp_830_;
}
}
else
{
lean_dec(v_i_805_);
return v___x_846_;
}
}
v___jp_855_:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v___y_856_, v___x_825_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec_ref(v___y_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v_snd_859_; uint8_t v___x_860_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref(v___x_857_);
v_snd_859_ = lean_ctor_get(v_a_858_, 1);
lean_inc(v_snd_859_);
lean_dec(v_a_858_);
v___x_860_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_uppers_842_, v_i_805_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
v___x_861_ = l_outOfBounds___redArg(v___x_854_);
v___y_844_ = v_snd_859_;
v___y_845_ = v___x_861_;
goto v___jp_843_;
}
else
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentArray_get_x21___redArg(v___x_854_, v_uppers_842_, v_i_805_);
v___y_844_ = v_snd_859_;
v___y_845_ = v___x_862_;
goto v___jp_843_;
}
}
else
{
lean_dec(v_i_805_);
return v___x_857_;
}
}
}
else
{
v_snd_827_ = v___y_806_;
goto v___jp_826_;
}
v___jp_826_:
{
lean_object* v___x_828_; 
v___x_828_ = lean_nat_add(v_i_805_, v_step_819_);
lean_dec(v_i_805_);
v_b_804_ = v___x_825_;
v_i_805_ = v___x_828_;
v___y_806_ = v_snd_827_;
goto _start;
}
v___jp_830_:
{
if (lean_obj_tag(v___y_832_) == 1)
{
lean_object* v_val_833_; lean_object* v_d_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v_a_837_; lean_object* v_snd_838_; 
v_val_833_ = lean_ctor_get(v___y_832_, 0);
lean_inc(v_val_833_);
lean_dec_ref(v___y_832_);
v_d_834_ = lean_ctor_get(v_val_833_, 0);
lean_inc(v_d_834_);
lean_dec(v_val_833_);
v___x_835_ = lean_nat_abs(v_d_834_);
lean_dec(v_d_834_);
v___x_836_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v___x_835_, v_i_805_, v___y_831_);
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref(v___x_836_);
v_snd_838_ = lean_ctor_get(v_a_837_, 1);
lean_inc(v_snd_838_);
lean_dec(v_a_837_);
v_snd_827_ = v_snd_838_;
goto v___jp_826_;
}
else
{
lean_dec(v___y_832_);
v_snd_827_ = v___y_831_;
goto v___jp_826_;
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref(v___y_806_);
lean_dec(v_i_805_);
v_a_866_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_823_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_823_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___boxed(lean_object* v_a_874_, lean_object* v_range_875_, lean_object* v_b_876_, lean_object* v_i_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_874_, v_range_875_, v_b_876_, v_i_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v_range_875_);
lean_dec_ref(v_a_874_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_892_, v_a_900_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v_vars_905_; lean_object* v_size_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref(v___x_903_);
v_vars_905_ = lean_ctor_get(v_a_904_, 0);
v_size_906_ = lean_ctor_get(v_vars_905_, 2);
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = lean_unsigned_to_nat(1u);
lean_inc(v_size_906_);
v___x_909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v_size_906_);
lean_ctor_set(v___x_909_, 2, v___x_908_);
v___x_910_ = lean_box(0);
v___x_911_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_904_, v___x_909_, v___x_910_, v___x_907_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
lean_dec_ref(v___x_909_);
lean_dec(v_a_904_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_928_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_928_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_928_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_928_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v_snd_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_926_; 
v_snd_916_ = lean_ctor_get(v_a_912_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_a_912_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_a_912_, 0);
lean_dec(v_unused_927_);
v___x_918_ = v_a_912_;
v_isShared_919_ = v_isSharedCheck_926_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_snd_916_);
lean_dec(v_a_912_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_926_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_910_);
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_snd_916_);
v___x_921_ = v_reuseFailAlloc_925_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_923_; 
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_921_);
v___x_923_ = v___x_914_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
else
{
return v___x_911_;
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec_ref(v_a_891_);
v_a_929_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_903_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_903_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go___boxed(lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec(v_a_938_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(lean_object* v_a_950_, lean_object* v_range_951_, lean_object* v_b_952_, lean_object* v_i_953_, lean_object* v_hs_954_, lean_object* v_hl_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_950_, v_range_951_, v_b_952_, v_i_953_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___boxed(lean_object** _args){
lean_object* v_a_969_ = _args[0];
lean_object* v_range_970_ = _args[1];
lean_object* v_b_971_ = _args[2];
lean_object* v_i_972_ = _args[3];
lean_object* v_hs_973_ = _args[4];
lean_object* v_hl_974_ = _args[5];
lean_object* v___y_975_ = _args[6];
lean_object* v___y_976_ = _args[7];
lean_object* v___y_977_ = _args[8];
lean_object* v___y_978_ = _args[9];
lean_object* v___y_979_ = _args[10];
lean_object* v___y_980_ = _args[11];
lean_object* v___y_981_ = _args[12];
lean_object* v___y_982_ = _args[13];
lean_object* v___y_983_ = _args[14];
lean_object* v___y_984_ = _args[15];
lean_object* v___y_985_ = _args[16];
lean_object* v___y_986_ = _args[17];
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(v_a_969_, v_range_970_, v_b_971_, v_i_972_, v_hs_973_, v_hl_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v_range_970_);
lean_dec_ref(v_a_969_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(lean_object* v_as_988_, size_t v_sz_989_, size_t v_i_990_, lean_object* v_b_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_988_, v_sz_989_, v_i_990_, v_b_991_, v___y_992_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1005_, lean_object* v_sz_1006_, lean_object* v_i_1007_, lean_object* v_b_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
size_t v_sz_boxed_1021_; size_t v_i_boxed_1022_; lean_object* v_res_1023_; 
v_sz_boxed_1021_ = lean_unbox_usize(v_sz_1006_);
lean_dec(v_sz_1006_);
v_i_boxed_1022_ = lean_unbox_usize(v_i_1007_);
lean_dec(v_i_1007_);
v_res_1023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(v_as_1005_, v_sz_boxed_1021_, v_i_boxed_1022_, v_b_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v_as_1005_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(lean_object* v_as_1024_, size_t v_sz_1025_, size_t v_i_1026_, lean_object* v_b_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1024_, v_sz_1025_, v_i_1026_, v_b_1027_, v___y_1028_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_as_1041_, lean_object* v_sz_1042_, lean_object* v_i_1043_, lean_object* v_b_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
size_t v_sz_boxed_1057_; size_t v_i_boxed_1058_; lean_object* v_res_1059_; 
v_sz_boxed_1057_ = lean_unbox_usize(v_sz_1042_);
lean_dec(v_sz_1042_);
v_i_boxed_1058_ = lean_unbox_usize(v_i_1043_);
lean_dec(v_i_1043_);
v_res_1059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(v_as_1041_, v_sz_boxed_1057_, v_i_boxed_1058_, v_b_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v_as_1041_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1060_, v_a_1068_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v_vars_1073_; lean_object* v_size_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref(v___x_1071_);
v_vars_1073_ = lean_ctor_get(v_a_1072_, 0);
lean_inc_ref(v_vars_1073_);
lean_dec(v_a_1072_);
v_size_1074_ = lean_ctor_get(v_vars_1073_, 2);
lean_inc(v_size_1074_);
lean_dec_ref(v_vars_1073_);
v___x_1075_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0));
v___x_1076_ = lean_mk_array(v_size_1074_, v___x_1075_);
v___x_1077_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v___x_1076_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1086_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v_snd_1082_; lean_object* v___x_1084_; 
v_snd_1082_ = lean_ctor_get(v_a_1078_, 1);
lean_inc(v_snd_1082_);
lean_dec(v_a_1078_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v_snd_1082_);
v___x_1084_ = v___x_1080_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_snd_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
v_a_1087_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1077_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1077_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_a_1095_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1071_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1071_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo___boxed(lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec(v_a_1103_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(lean_object* v_info_1115_){
_start:
{
lean_object* v_maxLowerCoeff_1116_; lean_object* v_maxUpperCoeff_1117_; lean_object* v_maxDvdCoeff_1118_; lean_object* v___y_1120_; uint8_t v___x_1122_; 
v_maxLowerCoeff_1116_ = lean_ctor_get(v_info_1115_, 0);
v_maxUpperCoeff_1117_ = lean_ctor_get(v_info_1115_, 1);
v_maxDvdCoeff_1118_ = lean_ctor_get(v_info_1115_, 2);
v___x_1122_ = lean_nat_dec_le(v_maxLowerCoeff_1116_, v_maxUpperCoeff_1117_);
if (v___x_1122_ == 0)
{
v___y_1120_ = v_maxUpperCoeff_1117_;
goto v___jp_1119_;
}
else
{
v___y_1120_ = v_maxLowerCoeff_1116_;
goto v___jp_1119_;
}
v___jp_1119_:
{
uint8_t v___x_1121_; 
v___x_1121_ = lean_nat_dec_le(v_maxDvdCoeff_1118_, v___y_1120_);
if (v___x_1121_ == 0)
{
lean_inc(v_maxDvdCoeff_1118_);
return v_maxDvdCoeff_1118_;
}
else
{
lean_inc(v___y_1120_);
return v___y_1120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081___boxed(lean_object* v_info_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v_info_1123_);
lean_dec_ref(v_info_1123_);
return v_res_1124_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(lean_object* v_infos_1125_, lean_object* v_x_1126_, lean_object* v_y_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1128_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1129_ = lean_array_get_borrowed(v___x_1128_, v_infos_1125_, v_x_1126_);
v___x_1130_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_1129_);
v___x_1131_ = lean_array_get_borrowed(v___x_1128_, v_infos_1125_, v_y_1127_);
v___x_1132_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_1131_);
v___x_1133_ = lean_nat_dec_lt(v___x_1130_, v___x_1132_);
if (v___x_1133_ == 0)
{
uint8_t v___x_1134_; 
v___x_1134_ = lean_nat_dec_eq(v___x_1130_, v___x_1132_);
lean_dec(v___x_1132_);
lean_dec(v___x_1130_);
if (v___x_1134_ == 0)
{
uint8_t v___x_1135_; 
v___x_1135_ = 0;
return v___x_1135_;
}
else
{
uint8_t v___x_1136_; 
v___x_1136_ = 1;
return v___x_1136_;
}
}
else
{
uint8_t v___x_1137_; 
lean_dec(v___x_1132_);
lean_dec(v___x_1130_);
v___x_1137_ = 2;
return v___x_1137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081___boxed(lean_object* v_infos_1138_, lean_object* v_x_1139_, lean_object* v_y_1140_){
_start:
{
uint8_t v_res_1141_; lean_object* v_r_1142_; 
v_res_1141_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_1138_, v_x_1139_, v_y_1140_);
lean_dec(v_y_1140_);
lean_dec(v_x_1139_);
lean_dec_ref(v_infos_1138_);
v_r_1142_ = lean_box(v_res_1141_);
return v_r_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(lean_object* v_info_1143_){
_start:
{
lean_object* v_maxLowerCoeff_1144_; lean_object* v_maxUpperCoeff_1145_; lean_object* v_maxDvdCoeff_1146_; lean_object* v___y_1148_; uint8_t v___x_1150_; 
v_maxLowerCoeff_1144_ = lean_ctor_get(v_info_1143_, 0);
v_maxUpperCoeff_1145_ = lean_ctor_get(v_info_1143_, 1);
v_maxDvdCoeff_1146_ = lean_ctor_get(v_info_1143_, 2);
v___x_1150_ = lean_nat_dec_le(v_maxLowerCoeff_1144_, v_maxUpperCoeff_1145_);
if (v___x_1150_ == 0)
{
v___y_1148_ = v_maxLowerCoeff_1144_;
goto v___jp_1147_;
}
else
{
v___y_1148_ = v_maxUpperCoeff_1145_;
goto v___jp_1147_;
}
v___jp_1147_:
{
uint8_t v___x_1149_; 
v___x_1149_ = lean_nat_dec_le(v_maxDvdCoeff_1146_, v___y_1148_);
if (v___x_1149_ == 0)
{
lean_inc(v_maxDvdCoeff_1146_);
return v_maxDvdCoeff_1146_;
}
else
{
lean_inc(v___y_1148_);
return v___y_1148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082___boxed(lean_object* v_info_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v_info_1151_);
lean_dec_ref(v_info_1151_);
return v_res_1152_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(lean_object* v_infos_1153_, lean_object* v_x_1154_, lean_object* v_y_1155_){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1156_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1157_ = lean_array_get_borrowed(v___x_1156_, v_infos_1153_, v_x_1154_);
v___x_1158_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v___x_1157_);
v___x_1159_ = lean_array_get_borrowed(v___x_1156_, v_infos_1153_, v_y_1155_);
v___x_1160_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v___x_1159_);
v___x_1161_ = lean_nat_dec_lt(v___x_1158_, v___x_1160_);
if (v___x_1161_ == 0)
{
uint8_t v___x_1162_; 
v___x_1162_ = lean_nat_dec_eq(v___x_1158_, v___x_1160_);
lean_dec(v___x_1160_);
lean_dec(v___x_1158_);
if (v___x_1162_ == 0)
{
uint8_t v___x_1163_; 
v___x_1163_ = 0;
return v___x_1163_;
}
else
{
uint8_t v___x_1164_; 
v___x_1164_ = 1;
return v___x_1164_;
}
}
else
{
uint8_t v___x_1165_; 
lean_dec(v___x_1160_);
lean_dec(v___x_1158_);
v___x_1165_ = 2;
return v___x_1165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082___boxed(lean_object* v_infos_1166_, lean_object* v_x_1167_, lean_object* v_y_1168_){
_start:
{
uint8_t v_res_1169_; lean_object* v_r_1170_; 
v_res_1169_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_1166_, v_x_1167_, v_y_1168_);
lean_dec(v_y_1168_);
lean_dec(v_x_1167_);
lean_dec_ref(v_infos_1166_);
v_r_1170_ = lean_box(v_res_1169_);
return v_r_1170_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(lean_object* v_infos_1171_, lean_object* v_x_1172_, lean_object* v_y_1173_){
_start:
{
uint8_t v___y_1175_; uint8_t v___x_1180_; 
v___x_1180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_1171_, v_x_1172_, v_y_1173_);
if (v___x_1180_ == 1)
{
uint8_t v___x_1181_; 
v___x_1181_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_1171_, v_x_1172_, v_y_1173_);
v___y_1175_ = v___x_1181_;
goto v___jp_1174_;
}
else
{
v___y_1175_ = v___x_1180_;
goto v___jp_1174_;
}
v___jp_1174_:
{
if (v___y_1175_ == 1)
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_nat_dec_lt(v_x_1172_, v_y_1173_);
if (v___x_1176_ == 0)
{
uint8_t v___x_1177_; 
v___x_1177_ = lean_nat_dec_eq(v_x_1172_, v_y_1173_);
if (v___x_1177_ == 0)
{
uint8_t v___x_1178_; 
v___x_1178_ = 2;
return v___x_1178_;
}
else
{
return v___y_1175_;
}
}
else
{
uint8_t v___x_1179_; 
v___x_1179_ = 0;
return v___x_1179_;
}
}
else
{
return v___y_1175_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp___boxed(lean_object* v_infos_1182_, lean_object* v_x_1183_, lean_object* v_y_1184_){
_start:
{
uint8_t v_res_1185_; lean_object* v_r_1186_; 
v_res_1185_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_1182_, v_x_1183_, v_y_1184_);
lean_dec(v_y_1184_);
lean_dec(v_x_1183_);
lean_dec_ref(v_infos_1182_);
v_r_1186_ = lean_box(v_res_1185_);
return v_r_1186_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(lean_object* v_a_1187_, lean_object* v_x_1188_, lean_object* v_y_1189_){
_start:
{
uint8_t v___x_1190_; uint8_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1190_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_a_1187_, v_x_1188_, v_y_1189_);
v___x_1191_ = 0;
v___x_1192_ = l_instDecidableEqOrdering(v___x_1190_, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0___boxed(lean_object* v_a_1193_, lean_object* v_x_1194_, lean_object* v_y_1195_){
_start:
{
uint8_t v_res_1196_; lean_object* v_r_1197_; 
v_res_1196_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_a_1193_, v_x_1194_, v_y_1195_);
lean_dec(v_y_1195_);
lean_dec(v_x_1194_);
lean_dec_ref(v_a_1193_);
v_r_1197_ = lean_box(v_res_1196_);
return v_r_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(lean_object* v_a_1198_, lean_object* v_hi_1199_, lean_object* v_pivot_1200_, lean_object* v_as_1201_, lean_object* v_i_1202_, lean_object* v_k_1203_){
_start:
{
uint8_t v___x_1204_; 
v___x_1204_ = lean_nat_dec_lt(v_k_1203_, v_hi_1199_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec(v_k_1203_);
v___x_1205_ = lean_array_fswap(v_as_1201_, v_i_1202_, v_hi_1199_);
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v_i_1202_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
return v___x_1206_;
}
else
{
lean_object* v___x_1207_; uint8_t v___x_1208_; uint8_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1207_ = lean_array_fget_borrowed(v_as_1201_, v_k_1203_);
v___x_1208_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_a_1198_, v___x_1207_, v_pivot_1200_);
v___x_1209_ = 0;
v___x_1210_ = l_instDecidableEqOrdering(v___x_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_unsigned_to_nat(1u);
v___x_1212_ = lean_nat_add(v_k_1203_, v___x_1211_);
lean_dec(v_k_1203_);
v_k_1203_ = v___x_1212_;
goto _start;
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1214_ = lean_array_fswap(v_as_1201_, v_i_1202_, v_k_1203_);
v___x_1215_ = lean_unsigned_to_nat(1u);
v___x_1216_ = lean_nat_add(v_i_1202_, v___x_1215_);
lean_dec(v_i_1202_);
v___x_1217_ = lean_nat_add(v_k_1203_, v___x_1215_);
lean_dec(v_k_1203_);
v_as_1201_ = v___x_1214_;
v_i_1202_ = v___x_1216_;
v_k_1203_ = v___x_1217_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_1219_, lean_object* v_hi_1220_, lean_object* v_pivot_1221_, lean_object* v_as_1222_, lean_object* v_i_1223_, lean_object* v_k_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_a_1219_, v_hi_1220_, v_pivot_1221_, v_as_1222_, v_i_1223_, v_k_1224_);
lean_dec(v_pivot_1221_);
lean_dec(v_hi_1220_);
lean_dec_ref(v_a_1219_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(lean_object* v_a_1226_, lean_object* v_n_1227_, lean_object* v_as_1228_, lean_object* v_lo_1229_, lean_object* v_hi_1230_){
_start:
{
lean_object* v___y_1232_; uint8_t v___x_1242_; 
v___x_1242_ = lean_nat_dec_lt(v_lo_1229_, v_hi_1230_);
if (v___x_1242_ == 0)
{
lean_dec(v_lo_1229_);
return v_as_1228_;
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_mid_1245_; lean_object* v___y_1247_; lean_object* v___y_1253_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1243_ = lean_nat_add(v_lo_1229_, v_hi_1230_);
v___x_1244_ = lean_unsigned_to_nat(1u);
v_mid_1245_ = lean_nat_shiftr(v___x_1243_, v___x_1244_);
lean_dec(v___x_1243_);
v___x_1258_ = lean_array_fget_borrowed(v_as_1228_, v_mid_1245_);
v___x_1259_ = lean_array_fget_borrowed(v_as_1228_, v_lo_1229_);
v___x_1260_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_a_1226_, v___x_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
v___y_1253_ = v_as_1228_;
goto v___jp_1252_;
}
else
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_array_fswap(v_as_1228_, v_lo_1229_, v_mid_1245_);
v___y_1253_ = v___x_1261_;
goto v___jp_1252_;
}
v___jp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1248_ = lean_array_fget_borrowed(v___y_1247_, v_mid_1245_);
v___x_1249_ = lean_array_fget_borrowed(v___y_1247_, v_hi_1230_);
v___x_1250_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_a_1226_, v___x_1248_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_dec(v_mid_1245_);
v___y_1232_ = v___y_1247_;
goto v___jp_1231_;
}
else
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_array_fswap(v___y_1247_, v_mid_1245_, v_hi_1230_);
lean_dec(v_mid_1245_);
v___y_1232_ = v___x_1251_;
goto v___jp_1231_;
}
}
v___jp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1254_ = lean_array_fget_borrowed(v___y_1253_, v_hi_1230_);
v___x_1255_ = lean_array_fget_borrowed(v___y_1253_, v_lo_1229_);
v___x_1256_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_a_1226_, v___x_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
v___y_1247_ = v___y_1253_;
goto v___jp_1246_;
}
else
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_array_fswap(v___y_1253_, v_lo_1229_, v_hi_1230_);
v___y_1247_ = v___x_1257_;
goto v___jp_1246_;
}
}
}
v___jp_1231_:
{
lean_object* v_pivot_1233_; lean_object* v___x_1234_; lean_object* v_fst_1235_; lean_object* v_snd_1236_; uint8_t v___x_1237_; 
v_pivot_1233_ = lean_array_fget(v___y_1232_, v_hi_1230_);
lean_inc_n(v_lo_1229_, 2);
v___x_1234_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_a_1226_, v_hi_1230_, v_pivot_1233_, v___y_1232_, v_lo_1229_, v_lo_1229_);
lean_dec(v_pivot_1233_);
v_fst_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_fst_1235_);
v_snd_1236_ = lean_ctor_get(v___x_1234_, 1);
lean_inc(v_snd_1236_);
lean_dec_ref(v___x_1234_);
v___x_1237_ = lean_nat_dec_le(v_hi_1230_, v_fst_1235_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_a_1226_, v_n_1227_, v_snd_1236_, v_lo_1229_, v_fst_1235_);
v___x_1239_ = lean_unsigned_to_nat(1u);
v___x_1240_ = lean_nat_add(v_fst_1235_, v___x_1239_);
lean_dec(v_fst_1235_);
v_as_1228_ = v___x_1238_;
v_lo_1229_ = v___x_1240_;
goto _start;
}
else
{
lean_dec(v_fst_1235_);
lean_dec(v_lo_1229_);
return v_snd_1236_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___boxed(lean_object* v_a_1262_, lean_object* v_n_1263_, lean_object* v_as_1264_, lean_object* v_lo_1265_, lean_object* v_hi_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_a_1262_, v_n_1263_, v_as_1264_, v_lo_1265_, v_hi_1266_);
lean_dec(v_hi_1266_);
lean_dec(v_n_1263_);
lean_dec_ref(v_a_1262_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1320_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1320_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1320_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1268_, v_a_1276_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1311_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1311_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1311_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v_vars_1289_; lean_object* v_size_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_vars_1289_ = lean_ctor_get(v_a_1285_, 0);
lean_inc_ref(v_vars_1289_);
lean_dec(v_a_1285_);
v_size_1290_ = lean_ctor_get(v_vars_1289_, 2);
lean_inc(v_size_1290_);
lean_dec_ref(v_vars_1289_);
v___x_1291_ = l_Array_range(v_size_1290_);
v___x_1292_ = lean_array_get_size(v___x_1291_);
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = lean_nat_dec_eq(v___x_1292_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___y_1305_; uint8_t v___x_1307_; 
lean_del_object(v___x_1282_);
v___x_1302_ = lean_unsigned_to_nat(1u);
v___x_1303_ = lean_nat_sub(v___x_1292_, v___x_1302_);
v___x_1307_ = lean_nat_dec_le(v___x_1300_, v___x_1303_);
if (v___x_1307_ == 0)
{
lean_inc(v___x_1303_);
v___y_1305_ = v___x_1303_;
goto v___jp_1304_;
}
else
{
v___y_1305_ = v___x_1300_;
goto v___jp_1304_;
}
v___jp_1304_:
{
uint8_t v___x_1306_; 
v___x_1306_ = lean_nat_dec_le(v___y_1305_, v___x_1303_);
if (v___x_1306_ == 0)
{
lean_dec(v___x_1303_);
lean_inc(v___y_1305_);
v___y_1294_ = v___y_1305_;
v___y_1295_ = v___y_1305_;
goto v___jp_1293_;
}
else
{
v___y_1294_ = v___y_1305_;
v___y_1295_ = v___x_1303_;
goto v___jp_1293_;
}
}
}
else
{
lean_object* v___x_1309_; 
lean_del_object(v___x_1287_);
lean_dec(v_a_1280_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v___x_1291_);
v___x_1309_ = v___x_1282_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1291_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
v___jp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1296_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_a_1280_, v___x_1292_, v___x_1291_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec(v_a_1280_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1296_);
v___x_1298_ = v___x_1287_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_del_object(v___x_1282_);
lean_dec(v_a_1280_);
v_a_1312_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1284_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1284_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
v_a_1321_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1279_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1279_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___boxed(lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
lean_dec(v_a_1332_);
lean_dec_ref(v_a_1331_);
lean_dec(v_a_1330_);
lean_dec(v_a_1329_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(lean_object* v_a_1341_, lean_object* v_n_1342_, lean_object* v_as_1343_, lean_object* v_lo_1344_, lean_object* v_hi_1345_, lean_object* v_w_1346_, lean_object* v_hlo_1347_, lean_object* v_hhi_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_a_1341_, v_n_1342_, v_as_1343_, v_lo_1344_, v_hi_1345_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___boxed(lean_object* v_a_1350_, lean_object* v_n_1351_, lean_object* v_as_1352_, lean_object* v_lo_1353_, lean_object* v_hi_1354_, lean_object* v_w_1355_, lean_object* v_hlo_1356_, lean_object* v_hhi_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(v_a_1350_, v_n_1351_, v_as_1352_, v_lo_1353_, v_hi_1354_, v_w_1355_, v_hlo_1356_, v_hhi_1357_);
lean_dec(v_hi_1354_);
lean_dec(v_n_1351_);
lean_dec_ref(v_a_1350_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0(lean_object* v_a_1359_, lean_object* v_n_1360_, lean_object* v_lo_1361_, lean_object* v_hi_1362_, lean_object* v_hhi_1363_, lean_object* v_pivot_1364_, lean_object* v_as_1365_, lean_object* v_i_1366_, lean_object* v_k_1367_, lean_object* v_ilo_1368_, lean_object* v_ik_1369_, lean_object* v_w_1370_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_a_1359_, v_hi_1362_, v_pivot_1364_, v_as_1365_, v_i_1366_, v_k_1367_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___boxed(lean_object* v_a_1372_, lean_object* v_n_1373_, lean_object* v_lo_1374_, lean_object* v_hi_1375_, lean_object* v_hhi_1376_, lean_object* v_pivot_1377_, lean_object* v_as_1378_, lean_object* v_i_1379_, lean_object* v_k_1380_, lean_object* v_ilo_1381_, lean_object* v_ik_1382_, lean_object* v_w_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0(v_a_1372_, v_n_1373_, v_lo_1374_, v_hi_1375_, v_hhi_1376_, v_pivot_1377_, v_as_1378_, v_i_1379_, v_k_1380_, v_ilo_1381_, v_ik_1382_, v_w_1383_);
lean_dec(v_pivot_1377_);
lean_dec(v_hi_1375_);
lean_dec(v_lo_1374_);
lean_dec(v_n_1373_);
lean_dec_ref(v_a_1372_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(lean_object* v_perm_1385_, lean_object* v_range_1386_, lean_object* v_b_1387_, lean_object* v_i_1388_){
_start:
{
lean_object* v_stop_1389_; lean_object* v_step_1390_; uint8_t v___x_1391_; 
v_stop_1389_ = lean_ctor_get(v_range_1386_, 1);
v_step_1390_ = lean_ctor_get(v_range_1386_, 2);
v___x_1391_ = lean_nat_dec_lt(v_i_1388_, v_stop_1389_);
if (v___x_1391_ == 0)
{
lean_dec(v_i_1388_);
return v_b_1387_;
}
else
{
lean_object* v___x_1392_; lean_object* v_inv_1393_; lean_object* v___x_1394_; 
v___x_1392_ = lean_array_fget_borrowed(v_perm_1385_, v_i_1388_);
lean_inc(v_i_1388_);
v_inv_1393_ = lean_array_set(v_b_1387_, v___x_1392_, v_i_1388_);
v___x_1394_ = lean_nat_add(v_i_1388_, v_step_1390_);
lean_dec(v_i_1388_);
v_b_1387_ = v_inv_1393_;
v_i_1388_ = v___x_1394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg___boxed(lean_object* v_perm_1396_, lean_object* v_range_1397_, lean_object* v_b_1398_, lean_object* v_i_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1396_, v_range_1397_, v_b_1398_, v_i_1399_);
lean_dec_ref(v_range_1397_);
lean_dec_ref(v_perm_1396_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(lean_object* v_perm_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v_inv_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1402_ = lean_array_get_size(v_perm_1401_);
v___x_1403_ = lean_unsigned_to_nat(0u);
v_inv_1404_ = lean_mk_array(v___x_1402_, v___x_1403_);
v___x_1405_ = lean_unsigned_to_nat(1u);
v___x_1406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1403_);
lean_ctor_set(v___x_1406_, 1, v___x_1402_);
lean_ctor_set(v___x_1406_, 2, v___x_1405_);
v___x_1407_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1401_, v___x_1406_, v_inv_1404_, v___x_1403_);
lean_dec_ref(v___x_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv___boxed(lean_object* v_perm_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_perm_1408_);
lean_dec_ref(v_perm_1408_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(lean_object* v_perm_1410_, lean_object* v_range_1411_, lean_object* v_b_1412_, lean_object* v_i_1413_, lean_object* v_hs_1414_, lean_object* v_hl_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1410_, v_range_1411_, v_b_1412_, v_i_1413_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___boxed(lean_object* v_perm_1417_, lean_object* v_range_1418_, lean_object* v_b_1419_, lean_object* v_i_1420_, lean_object* v_hs_1421_, lean_object* v_hl_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(v_perm_1417_, v_range_1418_, v_b_1419_, v_i_1420_, v_hs_1421_, v_hl_1422_);
lean_dec_ref(v_range_1418_);
lean_dec_ref(v_perm_1417_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_reorder(lean_object* v_p_1424_, lean_object* v_old2new_1425_){
_start:
{
if (lean_obj_tag(v_p_1424_) == 0)
{
return v_p_1424_;
}
else
{
lean_object* v_k_1426_; lean_object* v_v_1427_; lean_object* v_p_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1438_; 
v_k_1426_ = lean_ctor_get(v_p_1424_, 0);
v_v_1427_ = lean_ctor_get(v_p_1424_, 1);
v_p_1428_ = lean_ctor_get(v_p_1424_, 2);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_p_1424_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1430_ = v_p_1424_;
v_isShared_1431_ = v_isSharedCheck_1438_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_p_1428_);
lean_inc(v_v_1427_);
lean_inc(v_k_1426_);
lean_dec(v_p_1424_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1438_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1432_ = lean_unsigned_to_nat(0u);
v___x_1433_ = lean_array_get_borrowed(v___x_1432_, v_old2new_1425_, v_v_1427_);
lean_dec(v_v_1427_);
v___x_1434_ = l_Int_Linear_Poly_reorder(v_p_1428_, v_old2new_1425_);
lean_inc(v___x_1433_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 2, v___x_1434_);
lean_ctor_set(v___x_1430_, 1, v___x_1433_);
v___x_1436_ = v___x_1430_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_k_1426_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_reorder___boxed(lean_object* v_p_1439_, lean_object* v_old2new_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Int_Linear_Poly_reorder(v_p_1439_, v_old2new_1440_);
lean_dec_ref(v_old2new_1440_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(lean_object* v_c_1442_, lean_object* v_old2new_1443_){
_start:
{
lean_object* v_d_1444_; lean_object* v_p_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_d_1444_ = lean_ctor_get(v_c_1442_, 0);
lean_inc(v_d_1444_);
v_p_1445_ = lean_ctor_get(v_c_1442_, 1);
lean_inc_ref(v_p_1445_);
v___x_1446_ = l_Int_Linear_Poly_reorder(v_p_1445_, v_old2new_1443_);
v___x_1447_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_c_1442_);
v___x_1448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1448_, 0, v_d_1444_);
lean_ctor_set(v___x_1448_, 1, v___x_1446_);
lean_ctor_set(v___x_1448_, 2, v___x_1447_);
v___x_1449_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v___x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder___boxed(lean_object* v_c_1450_, lean_object* v_old2new_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(v_c_1450_, v_old2new_1451_);
lean_dec_ref(v_old2new_1451_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(lean_object* v_c_1453_, lean_object* v_old2new_1454_){
_start:
{
lean_object* v_p_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_p_1455_ = lean_ctor_get(v_c_1453_, 0);
lean_inc_ref(v_p_1455_);
v___x_1456_ = l_Int_Linear_Poly_reorder(v_p_1455_, v_old2new_1454_);
v___x_1457_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1457_, 0, v_c_1453_);
v___x_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_norm(v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder___boxed(lean_object* v_c_1460_, lean_object* v_old2new_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_c_1460_, v_old2new_1461_);
lean_dec_ref(v_old2new_1461_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(lean_object* v_c_1463_, lean_object* v_old2new_1464_){
_start:
{
lean_object* v_p_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v_p_1465_ = lean_ctor_get(v_c_1463_, 0);
lean_inc_ref(v_p_1465_);
v___x_1466_ = l_Int_Linear_Poly_reorder(v_p_1465_, v_old2new_1464_);
v___x_1467_ = lean_alloc_ctor(16, 1, 0);
lean_ctor_set(v___x_1467_, 0, v_c_1463_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder___boxed(lean_object* v_c_1470_, lean_object* v_old2new_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_c_1470_, v_old2new_1471_);
lean_dec_ref(v_old2new_1471_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(lean_object* v_c_1473_, lean_object* v_old2new_1474_){
_start:
{
lean_object* v_p_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v_p_1475_ = lean_ctor_get(v_c_1473_, 0);
lean_inc_ref(v_p_1475_);
v___x_1476_ = l_Int_Linear_Poly_reorder(v_p_1475_, v_old2new_1474_);
v___x_1477_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_c_1473_);
v___x_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1476_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_norm(v___x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder___boxed(lean_object* v_c_1480_, lean_object* v_old2new_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(v_c_1480_, v_old2new_1481_);
lean_dec_ref(v_old2new_1481_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(lean_object* v_new2old_1483_, lean_object* v_inst_1484_, lean_object* v_m_1485_, lean_object* v_i_1486_, lean_object* v_h_1487_, lean_object* v_____s_1488_){
_start:
{
lean_object* v_j_1489_; lean_object* v___x_1490_; lean_object* v_r_1491_; lean_object* v___x_1492_; 
v_j_1489_ = lean_array_fget_borrowed(v_new2old_1483_, v_i_1486_);
v___x_1490_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_1484_, v_m_1485_, v_j_1489_);
v_r_1491_ = l_Lean_PersistentArray_push___redArg(v_____s_1488_, v___x_1490_);
v___x_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1492_, 0, v_r_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed(lean_object* v_new2old_1493_, lean_object* v_inst_1494_, lean_object* v_m_1495_, lean_object* v_i_1496_, lean_object* v_h_1497_, lean_object* v_____s_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(v_new2old_1493_, v_inst_1494_, v_m_1495_, v_i_1496_, v_h_1497_, v_____s_1498_);
lean_dec(v_i_1496_);
lean_dec_ref(v_m_1495_);
lean_dec(v_inst_1494_);
lean_dec_ref(v_new2old_1493_);
return v_res_1499_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = lean_unsigned_to_nat(32u);
v___x_1520_ = lean_mk_empty_array_with_capacity(v___x_1519_);
v___x_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11(void){
_start:
{
size_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v_r_1527_; 
v___x_1522_ = ((size_t)5ULL);
v___x_1523_ = lean_unsigned_to_nat(0u);
v___x_1524_ = lean_unsigned_to_nat(32u);
v___x_1525_ = lean_mk_empty_array_with_capacity(v___x_1524_);
v___x_1526_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10);
v_r_1527_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_r_1527_, 0, v___x_1526_);
lean_ctor_set(v_r_1527_, 1, v___x_1525_);
lean_ctor_set(v_r_1527_, 2, v___x_1523_);
lean_ctor_set(v_r_1527_, 3, v___x_1523_);
lean_ctor_set_usize(v_r_1527_, 4, v___x_1522_);
return v_r_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(lean_object* v_inst_1528_, lean_object* v_m_1529_, lean_object* v_new2old_1530_){
_start:
{
lean_object* v___f_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v_r_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_inc_ref(v_new2old_1530_);
v___f_1531_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1531_, 0, v_new2old_1530_);
lean_closure_set(v___f_1531_, 1, v_inst_1528_);
lean_closure_set(v___f_1531_, 2, v_m_1529_);
v___x_1532_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9));
v___x_1533_ = lean_unsigned_to_nat(0u);
v_r_1534_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11);
v___x_1535_ = lean_array_get_size(v_new2old_1530_);
lean_dec_ref(v_new2old_1530_);
v___x_1536_ = lean_unsigned_to_nat(1u);
v___x_1537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1533_);
lean_ctor_set(v___x_1537_, 1, v___x_1535_);
lean_ctor_set(v___x_1537_, 2, v___x_1536_);
v___x_1538_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_box(0), lean_box(0), v___x_1532_, v___x_1537_, v___f_1531_, v_r_1534_, v___x_1533_, lean_box(0), lean_box(0));
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap(lean_object* v_00_u03b1_1539_, lean_object* v_inst_1540_, lean_object* v_m_1541_, lean_object* v_new2old_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v_inst_1540_, v_m_1541_, v_new2old_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_, lean_object* v_x_1547_){
_start:
{
lean_object* v_ks_1548_; lean_object* v_vs_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1573_; 
v_ks_1548_ = lean_ctor_get(v_x_1544_, 0);
v_vs_1549_ = lean_ctor_get(v_x_1544_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_x_1544_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1551_ = v_x_1544_;
v_isShared_1552_ = v_isSharedCheck_1573_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_vs_1549_);
lean_inc(v_ks_1548_);
lean_dec(v_x_1544_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1573_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = lean_array_get_size(v_ks_1548_);
v___x_1554_ = lean_nat_dec_lt(v_x_1545_, v___x_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
lean_dec(v_x_1545_);
v___x_1555_ = lean_array_push(v_ks_1548_, v_x_1546_);
v___x_1556_ = lean_array_push(v_vs_1549_, v_x_1547_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 1, v___x_1556_);
lean_ctor_set(v___x_1551_, 0, v___x_1555_);
v___x_1558_ = v___x_1551_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
else
{
lean_object* v_k_x27_1560_; uint8_t v___x_1561_; 
v_k_x27_1560_ = lean_array_fget_borrowed(v_ks_1548_, v_x_1545_);
v___x_1561_ = l_Int_Linear_instBEqPoly_beq(v_x_1546_, v_k_x27_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1563_; 
if (v_isShared_1552_ == 0)
{
v___x_1563_ = v___x_1551_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_ks_1548_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_vs_1549_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_unsigned_to_nat(1u);
v___x_1565_ = lean_nat_add(v_x_1545_, v___x_1564_);
lean_dec(v_x_1545_);
v_x_1544_ = v___x_1563_;
v_x_1545_ = v___x_1565_;
goto _start;
}
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1568_ = lean_array_fset(v_ks_1548_, v_x_1545_, v_x_1546_);
v___x_1569_ = lean_array_fset(v_vs_1549_, v_x_1545_, v_x_1547_);
lean_dec(v_x_1545_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 1, v___x_1569_);
lean_ctor_set(v___x_1551_, 0, v___x_1568_);
v___x_1571_ = v___x_1551_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1574_, lean_object* v_k_1575_, lean_object* v_v_1576_){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_unsigned_to_nat(0u);
v___x_1578_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1574_, v___x_1577_, v_k_1575_, v_v_1576_);
return v___x_1578_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1579_; size_t v___x_1580_; size_t v___x_1581_; 
v___x_1579_ = ((size_t)5ULL);
v___x_1580_ = ((size_t)1ULL);
v___x_1581_ = lean_usize_shift_left(v___x_1580_, v___x_1579_);
return v___x_1581_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1582_; size_t v___x_1583_; size_t v___x_1584_; 
v___x_1582_ = ((size_t)1ULL);
v___x_1583_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0);
v___x_1584_ = lean_usize_sub(v___x_1583_, v___x_1582_);
return v___x_1584_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(lean_object* v_x_1586_, size_t v_x_1587_, size_t v_x_1588_, lean_object* v_x_1589_, lean_object* v_x_1590_){
_start:
{
if (lean_obj_tag(v_x_1586_) == 0)
{
lean_object* v_es_1591_; size_t v___x_1592_; size_t v___x_1593_; size_t v___x_1594_; size_t v___x_1595_; lean_object* v_j_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v_es_1591_ = lean_ctor_get(v_x_1586_, 0);
v___x_1592_ = ((size_t)5ULL);
v___x_1593_ = ((size_t)1ULL);
v___x_1594_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1);
v___x_1595_ = lean_usize_land(v_x_1587_, v___x_1594_);
v_j_1596_ = lean_usize_to_nat(v___x_1595_);
v___x_1597_ = lean_array_get_size(v_es_1591_);
v___x_1598_ = lean_nat_dec_lt(v_j_1596_, v___x_1597_);
if (v___x_1598_ == 0)
{
lean_dec(v_j_1596_);
lean_dec(v_x_1590_);
lean_dec_ref(v_x_1589_);
return v_x_1586_;
}
else
{
lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1635_; 
lean_inc_ref(v_es_1591_);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_x_1586_);
if (v_isSharedCheck_1635_ == 0)
{
lean_object* v_unused_1636_; 
v_unused_1636_ = lean_ctor_get(v_x_1586_, 0);
lean_dec(v_unused_1636_);
v___x_1600_ = v_x_1586_;
v_isShared_1601_ = v_isSharedCheck_1635_;
goto v_resetjp_1599_;
}
else
{
lean_dec(v_x_1586_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1635_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v_v_1602_; lean_object* v___x_1603_; lean_object* v_xs_x27_1604_; lean_object* v___y_1606_; 
v_v_1602_ = lean_array_fget(v_es_1591_, v_j_1596_);
v___x_1603_ = lean_box(0);
v_xs_x27_1604_ = lean_array_fset(v_es_1591_, v_j_1596_, v___x_1603_);
switch(lean_obj_tag(v_v_1602_))
{
case 0:
{
lean_object* v_key_1611_; lean_object* v_val_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1622_; 
v_key_1611_ = lean_ctor_get(v_v_1602_, 0);
v_val_1612_ = lean_ctor_get(v_v_1602_, 1);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_v_1602_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1614_ = v_v_1602_;
v_isShared_1615_ = v_isSharedCheck_1622_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_val_1612_);
lean_inc(v_key_1611_);
lean_dec(v_v_1602_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1622_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
uint8_t v___x_1616_; 
v___x_1616_ = l_Int_Linear_instBEqPoly_beq(v_x_1589_, v_key_1611_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
lean_del_object(v___x_1614_);
v___x_1617_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1611_, v_val_1612_, v_x_1589_, v_x_1590_);
v___x_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
v___y_1606_ = v___x_1618_;
goto v___jp_1605_;
}
else
{
lean_object* v___x_1620_; 
lean_dec(v_val_1612_);
lean_dec(v_key_1611_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 1, v_x_1590_);
lean_ctor_set(v___x_1614_, 0, v_x_1589_);
v___x_1620_ = v___x_1614_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_x_1589_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_x_1590_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
v___y_1606_ = v___x_1620_;
goto v___jp_1605_;
}
}
}
}
case 1:
{
lean_object* v_node_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1633_; 
v_node_1623_ = lean_ctor_get(v_v_1602_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_v_1602_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1625_ = v_v_1602_;
v_isShared_1626_ = v_isSharedCheck_1633_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_node_1623_);
lean_dec(v_v_1602_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1633_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
size_t v___x_1627_; size_t v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1627_ = lean_usize_shift_right(v_x_1587_, v___x_1592_);
v___x_1628_ = lean_usize_add(v_x_1588_, v___x_1593_);
v___x_1629_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_node_1623_, v___x_1627_, v___x_1628_, v_x_1589_, v_x_1590_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1629_);
v___x_1631_ = v___x_1625_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
v___y_1606_ = v___x_1631_;
goto v___jp_1605_;
}
}
}
default: 
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v_x_1589_);
lean_ctor_set(v___x_1634_, 1, v_x_1590_);
v___y_1606_ = v___x_1634_;
goto v___jp_1605_;
}
}
v___jp_1605_:
{
lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1607_ = lean_array_fset(v_xs_x27_1604_, v_j_1596_, v___y_1606_);
lean_dec(v_j_1596_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1607_);
v___x_1609_ = v___x_1600_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
else
{
lean_object* v_ks_1637_; lean_object* v_vs_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1658_; 
v_ks_1637_ = lean_ctor_get(v_x_1586_, 0);
v_vs_1638_ = lean_ctor_get(v_x_1586_, 1);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_x_1586_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1640_ = v_x_1586_;
v_isShared_1641_ = v_isSharedCheck_1658_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_vs_1638_);
lean_inc(v_ks_1637_);
lean_dec(v_x_1586_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1658_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_ks_1637_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_vs_1638_);
v___x_1643_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v_newNode_1644_; uint8_t v___y_1646_; size_t v___x_1652_; uint8_t v___x_1653_; 
v_newNode_1644_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(v___x_1643_, v_x_1589_, v_x_1590_);
v___x_1652_ = ((size_t)7ULL);
v___x_1653_ = lean_usize_dec_le(v___x_1652_, v_x_1588_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1654_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1644_);
v___x_1655_ = lean_unsigned_to_nat(4u);
v___x_1656_ = lean_nat_dec_lt(v___x_1654_, v___x_1655_);
lean_dec(v___x_1654_);
v___y_1646_ = v___x_1656_;
goto v___jp_1645_;
}
else
{
v___y_1646_ = v___x_1653_;
goto v___jp_1645_;
}
v___jp_1645_:
{
if (v___y_1646_ == 0)
{
lean_object* v_ks_1647_; lean_object* v_vs_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v_ks_1647_ = lean_ctor_get(v_newNode_1644_, 0);
lean_inc_ref(v_ks_1647_);
v_vs_1648_ = lean_ctor_get(v_newNode_1644_, 1);
lean_inc_ref(v_vs_1648_);
lean_dec_ref(v_newNode_1644_);
v___x_1649_ = lean_unsigned_to_nat(0u);
v___x_1650_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2);
v___x_1651_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_x_1588_, v_ks_1647_, v_vs_1648_, v___x_1649_, v___x_1650_);
lean_dec_ref(v_vs_1648_);
lean_dec_ref(v_ks_1647_);
return v___x_1651_;
}
else
{
return v_newNode_1644_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(size_t v_depth_1659_, lean_object* v_keys_1660_, lean_object* v_vals_1661_, lean_object* v_i_1662_, lean_object* v_entries_1663_){
_start:
{
lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1664_ = lean_array_get_size(v_keys_1660_);
v___x_1665_ = lean_nat_dec_lt(v_i_1662_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_dec(v_i_1662_);
return v_entries_1663_;
}
else
{
lean_object* v_k_1666_; lean_object* v_v_1667_; uint64_t v___x_1668_; size_t v_h_1669_; size_t v___x_1670_; lean_object* v___x_1671_; size_t v___x_1672_; size_t v___x_1673_; size_t v___x_1674_; size_t v_h_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_k_1666_ = lean_array_fget_borrowed(v_keys_1660_, v_i_1662_);
v_v_1667_ = lean_array_fget_borrowed(v_vals_1661_, v_i_1662_);
v___x_1668_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_k_1666_);
v_h_1669_ = lean_uint64_to_usize(v___x_1668_);
v___x_1670_ = ((size_t)5ULL);
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = ((size_t)1ULL);
v___x_1673_ = lean_usize_sub(v_depth_1659_, v___x_1672_);
v___x_1674_ = lean_usize_mul(v___x_1670_, v___x_1673_);
v_h_1675_ = lean_usize_shift_right(v_h_1669_, v___x_1674_);
v___x_1676_ = lean_nat_add(v_i_1662_, v___x_1671_);
lean_dec(v_i_1662_);
lean_inc(v_v_1667_);
lean_inc(v_k_1666_);
v___x_1677_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_entries_1663_, v_h_1675_, v_depth_1659_, v_k_1666_, v_v_1667_);
v_i_1662_ = v___x_1676_;
v_entries_1663_ = v___x_1677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1679_, lean_object* v_keys_1680_, lean_object* v_vals_1681_, lean_object* v_i_1682_, lean_object* v_entries_1683_){
_start:
{
size_t v_depth_boxed_1684_; lean_object* v_res_1685_; 
v_depth_boxed_1684_ = lean_unbox_usize(v_depth_1679_);
lean_dec(v_depth_1679_);
v_res_1685_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1684_, v_keys_1680_, v_vals_1681_, v_i_1682_, v_entries_1683_);
lean_dec_ref(v_vals_1681_);
lean_dec_ref(v_keys_1680_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___boxed(lean_object* v_x_1686_, lean_object* v_x_1687_, lean_object* v_x_1688_, lean_object* v_x_1689_, lean_object* v_x_1690_){
_start:
{
size_t v_x_1894__boxed_1691_; size_t v_x_1895__boxed_1692_; lean_object* v_res_1693_; 
v_x_1894__boxed_1691_ = lean_unbox_usize(v_x_1687_);
lean_dec(v_x_1687_);
v_x_1895__boxed_1692_ = lean_unbox_usize(v_x_1688_);
lean_dec(v_x_1688_);
v_res_1693_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1686_, v_x_1894__boxed_1691_, v_x_1895__boxed_1692_, v_x_1689_, v_x_1690_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(lean_object* v_x_1694_, lean_object* v_x_1695_, lean_object* v_x_1696_){
_start:
{
uint64_t v___x_1697_; size_t v___x_1698_; size_t v___x_1699_; lean_object* v___x_1700_; 
v___x_1697_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_x_1695_);
v___x_1698_ = lean_uint64_to_usize(v___x_1697_);
v___x_1699_ = ((size_t)1ULL);
v___x_1700_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1694_, v___x_1698_, v___x_1699_, v_x_1695_, v_x_1696_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(lean_object* v_old2new_1701_, lean_object* v_x_1702_, lean_object* v_____s_1703_){
_start:
{
lean_object* v_fst_1704_; lean_object* v_snd_1705_; lean_object* v___x_1706_; lean_object* v_m_x27_1707_; lean_object* v___x_1708_; 
v_fst_1704_ = lean_ctor_get(v_x_1702_, 0);
lean_inc(v_fst_1704_);
v_snd_1705_ = lean_ctor_get(v_x_1702_, 1);
lean_inc(v_snd_1705_);
lean_dec_ref(v_x_1702_);
v___x_1706_ = l_Int_Linear_Poly_reorder(v_fst_1704_, v_old2new_1701_);
v_m_x27_1707_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(v_____s_1703_, v___x_1706_, v_snd_1705_);
v___x_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1708_, 0, v_m_x27_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed(lean_object* v_old2new_1709_, lean_object* v_x_1710_, lean_object* v_____s_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(v_old2new_1709_, v_x_1710_, v_____s_1711_);
lean_dec_ref(v_old2new_1709_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_f_1713_, lean_object* v_keys_1714_, lean_object* v_vals_1715_, lean_object* v_i_1716_, lean_object* v_acc_1717_){
_start:
{
lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1718_ = lean_array_get_size(v_keys_1714_);
v___x_1719_ = lean_nat_dec_lt(v_i_1716_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
lean_dec(v_i_1716_);
lean_dec_ref(v_f_1713_);
v___x_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_acc_1717_);
return v___x_1720_;
}
else
{
lean_object* v_k_1721_; lean_object* v_v_1722_; lean_object* v___x_1723_; 
v_k_1721_ = lean_array_fget_borrowed(v_keys_1714_, v_i_1716_);
v_v_1722_ = lean_array_fget_borrowed(v_vals_1715_, v_i_1716_);
lean_inc_ref(v_f_1713_);
lean_inc(v_v_1722_);
lean_inc(v_k_1721_);
v___x_1723_ = lean_apply_3(v_f_1713_, v_acc_1717_, v_k_1721_, v_v_1722_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_dec(v_i_1716_);
lean_dec_ref(v_f_1713_);
return v___x_1723_;
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref(v___x_1723_);
v___x_1725_ = lean_unsigned_to_nat(1u);
v___x_1726_ = lean_nat_add(v_i_1716_, v___x_1725_);
lean_dec(v_i_1716_);
v_i_1716_ = v___x_1726_;
v_acc_1717_ = v_a_1724_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_f_1728_, lean_object* v_keys_1729_, lean_object* v_vals_1730_, lean_object* v_i_1731_, lean_object* v_acc_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1728_, v_keys_1729_, v_vals_1730_, v_i_1731_, v_acc_1732_);
lean_dec_ref(v_vals_1730_);
lean_dec_ref(v_keys_1729_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(lean_object* v_f_1734_, lean_object* v_x_1735_, lean_object* v_x_1736_){
_start:
{
if (lean_obj_tag(v_x_1735_) == 0)
{
lean_object* v_es_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1757_; 
v_es_1737_ = lean_ctor_get(v_x_1735_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_x_1735_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1739_ = v_x_1735_;
v_isShared_1740_ = v_isSharedCheck_1757_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_es_1737_);
lean_dec(v_x_1735_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1757_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v___x_1741_ = lean_unsigned_to_nat(0u);
v___x_1742_ = lean_array_get_size(v_es_1737_);
v___x_1743_ = lean_nat_dec_lt(v___x_1741_, v___x_1742_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1745_; 
lean_dec_ref(v_es_1737_);
lean_dec_ref(v_f_1734_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set_tag(v___x_1739_, 1);
lean_ctor_set(v___x_1739_, 0, v_x_1736_);
v___x_1745_ = v___x_1739_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_x_1736_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
else
{
uint8_t v___x_1747_; 
v___x_1747_ = lean_nat_dec_le(v___x_1742_, v___x_1742_);
if (v___x_1747_ == 0)
{
if (v___x_1743_ == 0)
{
lean_object* v___x_1749_; 
lean_dec_ref(v_es_1737_);
lean_dec_ref(v_f_1734_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set_tag(v___x_1739_, 1);
lean_ctor_set(v___x_1739_, 0, v_x_1736_);
v___x_1749_ = v___x_1739_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_x_1736_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
else
{
size_t v___x_1751_; size_t v___x_1752_; lean_object* v___x_1753_; 
lean_del_object(v___x_1739_);
v___x_1751_ = ((size_t)0ULL);
v___x_1752_ = lean_usize_of_nat(v___x_1742_);
v___x_1753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1734_, v_es_1737_, v___x_1751_, v___x_1752_, v_x_1736_);
lean_dec_ref(v_es_1737_);
return v___x_1753_;
}
}
else
{
size_t v___x_1754_; size_t v___x_1755_; lean_object* v___x_1756_; 
lean_del_object(v___x_1739_);
v___x_1754_ = ((size_t)0ULL);
v___x_1755_ = lean_usize_of_nat(v___x_1742_);
v___x_1756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1734_, v_es_1737_, v___x_1754_, v___x_1755_, v_x_1736_);
lean_dec_ref(v_es_1737_);
return v___x_1756_;
}
}
}
}
else
{
lean_object* v_ks_1758_; lean_object* v_vs_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_ks_1758_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_ks_1758_);
v_vs_1759_ = lean_ctor_get(v_x_1735_, 1);
lean_inc_ref(v_vs_1759_);
lean_dec_ref(v_x_1735_);
v___x_1760_ = lean_unsigned_to_nat(0u);
v___x_1761_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1734_, v_ks_1758_, v_vs_1759_, v___x_1760_, v_x_1736_);
lean_dec_ref(v_vs_1759_);
lean_dec_ref(v_ks_1758_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_f_1762_, lean_object* v_as_1763_, size_t v_i_1764_, size_t v_stop_1765_, lean_object* v_b_1766_){
_start:
{
lean_object* v_a_1768_; lean_object* v___y_1773_; uint8_t v___x_1775_; 
v___x_1775_ = lean_usize_dec_eq(v_i_1764_, v_stop_1765_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_array_uget_borrowed(v_as_1763_, v_i_1764_);
switch(lean_obj_tag(v___x_1776_))
{
case 0:
{
lean_object* v_key_1777_; lean_object* v_val_1778_; lean_object* v___x_1779_; 
v_key_1777_ = lean_ctor_get(v___x_1776_, 0);
v_val_1778_ = lean_ctor_get(v___x_1776_, 1);
lean_inc_ref(v_f_1762_);
lean_inc(v_val_1778_);
lean_inc(v_key_1777_);
v___x_1779_ = lean_apply_3(v_f_1762_, v_b_1766_, v_key_1777_, v_val_1778_);
v___y_1773_ = v___x_1779_;
goto v___jp_1772_;
}
case 1:
{
lean_object* v_node_1780_; lean_object* v___x_1781_; 
v_node_1780_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_node_1780_);
lean_inc_ref(v_f_1762_);
v___x_1781_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1762_, v_node_1780_, v_b_1766_);
v___y_1773_ = v___x_1781_;
goto v___jp_1772_;
}
default: 
{
v_a_1768_ = v_b_1766_;
goto v___jp_1767_;
}
}
}
else
{
lean_object* v___x_1782_; 
lean_dec_ref(v_f_1762_);
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_b_1766_);
return v___x_1782_;
}
v___jp_1767_:
{
size_t v___x_1769_; size_t v___x_1770_; 
v___x_1769_ = ((size_t)1ULL);
v___x_1770_ = lean_usize_add(v_i_1764_, v___x_1769_);
v_i_1764_ = v___x_1770_;
v_b_1766_ = v_a_1768_;
goto _start;
}
v___jp_1772_:
{
if (lean_obj_tag(v___y_1773_) == 0)
{
lean_dec_ref(v_f_1762_);
return v___y_1773_;
}
else
{
lean_object* v_a_1774_; 
v_a_1774_ = lean_ctor_get(v___y_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref(v___y_1773_);
v_a_1768_ = v_a_1774_;
goto v___jp_1767_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_f_1783_, lean_object* v_as_1784_, lean_object* v_i_1785_, lean_object* v_stop_1786_, lean_object* v_b_1787_){
_start:
{
size_t v_i_boxed_1788_; size_t v_stop_boxed_1789_; lean_object* v_res_1790_; 
v_i_boxed_1788_ = lean_unbox_usize(v_i_1785_);
lean_dec(v_i_1785_);
v_stop_boxed_1789_ = lean_unbox_usize(v_stop_1786_);
lean_dec(v_stop_1786_);
v_res_1790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1783_, v_as_1784_, v_i_boxed_1788_, v_stop_boxed_1789_, v_b_1787_);
lean_dec_ref(v_as_1784_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0(lean_object* v_f_1791_, lean_object* v_s_1792_, lean_object* v_a_1793_, lean_object* v_b_1794_){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_a_1793_);
lean_ctor_set(v___x_1795_, 1, v_b_1794_);
v___x_1796_ = lean_apply_2(v_f_1791_, v___x_1795_, v_s_1792_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
v_a_1805_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1796_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1796_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(lean_object* v_map_1813_, lean_object* v_init_1814_, lean_object* v_f_1815_){
_start:
{
lean_object* v___f_1816_; lean_object* v___x_1817_; lean_object* v_a_1818_; 
v___f_1816_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1816_, 0, v_f_1815_);
lean_inc_ref(v_map_1813_);
v___x_1817_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v___f_1816_, v_map_1813_, v_init_1814_);
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
lean_dec_ref(v___x_1817_);
return v_a_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___boxed(lean_object* v_map_1819_, lean_object* v_init_1820_, lean_object* v_f_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_map_1819_, v_init_1820_, v_f_1821_);
lean_dec_ref(v_map_1819_);
return v_res_1822_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0(void){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1823_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1(void){
_start:
{
lean_object* v___x_1824_; lean_object* v_m_x27_1825_; 
v___x_1824_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0);
v_m_x27_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_m_x27_1825_, 0, v___x_1824_);
return v_m_x27_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(lean_object* v_m_1826_, lean_object* v_old2new_1827_){
_start:
{
lean_object* v___f_1828_; lean_object* v_m_x27_1829_; lean_object* v___x_1830_; 
v___f_1828_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1828_, 0, v_old2new_1827_);
v_m_x27_1829_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1);
v___x_1830_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_m_1826_, v_m_x27_1829_, v___f_1828_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___boxed(lean_object* v_m_1831_, lean_object* v_old2new_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(v_m_1831_, v_old2new_1832_);
lean_dec_ref(v_m_1831_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0(lean_object* v_00_u03b2_1834_, lean_object* v_x_1835_, lean_object* v_x_1836_, lean_object* v_x_1837_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(v_x_1835_, v_x_1836_, v_x_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(lean_object* v_00_u03c3_1839_, lean_object* v_00_u03b2_1840_, lean_object* v_map_1841_, lean_object* v_init_1842_, lean_object* v_f_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_map_1841_, v_init_1842_, v_f_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___boxed(lean_object* v_00_u03c3_1845_, lean_object* v_00_u03b2_1846_, lean_object* v_map_1847_, lean_object* v_init_1848_, lean_object* v_f_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(v_00_u03c3_1845_, v_00_u03b2_1846_, v_map_1847_, v_init_1848_, v_f_1849_);
lean_dec_ref(v_map_1847_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(lean_object* v_00_u03b2_1851_, lean_object* v_x_1852_, size_t v_x_1853_, size_t v_x_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1852_, v_x_1853_, v_x_1854_, v_x_1855_, v_x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1858_, lean_object* v_x_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_, lean_object* v_x_1863_){
_start:
{
size_t v_x_2251__boxed_1864_; size_t v_x_2252__boxed_1865_; lean_object* v_res_1866_; 
v_x_2251__boxed_1864_ = lean_unbox_usize(v_x_1860_);
lean_dec(v_x_1860_);
v_x_2252__boxed_1865_ = lean_unbox_usize(v_x_1861_);
lean_dec(v_x_1861_);
v_res_1866_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(v_00_u03b2_1858_, v_x_1859_, v_x_2251__boxed_1864_, v_x_2252__boxed_1865_, v_x_1862_, v_x_1863_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2___redArg(lean_object* v_map_1867_, lean_object* v_f_1868_, lean_object* v_init_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1868_, v_map_1867_, v_init_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2(lean_object* v_00_u03c3_1871_, lean_object* v_00_u03c3_1872_, lean_object* v_00_u03b2_1873_, lean_object* v_map_1874_, lean_object* v_f_1875_, lean_object* v_init_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1875_, v_map_1874_, v_init_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1878_, lean_object* v_n_1879_, lean_object* v_k_1880_, lean_object* v_v_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(v_n_1879_, v_k_1880_, v_v_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1883_, size_t v_depth_1884_, lean_object* v_keys_1885_, lean_object* v_vals_1886_, lean_object* v_heq_1887_, lean_object* v_i_1888_, lean_object* v_entries_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_1884_, v_keys_1885_, v_vals_1886_, v_i_1888_, v_entries_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1891_, lean_object* v_depth_1892_, lean_object* v_keys_1893_, lean_object* v_vals_1894_, lean_object* v_heq_1895_, lean_object* v_i_1896_, lean_object* v_entries_1897_){
_start:
{
size_t v_depth_boxed_1898_; lean_object* v_res_1899_; 
v_depth_boxed_1898_ = lean_unbox_usize(v_depth_1892_);
lean_dec(v_depth_1892_);
v_res_1899_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(v_00_u03b2_1891_, v_depth_boxed_1898_, v_keys_1893_, v_vals_1894_, v_heq_1895_, v_i_1896_, v_entries_1897_);
lean_dec_ref(v_vals_1894_);
lean_dec_ref(v_keys_1893_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5(lean_object* v_00_u03c3_1900_, lean_object* v_00_u03c3_1901_, lean_object* v_00_u03b1_1902_, lean_object* v_00_u03b2_1903_, lean_object* v_f_1904_, lean_object* v_x_1905_, lean_object* v_x_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1904_, v_x_1905_, v_x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1908_, lean_object* v_x_1909_, lean_object* v_x_1910_, lean_object* v_x_1911_, lean_object* v_x_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1909_, v_x_1910_, v_x_1911_, v_x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_1914_, lean_object* v_00_u03b2_1915_, lean_object* v_00_u03c3_1916_, lean_object* v_00_u03c3_1917_, lean_object* v_f_1918_, lean_object* v_as_1919_, size_t v_i_1920_, size_t v_stop_1921_, lean_object* v_b_1922_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1918_, v_as_1919_, v_i_1920_, v_stop_1921_, v_b_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1924_, lean_object* v_00_u03b2_1925_, lean_object* v_00_u03c3_1926_, lean_object* v_00_u03c3_1927_, lean_object* v_f_1928_, lean_object* v_as_1929_, lean_object* v_i_1930_, lean_object* v_stop_1931_, lean_object* v_b_1932_){
_start:
{
size_t v_i_boxed_1933_; size_t v_stop_boxed_1934_; lean_object* v_res_1935_; 
v_i_boxed_1933_ = lean_unbox_usize(v_i_1930_);
lean_dec(v_i_1930_);
v_stop_boxed_1934_ = lean_unbox_usize(v_stop_1931_);
lean_dec(v_stop_1931_);
v_res_1935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_1924_, v_00_u03b2_1925_, v_00_u03c3_1926_, v_00_u03c3_1927_, v_f_1928_, v_as_1929_, v_i_boxed_1933_, v_stop_boxed_1934_, v_b_1932_);
lean_dec_ref(v_as_1929_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03c3_1936_, lean_object* v_00_u03c3_1937_, lean_object* v_00_u03b1_1938_, lean_object* v_00_u03b2_1939_, lean_object* v_f_1940_, lean_object* v_keys_1941_, lean_object* v_vals_1942_, lean_object* v_heq_1943_, lean_object* v_i_1944_, lean_object* v_acc_1945_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1940_, v_keys_1941_, v_vals_1942_, v_i_1944_, v_acc_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03c3_1947_, lean_object* v_00_u03c3_1948_, lean_object* v_00_u03b1_1949_, lean_object* v_00_u03b2_1950_, lean_object* v_f_1951_, lean_object* v_keys_1952_, lean_object* v_vals_1953_, lean_object* v_heq_1954_, lean_object* v_i_1955_, lean_object* v_acc_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(v_00_u03c3_1947_, v_00_u03c3_1948_, v_00_u03b1_1949_, v_00_u03b2_1950_, v_f_1951_, v_keys_1952_, v_vals_1953_, v_heq_1954_, v_i_1955_, v_acc_1956_);
lean_dec_ref(v_vals_1953_);
lean_dec_ref(v_keys_1952_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(lean_object* v___x_1958_, lean_object* v_x_1959_){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = lean_unsigned_to_nat(0u);
v___x_1961_ = lean_array_get_borrowed(v___x_1960_, v___x_1958_, v_x_1959_);
lean_inc(v___x_1961_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed(lean_object* v___x_1962_, lean_object* v_x_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(v___x_1962_, v_x_1963_);
lean_dec(v_x_1963_);
lean_dec_ref(v___x_1962_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg___lam__0(lean_object* v_f_1965_, lean_object* v_x_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_apply_1(v_f_1965_, v_x_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(lean_object* v_f_1968_, lean_object* v_as_1969_, lean_object* v_i_1970_, lean_object* v_acc_1971_){
_start:
{
lean_object* v___x_1972_; uint8_t v___x_1973_; 
v___x_1972_ = lean_array_get_size(v_as_1969_);
v___x_1973_ = lean_nat_dec_eq(v_i_1970_, v___x_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1974_ = lean_array_fget_borrowed(v_as_1969_, v_i_1970_);
lean_inc(v_f_1968_);
lean_inc(v___x_1974_);
v___x_1975_ = lean_apply_1(v_f_1968_, v___x_1974_);
v___x_1976_ = lean_unsigned_to_nat(1u);
v___x_1977_ = lean_nat_add(v_i_1970_, v___x_1976_);
lean_dec(v_i_1970_);
v___x_1978_ = lean_array_push(v_acc_1971_, v___x_1975_);
v_i_1970_ = v___x_1977_;
v_acc_1971_ = v___x_1978_;
goto _start;
}
else
{
lean_dec(v_i_1970_);
lean_dec(v_f_1968_);
return v_acc_1971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg___boxed(lean_object* v_f_1980_, lean_object* v_as_1981_, lean_object* v_i_1982_, lean_object* v_acc_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(v_f_1980_, v_as_1981_, v_i_1982_, v_acc_1983_);
lean_dec_ref(v_as_1981_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(lean_object* v_f_1985_, lean_object* v_as_1986_){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1987_ = lean_unsigned_to_nat(0u);
v___x_1988_ = lean_array_get_size(v_as_1986_);
v___x_1989_ = lean_mk_empty_array_with_capacity(v___x_1988_);
v___x_1990_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(v_f_1985_, v_as_1986_, v___x_1987_, v___x_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg___boxed(lean_object* v_f_1991_, lean_object* v_as_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(v_f_1991_, v_as_1992_);
lean_dec_ref(v_as_1992_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(lean_object* v_f_1994_, size_t v_sz_1995_, size_t v_i_1996_, lean_object* v_bs_1997_){
_start:
{
uint8_t v___x_1998_; 
v___x_1998_ = lean_usize_dec_lt(v_i_1996_, v_sz_1995_);
if (v___x_1998_ == 0)
{
lean_dec(v_f_1994_);
return v_bs_1997_;
}
else
{
lean_object* v_v_1999_; lean_object* v___x_2000_; lean_object* v_bs_x27_2001_; lean_object* v___y_2003_; 
v_v_1999_ = lean_array_uget(v_bs_1997_, v_i_1996_);
v___x_2000_ = lean_unsigned_to_nat(0u);
v_bs_x27_2001_ = lean_array_uset(v_bs_1997_, v_i_1996_, v___x_2000_);
switch(lean_obj_tag(v_v_1999_))
{
case 0:
{
lean_object* v_key_2008_; lean_object* v_val_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2017_; 
v_key_2008_ = lean_ctor_get(v_v_1999_, 0);
v_val_2009_ = lean_ctor_get(v_v_1999_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_v_1999_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2011_ = v_v_1999_;
v_isShared_2012_ = v_isSharedCheck_2017_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_val_2009_);
lean_inc(v_key_2008_);
lean_dec(v_v_1999_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2017_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; lean_object* v___x_2015_; 
lean_inc(v_f_1994_);
v___x_2013_ = lean_apply_1(v_f_1994_, v_val_2009_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 1, v___x_2013_);
v___x_2015_ = v___x_2011_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_key_2008_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
v___y_2003_ = v___x_2015_;
goto v___jp_2002_;
}
}
}
case 1:
{
lean_object* v_node_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2026_; 
v_node_2018_ = lean_ctor_get(v_v_1999_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_v_1999_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2020_ = v_v_1999_;
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_node_2018_);
lean_dec(v_v_1999_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
lean_inc(v_f_1994_);
v___x_2022_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v_f_1994_, v_node_2018_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2022_);
v___x_2024_ = v___x_2020_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
v___y_2003_ = v___x_2024_;
goto v___jp_2002_;
}
}
}
default: 
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_box(2);
v___y_2003_ = v___x_2027_;
goto v___jp_2002_;
}
}
v___jp_2002_:
{
size_t v___x_2004_; size_t v___x_2005_; lean_object* v___x_2006_; 
v___x_2004_ = ((size_t)1ULL);
v___x_2005_ = lean_usize_add(v_i_1996_, v___x_2004_);
v___x_2006_ = lean_array_uset(v_bs_x27_2001_, v_i_1996_, v___y_2003_);
v_i_1996_ = v___x_2005_;
v_bs_1997_ = v___x_2006_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2028_, lean_object* v_n_2029_){
_start:
{
if (lean_obj_tag(v_n_2029_) == 0)
{
lean_object* v_es_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2040_; 
v_es_2030_ = lean_ctor_get(v_n_2029_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_n_2029_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2032_ = v_n_2029_;
v_isShared_2033_ = v_isSharedCheck_2040_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_es_2030_);
lean_dec(v_n_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2040_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
size_t v_sz_2034_; size_t v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v_sz_2034_ = lean_array_size(v_es_2030_);
v___x_2035_ = ((size_t)0ULL);
v___x_2036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(v_f_2028_, v_sz_2034_, v___x_2035_, v_es_2030_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2036_);
v___x_2038_ = v___x_2032_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
else
{
lean_object* v_ks_2041_; lean_object* v_vs_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2050_; 
v_ks_2041_ = lean_ctor_get(v_n_2029_, 0);
v_vs_2042_ = lean_ctor_get(v_n_2029_, 1);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_n_2029_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2044_ = v_n_2029_;
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_vs_2042_);
lean_inc(v_ks_2041_);
lean_dec(v_n_2029_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v_val_2046_; lean_object* v___x_2048_; 
v_val_2046_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(v_f_2028_, v_vs_2042_);
lean_dec_ref(v_vs_2042_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 1, v_val_2046_);
v___x_2048_ = v___x_2044_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_ks_2041_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_val_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg___boxed(lean_object* v_f_2051_, lean_object* v_sz_2052_, lean_object* v_i_2053_, lean_object* v_bs_2054_){
_start:
{
size_t v_sz_boxed_2055_; size_t v_i_boxed_2056_; lean_object* v_res_2057_; 
v_sz_boxed_2055_ = lean_unbox_usize(v_sz_2052_);
lean_dec(v_sz_2052_);
v_i_boxed_2056_ = lean_unbox_usize(v_i_2053_);
lean_dec(v_i_2053_);
v_res_2057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(v_f_2051_, v_sz_boxed_2055_, v_i_boxed_2056_, v_bs_2054_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(lean_object* v_pm_2058_, lean_object* v_f_2059_){
_start:
{
lean_object* v___f_2060_; lean_object* v___x_2061_; 
v___f_2060_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2060_, 0, v_f_2059_);
v___x_2061_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v___f_2060_, v_pm_2058_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(lean_object* v___x_2062_, size_t v_sz_2063_, size_t v_i_2064_, lean_object* v_bs_2065_){
_start:
{
uint8_t v___x_2066_; 
v___x_2066_ = lean_usize_dec_lt(v_i_2064_, v_sz_2063_);
if (v___x_2066_ == 0)
{
return v_bs_2065_;
}
else
{
lean_object* v_v_2067_; lean_object* v___x_2068_; lean_object* v_bs_x27_2069_; lean_object* v___y_2071_; 
v_v_2067_ = lean_array_uget(v_bs_2065_, v_i_2064_);
v___x_2068_ = lean_unsigned_to_nat(0u);
v_bs_x27_2069_ = lean_array_uset(v_bs_2065_, v_i_2064_, v___x_2068_);
if (lean_obj_tag(v_v_2067_) == 0)
{
v___y_2071_ = v_v_2067_;
goto v___jp_2070_;
}
else
{
lean_object* v_val_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2084_; 
v_val_2076_ = lean_ctor_get(v_v_2067_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v_v_2067_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2078_ = v_v_2067_;
v_isShared_2079_ = v_isSharedCheck_2084_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_val_2076_);
lean_dec(v_v_2067_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2084_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_val_2076_, v___x_2062_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2080_);
v___x_2082_ = v___x_2078_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
v___y_2071_ = v___x_2082_;
goto v___jp_2070_;
}
}
}
v___jp_2070_:
{
size_t v___x_2072_; size_t v___x_2073_; lean_object* v___x_2074_; 
v___x_2072_ = ((size_t)1ULL);
v___x_2073_ = lean_usize_add(v_i_2064_, v___x_2072_);
v___x_2074_ = lean_array_uset(v_bs_x27_2069_, v_i_2064_, v___y_2071_);
v_i_2064_ = v___x_2073_;
v_bs_2065_ = v___x_2074_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12___boxed(lean_object* v___x_2085_, lean_object* v_sz_2086_, lean_object* v_i_2087_, lean_object* v_bs_2088_){
_start:
{
size_t v_sz_boxed_2089_; size_t v_i_boxed_2090_; lean_object* v_res_2091_; 
v_sz_boxed_2089_ = lean_unbox_usize(v_sz_2086_);
lean_dec(v_sz_2086_);
v_i_boxed_2090_ = lean_unbox_usize(v_i_2087_);
lean_dec(v_i_2087_);
v_res_2091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(v___x_2085_, v_sz_boxed_2089_, v_i_boxed_2090_, v_bs_2088_);
lean_dec_ref(v___x_2085_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16(lean_object* v___x_2092_, size_t v_sz_2093_, size_t v_i_2094_, lean_object* v_bs_2095_){
_start:
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_usize_dec_lt(v_i_2094_, v_sz_2093_);
if (v___x_2096_ == 0)
{
return v_bs_2095_;
}
else
{
lean_object* v_v_2097_; lean_object* v___x_2098_; lean_object* v_bs_x27_2099_; lean_object* v___x_2100_; size_t v___x_2101_; size_t v___x_2102_; lean_object* v___x_2103_; 
v_v_2097_ = lean_array_uget(v_bs_2095_, v_i_2094_);
v___x_2098_ = lean_unsigned_to_nat(0u);
v_bs_x27_2099_ = lean_array_uset(v_bs_2095_, v_i_2094_, v___x_2098_);
v___x_2100_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(v___x_2092_, v_v_2097_);
v___x_2101_ = ((size_t)1ULL);
v___x_2102_ = lean_usize_add(v_i_2094_, v___x_2101_);
v___x_2103_ = lean_array_uset(v_bs_x27_2099_, v_i_2094_, v___x_2100_);
v_i_2094_ = v___x_2102_;
v_bs_2095_ = v___x_2103_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(lean_object* v___x_2105_, lean_object* v_x_2106_){
_start:
{
if (lean_obj_tag(v_x_2106_) == 0)
{
lean_object* v_cs_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2117_; 
v_cs_2107_ = lean_ctor_get(v_x_2106_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_x_2106_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2109_ = v_x_2106_;
v_isShared_2110_ = v_isSharedCheck_2117_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_cs_2107_);
lean_dec(v_x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2117_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
size_t v_sz_2111_; size_t v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2115_; 
v_sz_2111_ = lean_array_size(v_cs_2107_);
v___x_2112_ = ((size_t)0ULL);
v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16(v___x_2105_, v_sz_2111_, v___x_2112_, v_cs_2107_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2113_);
v___x_2115_ = v___x_2109_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
else
{
lean_object* v_vs_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2128_; 
v_vs_2118_ = lean_ctor_get(v_x_2106_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_x_2106_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2120_ = v_x_2106_;
v_isShared_2121_ = v_isSharedCheck_2128_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_vs_2118_);
lean_dec(v_x_2106_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2128_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
size_t v_sz_2122_; size_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v_sz_2122_ = lean_array_size(v_vs_2118_);
v___x_2123_ = ((size_t)0ULL);
v___x_2124_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(v___x_2105_, v_sz_2122_, v___x_2123_, v_vs_2118_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2124_);
v___x_2126_ = v___x_2120_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11___boxed(lean_object* v___x_2129_, lean_object* v_x_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(v___x_2129_, v_x_2130_);
lean_dec_ref(v___x_2129_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16___boxed(lean_object* v___x_2132_, lean_object* v_sz_2133_, lean_object* v_i_2134_, lean_object* v_bs_2135_){
_start:
{
size_t v_sz_boxed_2136_; size_t v_i_boxed_2137_; lean_object* v_res_2138_; 
v_sz_boxed_2136_ = lean_unbox_usize(v_sz_2133_);
lean_dec(v_sz_2133_);
v_i_boxed_2137_ = lean_unbox_usize(v_i_2134_);
lean_dec(v_i_2134_);
v_res_2138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16(v___x_2132_, v_sz_boxed_2136_, v_i_boxed_2137_, v_bs_2135_);
lean_dec_ref(v___x_2132_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(lean_object* v___x_2139_, lean_object* v_t_2140_){
_start:
{
lean_object* v_root_2141_; lean_object* v_tail_2142_; lean_object* v_size_2143_; size_t v_shift_2144_; lean_object* v_tailOff_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2156_; 
v_root_2141_ = lean_ctor_get(v_t_2140_, 0);
v_tail_2142_ = lean_ctor_get(v_t_2140_, 1);
v_size_2143_ = lean_ctor_get(v_t_2140_, 2);
v_shift_2144_ = lean_ctor_get_usize(v_t_2140_, 4);
v_tailOff_2145_ = lean_ctor_get(v_t_2140_, 3);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_t_2140_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2147_ = v_t_2140_;
v_isShared_2148_ = v_isSharedCheck_2156_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_tailOff_2145_);
lean_inc(v_size_2143_);
lean_inc(v_tail_2142_);
lean_inc(v_root_2141_);
lean_dec(v_t_2140_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2156_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; size_t v_sz_2150_; size_t v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2149_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(v___x_2139_, v_root_2141_);
v_sz_2150_ = lean_array_size(v_tail_2142_);
v___x_2151_ = ((size_t)0ULL);
v___x_2152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(v___x_2139_, v_sz_2150_, v___x_2151_, v_tail_2142_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 1, v___x_2152_);
lean_ctor_set(v___x_2147_, 0, v___x_2149_);
v___x_2154_ = v___x_2147_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_size_2143_);
lean_ctor_set(v_reuseFailAlloc_2155_, 3, v_tailOff_2145_);
lean_ctor_set_usize(v_reuseFailAlloc_2155_, 4, v_shift_2144_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4___boxed(lean_object* v___x_2157_, lean_object* v_t_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(v___x_2157_, v_t_2158_);
lean_dec_ref(v___x_2157_);
return v_res_2159_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = lean_unsigned_to_nat(32u);
v___x_2161_ = lean_mk_empty_array_with_capacity(v___x_2160_);
v___x_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
return v___x_2162_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1(void){
_start:
{
size_t v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2163_ = ((size_t)5ULL);
v___x_2164_ = lean_unsigned_to_nat(0u);
v___x_2165_ = lean_unsigned_to_nat(32u);
v___x_2166_ = lean_mk_empty_array_with_capacity(v___x_2165_);
v___x_2167_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0);
v___x_2168_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
lean_ctor_set(v___x_2168_, 1, v___x_2166_);
lean_ctor_set(v___x_2168_, 2, v___x_2164_);
lean_ctor_set(v___x_2168_, 3, v___x_2164_);
lean_ctor_set_usize(v___x_2168_, 4, v___x_2163_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(size_t v_sz_2169_, size_t v_i_2170_, lean_object* v_bs_2171_){
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
lean_object* v___x_2173_; lean_object* v_bs_x27_2174_; lean_object* v___x_2175_; size_t v___x_2176_; size_t v___x_2177_; lean_object* v___x_2178_; 
v___x_2173_ = lean_unsigned_to_nat(0u);
v_bs_x27_2174_ = lean_array_uset(v_bs_2171_, v_i_2170_, v___x_2173_);
v___x_2175_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1);
v___x_2176_ = ((size_t)1ULL);
v___x_2177_ = lean_usize_add(v_i_2170_, v___x_2176_);
v___x_2178_ = lean_array_uset(v_bs_x27_2174_, v_i_2170_, v___x_2175_);
v_i_2170_ = v___x_2177_;
v_bs_2171_ = v___x_2178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___boxed(lean_object* v_sz_2180_, lean_object* v_i_2181_, lean_object* v_bs_2182_){
_start:
{
size_t v_sz_boxed_2183_; size_t v_i_boxed_2184_; lean_object* v_res_2185_; 
v_sz_boxed_2183_ = lean_unbox_usize(v_sz_2180_);
lean_dec(v_sz_2180_);
v_i_boxed_2184_ = lean_unbox_usize(v_i_2181_);
lean_dec(v_i_2181_);
v_res_2185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(v_sz_boxed_2183_, v_i_boxed_2184_, v_bs_2182_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12(size_t v_sz_2186_, size_t v_i_2187_, lean_object* v_bs_2188_){
_start:
{
uint8_t v___x_2189_; 
v___x_2189_ = lean_usize_dec_lt(v_i_2187_, v_sz_2186_);
if (v___x_2189_ == 0)
{
return v_bs_2188_;
}
else
{
lean_object* v_v_2190_; lean_object* v___x_2191_; lean_object* v_bs_x27_2192_; lean_object* v___x_2193_; size_t v___x_2194_; size_t v___x_2195_; lean_object* v___x_2196_; 
v_v_2190_ = lean_array_uget(v_bs_2188_, v_i_2187_);
v___x_2191_ = lean_unsigned_to_nat(0u);
v_bs_x27_2192_ = lean_array_uset(v_bs_2188_, v_i_2187_, v___x_2191_);
v___x_2193_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(v_v_2190_);
v___x_2194_ = ((size_t)1ULL);
v___x_2195_ = lean_usize_add(v_i_2187_, v___x_2194_);
v___x_2196_ = lean_array_uset(v_bs_x27_2192_, v_i_2187_, v___x_2193_);
v_i_2187_ = v___x_2195_;
v_bs_2188_ = v___x_2196_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(lean_object* v_x_2198_){
_start:
{
if (lean_obj_tag(v_x_2198_) == 0)
{
lean_object* v_cs_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2209_; 
v_cs_2199_ = lean_ctor_get(v_x_2198_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_x_2198_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2201_ = v_x_2198_;
v_isShared_2202_ = v_isSharedCheck_2209_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_cs_2199_);
lean_dec(v_x_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2209_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
size_t v_sz_2203_; size_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
v_sz_2203_ = lean_array_size(v_cs_2199_);
v___x_2204_ = ((size_t)0ULL);
v___x_2205_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12(v_sz_2203_, v___x_2204_, v_cs_2199_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2205_);
v___x_2207_ = v___x_2201_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
else
{
lean_object* v_vs_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2220_; 
v_vs_2210_ = lean_ctor_get(v_x_2198_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_x_2198_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2212_ = v_x_2198_;
v_isShared_2213_ = v_isSharedCheck_2220_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_vs_2210_);
lean_dec(v_x_2198_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2220_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
size_t v_sz_2214_; size_t v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2218_; 
v_sz_2214_ = lean_array_size(v_vs_2210_);
v___x_2215_ = ((size_t)0ULL);
v___x_2216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(v_sz_2214_, v___x_2215_, v_vs_2210_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2216_);
v___x_2218_ = v___x_2212_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12___boxed(lean_object* v_sz_2221_, lean_object* v_i_2222_, lean_object* v_bs_2223_){
_start:
{
size_t v_sz_boxed_2224_; size_t v_i_boxed_2225_; lean_object* v_res_2226_; 
v_sz_boxed_2224_ = lean_unbox_usize(v_sz_2221_);
lean_dec(v_sz_2221_);
v_i_boxed_2225_ = lean_unbox_usize(v_i_2222_);
lean_dec(v_i_2222_);
v_res_2226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12(v_sz_boxed_2224_, v_i_boxed_2225_, v_bs_2223_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(lean_object* v_t_2227_){
_start:
{
lean_object* v_root_2228_; lean_object* v_tail_2229_; lean_object* v_size_2230_; size_t v_shift_2231_; lean_object* v_tailOff_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2243_; 
v_root_2228_ = lean_ctor_get(v_t_2227_, 0);
v_tail_2229_ = lean_ctor_get(v_t_2227_, 1);
v_size_2230_ = lean_ctor_get(v_t_2227_, 2);
v_shift_2231_ = lean_ctor_get_usize(v_t_2227_, 4);
v_tailOff_2232_ = lean_ctor_get(v_t_2227_, 3);
v_isSharedCheck_2243_ = !lean_is_exclusive(v_t_2227_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2234_ = v_t_2227_;
v_isShared_2235_ = v_isSharedCheck_2243_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_tailOff_2232_);
lean_inc(v_size_2230_);
lean_inc(v_tail_2229_);
lean_inc(v_root_2228_);
lean_dec(v_t_2227_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2243_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; size_t v_sz_2237_; size_t v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2241_; 
v___x_2236_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(v_root_2228_);
v_sz_2237_ = lean_array_size(v_tail_2229_);
v___x_2238_ = ((size_t)0ULL);
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(v_sz_2237_, v___x_2238_, v_tail_2229_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 1, v___x_2239_);
lean_ctor_set(v___x_2234_, 0, v___x_2236_);
v___x_2241_ = v___x_2234_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v___x_2239_);
lean_ctor_set(v_reuseFailAlloc_2242_, 2, v_size_2230_);
lean_ctor_set(v_reuseFailAlloc_2242_, 3, v_tailOff_2232_);
lean_ctor_set_usize(v_reuseFailAlloc_2242_, 4, v_shift_2231_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = lean_unsigned_to_nat(32u);
v___x_2245_ = lean_mk_empty_array_with_capacity(v___x_2244_);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1(void){
_start:
{
size_t v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2247_ = ((size_t)5ULL);
v___x_2248_ = lean_unsigned_to_nat(0u);
v___x_2249_ = lean_unsigned_to_nat(32u);
v___x_2250_ = lean_mk_empty_array_with_capacity(v___x_2249_);
v___x_2251_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0);
v___x_2252_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v___x_2250_);
lean_ctor_set(v___x_2252_, 2, v___x_2248_);
lean_ctor_set(v___x_2252_, 3, v___x_2248_);
lean_ctor_set_usize(v___x_2252_, 4, v___x_2247_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(size_t v_sz_2253_, size_t v_i_2254_, lean_object* v_bs_2255_){
_start:
{
uint8_t v___x_2256_; 
v___x_2256_ = lean_usize_dec_lt(v_i_2254_, v_sz_2253_);
if (v___x_2256_ == 0)
{
return v_bs_2255_;
}
else
{
lean_object* v___x_2257_; lean_object* v_bs_x27_2258_; lean_object* v___x_2259_; size_t v___x_2260_; size_t v___x_2261_; lean_object* v___x_2262_; 
v___x_2257_ = lean_unsigned_to_nat(0u);
v_bs_x27_2258_ = lean_array_uset(v_bs_2255_, v_i_2254_, v___x_2257_);
v___x_2259_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1);
v___x_2260_ = ((size_t)1ULL);
v___x_2261_ = lean_usize_add(v_i_2254_, v___x_2260_);
v___x_2262_ = lean_array_uset(v_bs_x27_2258_, v_i_2254_, v___x_2259_);
v_i_2254_ = v___x_2261_;
v_bs_2255_ = v___x_2262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___boxed(lean_object* v_sz_2264_, lean_object* v_i_2265_, lean_object* v_bs_2266_){
_start:
{
size_t v_sz_boxed_2267_; size_t v_i_boxed_2268_; lean_object* v_res_2269_; 
v_sz_boxed_2267_ = lean_unbox_usize(v_sz_2264_);
lean_dec(v_sz_2264_);
v_i_boxed_2268_ = lean_unbox_usize(v_i_2265_);
lean_dec(v_i_2265_);
v_res_2269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(v_sz_boxed_2267_, v_i_boxed_2268_, v_bs_2266_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8(size_t v_sz_2270_, size_t v_i_2271_, lean_object* v_bs_2272_){
_start:
{
uint8_t v___x_2273_; 
v___x_2273_ = lean_usize_dec_lt(v_i_2271_, v_sz_2270_);
if (v___x_2273_ == 0)
{
return v_bs_2272_;
}
else
{
lean_object* v_v_2274_; lean_object* v___x_2275_; lean_object* v_bs_x27_2276_; lean_object* v___x_2277_; size_t v___x_2278_; size_t v___x_2279_; lean_object* v___x_2280_; 
v_v_2274_ = lean_array_uget(v_bs_2272_, v_i_2271_);
v___x_2275_ = lean_unsigned_to_nat(0u);
v_bs_x27_2276_ = lean_array_uset(v_bs_2272_, v_i_2271_, v___x_2275_);
v___x_2277_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(v_v_2274_);
v___x_2278_ = ((size_t)1ULL);
v___x_2279_ = lean_usize_add(v_i_2271_, v___x_2278_);
v___x_2280_ = lean_array_uset(v_bs_x27_2276_, v_i_2271_, v___x_2277_);
v_i_2271_ = v___x_2279_;
v_bs_2272_ = v___x_2280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(lean_object* v_x_2282_){
_start:
{
if (lean_obj_tag(v_x_2282_) == 0)
{
lean_object* v_cs_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2293_; 
v_cs_2283_ = lean_ctor_get(v_x_2282_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_x_2282_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2285_ = v_x_2282_;
v_isShared_2286_ = v_isSharedCheck_2293_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_cs_2283_);
lean_dec(v_x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2293_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
size_t v_sz_2287_; size_t v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2291_; 
v_sz_2287_ = lean_array_size(v_cs_2283_);
v___x_2288_ = ((size_t)0ULL);
v___x_2289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8(v_sz_2287_, v___x_2288_, v_cs_2283_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2289_);
v___x_2291_ = v___x_2285_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
else
{
lean_object* v_vs_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2304_; 
v_vs_2294_ = lean_ctor_get(v_x_2282_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v_x_2282_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2296_ = v_x_2282_;
v_isShared_2297_ = v_isSharedCheck_2304_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_vs_2294_);
lean_dec(v_x_2282_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2304_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
size_t v_sz_2298_; size_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
v_sz_2298_ = lean_array_size(v_vs_2294_);
v___x_2299_ = ((size_t)0ULL);
v___x_2300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(v_sz_2298_, v___x_2299_, v_vs_2294_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2300_);
v___x_2302_ = v___x_2296_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8___boxed(lean_object* v_sz_2305_, lean_object* v_i_2306_, lean_object* v_bs_2307_){
_start:
{
size_t v_sz_boxed_2308_; size_t v_i_boxed_2309_; lean_object* v_res_2310_; 
v_sz_boxed_2308_ = lean_unbox_usize(v_sz_2305_);
lean_dec(v_sz_2305_);
v_i_boxed_2309_ = lean_unbox_usize(v_i_2306_);
lean_dec(v_i_2306_);
v_res_2310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8(v_sz_boxed_2308_, v_i_boxed_2309_, v_bs_2307_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(lean_object* v_t_2311_){
_start:
{
lean_object* v_root_2312_; lean_object* v_tail_2313_; lean_object* v_size_2314_; size_t v_shift_2315_; lean_object* v_tailOff_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2327_; 
v_root_2312_ = lean_ctor_get(v_t_2311_, 0);
v_tail_2313_ = lean_ctor_get(v_t_2311_, 1);
v_size_2314_ = lean_ctor_get(v_t_2311_, 2);
v_shift_2315_ = lean_ctor_get_usize(v_t_2311_, 4);
v_tailOff_2316_ = lean_ctor_get(v_t_2311_, 3);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_t_2311_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2318_ = v_t_2311_;
v_isShared_2319_ = v_isSharedCheck_2327_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_tailOff_2316_);
lean_inc(v_size_2314_);
lean_inc(v_tail_2313_);
lean_inc(v_root_2312_);
lean_dec(v_t_2311_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2327_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2320_; size_t v_sz_2321_; size_t v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2320_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(v_root_2312_);
v_sz_2321_ = lean_array_size(v_tail_2313_);
v___x_2322_ = ((size_t)0ULL);
v___x_2323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(v_sz_2321_, v___x_2322_, v_tail_2313_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 1, v___x_2323_);
lean_ctor_set(v___x_2318_, 0, v___x_2320_);
v___x_2325_ = v___x_2318_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2320_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___x_2323_);
lean_ctor_set(v_reuseFailAlloc_2326_, 2, v_size_2314_);
lean_ctor_set(v_reuseFailAlloc_2326_, 3, v_tailOff_2316_);
lean_ctor_set_usize(v_reuseFailAlloc_2326_, 4, v_shift_2315_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(size_t v_sz_2328_, size_t v_i_2329_, lean_object* v_bs_2330_){
_start:
{
uint8_t v___x_2331_; 
v___x_2331_ = lean_usize_dec_lt(v_i_2329_, v_sz_2328_);
if (v___x_2331_ == 0)
{
return v_bs_2330_;
}
else
{
lean_object* v___x_2332_; lean_object* v_bs_x27_2333_; lean_object* v___x_2334_; size_t v___x_2335_; size_t v___x_2336_; lean_object* v___x_2337_; 
v___x_2332_ = lean_unsigned_to_nat(0u);
v_bs_x27_2333_ = lean_array_uset(v_bs_2330_, v_i_2329_, v___x_2332_);
v___x_2334_ = lean_box(1);
v___x_2335_ = ((size_t)1ULL);
v___x_2336_ = lean_usize_add(v_i_2329_, v___x_2335_);
v___x_2337_ = lean_array_uset(v_bs_x27_2333_, v_i_2329_, v___x_2334_);
v_i_2329_ = v___x_2336_;
v_bs_2330_ = v___x_2337_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16___boxed(lean_object* v_sz_2339_, lean_object* v_i_2340_, lean_object* v_bs_2341_){
_start:
{
size_t v_sz_boxed_2342_; size_t v_i_boxed_2343_; lean_object* v_res_2344_; 
v_sz_boxed_2342_ = lean_unbox_usize(v_sz_2339_);
lean_dec(v_sz_2339_);
v_i_boxed_2343_ = lean_unbox_usize(v_i_2340_);
lean_dec(v_i_2340_);
v_res_2344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(v_sz_boxed_2342_, v_i_boxed_2343_, v_bs_2341_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21(size_t v_sz_2345_, size_t v_i_2346_, lean_object* v_bs_2347_){
_start:
{
uint8_t v___x_2348_; 
v___x_2348_ = lean_usize_dec_lt(v_i_2346_, v_sz_2345_);
if (v___x_2348_ == 0)
{
return v_bs_2347_;
}
else
{
lean_object* v_v_2349_; lean_object* v___x_2350_; lean_object* v_bs_x27_2351_; lean_object* v___x_2352_; size_t v___x_2353_; size_t v___x_2354_; lean_object* v___x_2355_; 
v_v_2349_ = lean_array_uget(v_bs_2347_, v_i_2346_);
v___x_2350_ = lean_unsigned_to_nat(0u);
v_bs_x27_2351_ = lean_array_uset(v_bs_2347_, v_i_2346_, v___x_2350_);
v___x_2352_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(v_v_2349_);
v___x_2353_ = ((size_t)1ULL);
v___x_2354_ = lean_usize_add(v_i_2346_, v___x_2353_);
v___x_2355_ = lean_array_uset(v_bs_x27_2351_, v_i_2346_, v___x_2352_);
v_i_2346_ = v___x_2354_;
v_bs_2347_ = v___x_2355_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(lean_object* v_x_2357_){
_start:
{
if (lean_obj_tag(v_x_2357_) == 0)
{
lean_object* v_cs_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2368_; 
v_cs_2358_ = lean_ctor_get(v_x_2357_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_x_2357_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2360_ = v_x_2357_;
v_isShared_2361_ = v_isSharedCheck_2368_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_cs_2358_);
lean_dec(v_x_2357_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2368_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
size_t v_sz_2362_; size_t v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2366_; 
v_sz_2362_ = lean_array_size(v_cs_2358_);
v___x_2363_ = ((size_t)0ULL);
v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21(v_sz_2362_, v___x_2363_, v_cs_2358_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2364_);
v___x_2366_ = v___x_2360_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
else
{
lean_object* v_vs_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2379_; 
v_vs_2369_ = lean_ctor_get(v_x_2357_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v_x_2357_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2371_ = v_x_2357_;
v_isShared_2372_ = v_isSharedCheck_2379_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_vs_2369_);
lean_dec(v_x_2357_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2379_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
size_t v_sz_2373_; size_t v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
v_sz_2373_ = lean_array_size(v_vs_2369_);
v___x_2374_ = ((size_t)0ULL);
v___x_2375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(v_sz_2373_, v___x_2374_, v_vs_2369_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2375_);
v___x_2377_ = v___x_2371_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21___boxed(lean_object* v_sz_2380_, lean_object* v_i_2381_, lean_object* v_bs_2382_){
_start:
{
size_t v_sz_boxed_2383_; size_t v_i_boxed_2384_; lean_object* v_res_2385_; 
v_sz_boxed_2383_ = lean_unbox_usize(v_sz_2380_);
lean_dec(v_sz_2380_);
v_i_boxed_2384_ = lean_unbox_usize(v_i_2381_);
lean_dec(v_i_2381_);
v_res_2385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21(v_sz_boxed_2383_, v_i_boxed_2384_, v_bs_2382_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(lean_object* v_t_2386_){
_start:
{
lean_object* v_root_2387_; lean_object* v_tail_2388_; lean_object* v_size_2389_; size_t v_shift_2390_; lean_object* v_tailOff_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2402_; 
v_root_2387_ = lean_ctor_get(v_t_2386_, 0);
v_tail_2388_ = lean_ctor_get(v_t_2386_, 1);
v_size_2389_ = lean_ctor_get(v_t_2386_, 2);
v_shift_2390_ = lean_ctor_get_usize(v_t_2386_, 4);
v_tailOff_2391_ = lean_ctor_get(v_t_2386_, 3);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_t_2386_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2393_ = v_t_2386_;
v_isShared_2394_ = v_isSharedCheck_2402_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_tailOff_2391_);
lean_inc(v_size_2389_);
lean_inc(v_tail_2388_);
lean_inc(v_root_2387_);
lean_dec(v_t_2386_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2402_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; size_t v_sz_2396_; size_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2395_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(v_root_2387_);
v_sz_2396_ = lean_array_size(v_tail_2388_);
v___x_2397_ = ((size_t)0ULL);
v___x_2398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(v_sz_2396_, v___x_2397_, v_tail_2388_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 1, v___x_2398_);
lean_ctor_set(v___x_2393_, 0, v___x_2395_);
v___x_2400_ = v___x_2393_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2395_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2401_, 2, v_size_2389_);
lean_ctor_set(v_reuseFailAlloc_2401_, 3, v_tailOff_2391_);
lean_ctor_set_usize(v_reuseFailAlloc_2401_, 4, v_shift_2390_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(lean_object* v___x_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
if (lean_obj_tag(v_a_2404_) == 0)
{
lean_object* v___x_2406_; 
v___x_2406_ = l_List_reverse___redArg(v_a_2405_);
return v___x_2406_;
}
else
{
lean_object* v_head_2407_; lean_object* v_tail_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2418_; 
v_head_2407_ = lean_ctor_get(v_a_2404_, 0);
v_tail_2408_ = lean_ctor_get(v_a_2404_, 1);
v_isSharedCheck_2418_ = !lean_is_exclusive(v_a_2404_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2410_ = v_a_2404_;
v_isShared_2411_ = v_isSharedCheck_2418_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_tail_2408_);
lean_inc(v_head_2407_);
lean_dec(v_a_2404_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2418_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2412_ = lean_unsigned_to_nat(0u);
v___x_2413_ = lean_array_get_borrowed(v___x_2412_, v___x_2403_, v_head_2407_);
lean_dec(v_head_2407_);
lean_inc(v___x_2413_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 1, v_a_2405_);
lean_ctor_set(v___x_2410_, 0, v___x_2413_);
v___x_2415_ = v___x_2410_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_a_2405_);
v___x_2415_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
v_a_2404_ = v_tail_2408_;
v_a_2405_ = v___x_2415_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5___boxed(lean_object* v___x_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(v___x_2419_, v_a_2420_, v_a_2421_);
lean_dec_ref(v___x_2419_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(size_t v_sz_2423_, size_t v_i_2424_, lean_object* v_bs_2425_){
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
lean_object* v___x_2427_; lean_object* v_bs_x27_2428_; lean_object* v___x_2429_; size_t v___x_2430_; size_t v___x_2431_; lean_object* v___x_2432_; 
v___x_2427_ = lean_unsigned_to_nat(0u);
v_bs_x27_2428_ = lean_array_uset(v_bs_2425_, v_i_2424_, v___x_2427_);
v___x_2429_ = lean_box(0);
v___x_2430_ = ((size_t)1ULL);
v___x_2431_ = lean_usize_add(v_i_2424_, v___x_2430_);
v___x_2432_ = lean_array_uset(v_bs_x27_2428_, v_i_2424_, v___x_2429_);
v_i_2424_ = v___x_2431_;
v_bs_2425_ = v___x_2432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3___boxed(lean_object* v_sz_2434_, lean_object* v_i_2435_, lean_object* v_bs_2436_){
_start:
{
size_t v_sz_boxed_2437_; size_t v_i_boxed_2438_; lean_object* v_res_2439_; 
v_sz_boxed_2437_ = lean_unbox_usize(v_sz_2434_);
lean_dec(v_sz_2434_);
v_i_boxed_2438_ = lean_unbox_usize(v_i_2435_);
lean_dec(v_i_2435_);
v_res_2439_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_sz_boxed_2437_, v_i_boxed_2438_, v_bs_2436_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4(size_t v_sz_2440_, size_t v_i_2441_, lean_object* v_bs_2442_){
_start:
{
uint8_t v___x_2443_; 
v___x_2443_ = lean_usize_dec_lt(v_i_2441_, v_sz_2440_);
if (v___x_2443_ == 0)
{
return v_bs_2442_;
}
else
{
lean_object* v_v_2444_; lean_object* v___x_2445_; lean_object* v_bs_x27_2446_; lean_object* v___x_2447_; size_t v___x_2448_; size_t v___x_2449_; lean_object* v___x_2450_; 
v_v_2444_ = lean_array_uget(v_bs_2442_, v_i_2441_);
v___x_2445_ = lean_unsigned_to_nat(0u);
v_bs_x27_2446_ = lean_array_uset(v_bs_2442_, v_i_2441_, v___x_2445_);
v___x_2447_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(v_v_2444_);
v___x_2448_ = ((size_t)1ULL);
v___x_2449_ = lean_usize_add(v_i_2441_, v___x_2448_);
v___x_2450_ = lean_array_uset(v_bs_x27_2446_, v_i_2441_, v___x_2447_);
v_i_2441_ = v___x_2449_;
v_bs_2442_ = v___x_2450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(lean_object* v_x_2452_){
_start:
{
if (lean_obj_tag(v_x_2452_) == 0)
{
lean_object* v_cs_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2463_; 
v_cs_2453_ = lean_ctor_get(v_x_2452_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_x_2452_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2455_ = v_x_2452_;
v_isShared_2456_ = v_isSharedCheck_2463_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_cs_2453_);
lean_dec(v_x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2463_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
size_t v_sz_2457_; size_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2461_; 
v_sz_2457_ = lean_array_size(v_cs_2453_);
v___x_2458_ = ((size_t)0ULL);
v___x_2459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4(v_sz_2457_, v___x_2458_, v_cs_2453_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2459_);
v___x_2461_ = v___x_2455_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
else
{
lean_object* v_vs_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2474_; 
v_vs_2464_ = lean_ctor_get(v_x_2452_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_x_2452_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2466_ = v_x_2452_;
v_isShared_2467_ = v_isSharedCheck_2474_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_vs_2464_);
lean_dec(v_x_2452_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2474_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
size_t v_sz_2468_; size_t v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v_sz_2468_ = lean_array_size(v_vs_2464_);
v___x_2469_ = ((size_t)0ULL);
v___x_2470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_sz_2468_, v___x_2469_, v_vs_2464_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v___x_2470_);
v___x_2472_ = v___x_2466_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_2475_, lean_object* v_i_2476_, lean_object* v_bs_2477_){
_start:
{
size_t v_sz_boxed_2478_; size_t v_i_boxed_2479_; lean_object* v_res_2480_; 
v_sz_boxed_2478_ = lean_unbox_usize(v_sz_2475_);
lean_dec(v_sz_2475_);
v_i_boxed_2479_ = lean_unbox_usize(v_i_2476_);
lean_dec(v_i_2476_);
v_res_2480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4(v_sz_boxed_2478_, v_i_boxed_2479_, v_bs_2477_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(lean_object* v_t_2481_){
_start:
{
lean_object* v_root_2482_; lean_object* v_tail_2483_; lean_object* v_size_2484_; size_t v_shift_2485_; lean_object* v_tailOff_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2497_; 
v_root_2482_ = lean_ctor_get(v_t_2481_, 0);
v_tail_2483_ = lean_ctor_get(v_t_2481_, 1);
v_size_2484_ = lean_ctor_get(v_t_2481_, 2);
v_shift_2485_ = lean_ctor_get_usize(v_t_2481_, 4);
v_tailOff_2486_ = lean_ctor_get(v_t_2481_, 3);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_t_2481_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2488_ = v_t_2481_;
v_isShared_2489_ = v_isSharedCheck_2497_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_tailOff_2486_);
lean_inc(v_size_2484_);
lean_inc(v_tail_2483_);
lean_inc(v_root_2482_);
lean_dec(v_t_2481_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2497_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2490_; size_t v_sz_2491_; size_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2495_; 
v___x_2490_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(v_root_2482_);
v_sz_2491_ = lean_array_size(v_tail_2483_);
v___x_2492_ = ((size_t)0ULL);
v___x_2493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_sz_2491_, v___x_2492_, v_tail_2483_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 1, v___x_2493_);
lean_ctor_set(v___x_2488_, 0, v___x_2490_);
v___x_2495_ = v___x_2488_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_size_2484_);
lean_ctor_set(v_reuseFailAlloc_2496_, 3, v_tailOff_2486_);
lean_ctor_set_usize(v_reuseFailAlloc_2496_, 4, v_shift_2485_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(lean_object* v_a_2498_, lean_object* v___f_2499_, lean_object* v___x_2500_, lean_object* v_s_2501_){
_start:
{
lean_object* v_vars_2502_; lean_object* v_varMap_2503_; lean_object* v_natToIntMap_2504_; lean_object* v_natDef_2505_; lean_object* v_dvds_2506_; lean_object* v_lowers_2507_; lean_object* v_uppers_2508_; lean_object* v_diseqs_2509_; lean_object* v_elimEqs_2510_; lean_object* v_elimStack_2511_; lean_object* v_occurs_2512_; lean_object* v_assignment_2513_; lean_object* v_nextCnstrId_2514_; uint8_t v_caseSplits_2515_; lean_object* v_conflict_x3f_2516_; lean_object* v_divMod_2517_; lean_object* v_toIntIds_2518_; lean_object* v_toIntInfos_2519_; lean_object* v_toIntTermMap_2520_; lean_object* v_toIntVarMap_2521_; uint8_t v_usedCommRing_2522_; lean_object* v_nonlinearOccs_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2545_; 
v_vars_2502_ = lean_ctor_get(v_s_2501_, 0);
v_varMap_2503_ = lean_ctor_get(v_s_2501_, 1);
v_natToIntMap_2504_ = lean_ctor_get(v_s_2501_, 4);
v_natDef_2505_ = lean_ctor_get(v_s_2501_, 5);
v_dvds_2506_ = lean_ctor_get(v_s_2501_, 6);
v_lowers_2507_ = lean_ctor_get(v_s_2501_, 7);
v_uppers_2508_ = lean_ctor_get(v_s_2501_, 8);
v_diseqs_2509_ = lean_ctor_get(v_s_2501_, 9);
v_elimEqs_2510_ = lean_ctor_get(v_s_2501_, 10);
v_elimStack_2511_ = lean_ctor_get(v_s_2501_, 11);
v_occurs_2512_ = lean_ctor_get(v_s_2501_, 12);
v_assignment_2513_ = lean_ctor_get(v_s_2501_, 13);
v_nextCnstrId_2514_ = lean_ctor_get(v_s_2501_, 14);
v_caseSplits_2515_ = lean_ctor_get_uint8(v_s_2501_, sizeof(void*)*23);
v_conflict_x3f_2516_ = lean_ctor_get(v_s_2501_, 15);
v_divMod_2517_ = lean_ctor_get(v_s_2501_, 17);
v_toIntIds_2518_ = lean_ctor_get(v_s_2501_, 18);
v_toIntInfos_2519_ = lean_ctor_get(v_s_2501_, 19);
v_toIntTermMap_2520_ = lean_ctor_get(v_s_2501_, 20);
v_toIntVarMap_2521_ = lean_ctor_get(v_s_2501_, 21);
v_usedCommRing_2522_ = lean_ctor_get_uint8(v_s_2501_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2523_ = lean_ctor_get(v_s_2501_, 22);
v_isSharedCheck_2545_ = !lean_is_exclusive(v_s_2501_);
if (v_isSharedCheck_2545_ == 0)
{
lean_object* v_unused_2546_; lean_object* v_unused_2547_; lean_object* v_unused_2548_; 
v_unused_2546_ = lean_ctor_get(v_s_2501_, 16);
lean_dec(v_unused_2546_);
v_unused_2547_ = lean_ctor_get(v_s_2501_, 3);
lean_dec(v_unused_2547_);
v_unused_2548_ = lean_ctor_get(v_s_2501_, 2);
lean_dec(v_unused_2548_);
v___x_2525_ = v_s_2501_;
v_isShared_2526_ = v_isSharedCheck_2545_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_nonlinearOccs_2523_);
lean_inc(v_toIntVarMap_2521_);
lean_inc(v_toIntTermMap_2520_);
lean_inc(v_toIntInfos_2519_);
lean_inc(v_toIntIds_2518_);
lean_inc(v_divMod_2517_);
lean_inc(v_conflict_x3f_2516_);
lean_inc(v_nextCnstrId_2514_);
lean_inc(v_assignment_2513_);
lean_inc(v_occurs_2512_);
lean_inc(v_elimStack_2511_);
lean_inc(v_elimEqs_2510_);
lean_inc(v_diseqs_2509_);
lean_inc(v_uppers_2508_);
lean_inc(v_lowers_2507_);
lean_inc(v_dvds_2506_);
lean_inc(v_natDef_2505_);
lean_inc(v_natToIntMap_2504_);
lean_inc(v_varMap_2503_);
lean_inc(v_vars_2502_);
lean_dec(v_s_2501_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2545_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2543_; 
v___x_2527_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_a_2498_);
lean_inc_ref(v_vars_2502_);
v___x_2528_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2527_, v_vars_2502_, v_a_2498_);
lean_inc_ref(v___f_2499_);
lean_inc_ref(v_varMap_2503_);
v___x_2529_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(v_varMap_2503_, v___f_2499_);
v___x_2530_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(v_natDef_2505_, v___f_2499_);
v___x_2531_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(v_dvds_2506_);
v___x_2532_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(v_lowers_2507_);
v___x_2533_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(v_uppers_2508_);
v___x_2534_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(v_diseqs_2509_);
v___x_2535_ = lean_box(0);
v___x_2536_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2535_, v_elimEqs_2510_, v_a_2498_);
v___x_2537_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(v___x_2500_, v___x_2536_);
v___x_2538_ = lean_box(0);
v___x_2539_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(v___x_2500_, v_elimStack_2511_, v___x_2538_);
v___x_2540_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(v_occurs_2512_);
v___x_2541_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 16, v___x_2541_);
lean_ctor_set(v___x_2525_, 12, v___x_2540_);
lean_ctor_set(v___x_2525_, 11, v___x_2539_);
lean_ctor_set(v___x_2525_, 10, v___x_2537_);
lean_ctor_set(v___x_2525_, 9, v___x_2534_);
lean_ctor_set(v___x_2525_, 8, v___x_2533_);
lean_ctor_set(v___x_2525_, 7, v___x_2532_);
lean_ctor_set(v___x_2525_, 6, v___x_2531_);
lean_ctor_set(v___x_2525_, 5, v___x_2530_);
lean_ctor_set(v___x_2525_, 3, v_varMap_2503_);
lean_ctor_set(v___x_2525_, 2, v_vars_2502_);
lean_ctor_set(v___x_2525_, 1, v___x_2529_);
lean_ctor_set(v___x_2525_, 0, v___x_2528_);
v___x_2543_ = v___x_2525_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2544_, 2, v_vars_2502_);
lean_ctor_set(v_reuseFailAlloc_2544_, 3, v_varMap_2503_);
lean_ctor_set(v_reuseFailAlloc_2544_, 4, v_natToIntMap_2504_);
lean_ctor_set(v_reuseFailAlloc_2544_, 5, v___x_2530_);
lean_ctor_set(v_reuseFailAlloc_2544_, 6, v___x_2531_);
lean_ctor_set(v_reuseFailAlloc_2544_, 7, v___x_2532_);
lean_ctor_set(v_reuseFailAlloc_2544_, 8, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2544_, 9, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2544_, 10, v___x_2537_);
lean_ctor_set(v_reuseFailAlloc_2544_, 11, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2544_, 12, v___x_2540_);
lean_ctor_set(v_reuseFailAlloc_2544_, 13, v_assignment_2513_);
lean_ctor_set(v_reuseFailAlloc_2544_, 14, v_nextCnstrId_2514_);
lean_ctor_set(v_reuseFailAlloc_2544_, 15, v_conflict_x3f_2516_);
lean_ctor_set(v_reuseFailAlloc_2544_, 16, v___x_2541_);
lean_ctor_set(v_reuseFailAlloc_2544_, 17, v_divMod_2517_);
lean_ctor_set(v_reuseFailAlloc_2544_, 18, v_toIntIds_2518_);
lean_ctor_set(v_reuseFailAlloc_2544_, 19, v_toIntInfos_2519_);
lean_ctor_set(v_reuseFailAlloc_2544_, 20, v_toIntTermMap_2520_);
lean_ctor_set(v_reuseFailAlloc_2544_, 21, v_toIntVarMap_2521_);
lean_ctor_set(v_reuseFailAlloc_2544_, 22, v_nonlinearOccs_2523_);
lean_ctor_set_uint8(v_reuseFailAlloc_2544_, sizeof(void*)*23, v_caseSplits_2515_);
lean_ctor_set_uint8(v_reuseFailAlloc_2544_, sizeof(void*)*23 + 1, v_usedCommRing_2522_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed(lean_object* v_a_2549_, lean_object* v___f_2550_, lean_object* v___x_2551_, lean_object* v_s_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(v_a_2549_, v___f_2550_, v___x_2551_, v_s_2552_);
lean_dec_ref(v___x_2551_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(lean_object* v_as_2554_, size_t v_i_2555_, size_t v_stop_2556_, lean_object* v_b_2557_){
_start:
{
lean_object* v___y_2559_; uint8_t v___x_2563_; 
v___x_2563_ = lean_usize_dec_eq(v_i_2555_, v_stop_2556_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_array_uget_borrowed(v_as_2554_, v_i_2555_);
if (lean_obj_tag(v___x_2564_) == 0)
{
v___y_2559_ = v_b_2557_;
goto v___jp_2558_;
}
else
{
lean_object* v_val_2565_; lean_object* v___x_2566_; 
v_val_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_val_2565_);
v___x_2566_ = lean_array_push(v_b_2557_, v_val_2565_);
v___y_2559_ = v___x_2566_;
goto v___jp_2558_;
}
}
else
{
return v_b_2557_;
}
v___jp_2558_:
{
size_t v___x_2560_; size_t v___x_2561_; 
v___x_2560_ = ((size_t)1ULL);
v___x_2561_ = lean_usize_add(v_i_2555_, v___x_2560_);
v_i_2555_ = v___x_2561_;
v_b_2557_ = v___y_2559_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19___boxed(lean_object* v_as_2567_, lean_object* v_i_2568_, lean_object* v_stop_2569_, lean_object* v_b_2570_){
_start:
{
size_t v_i_boxed_2571_; size_t v_stop_boxed_2572_; lean_object* v_res_2573_; 
v_i_boxed_2571_ = lean_unbox_usize(v_i_2568_);
lean_dec(v_i_2568_);
v_stop_boxed_2572_ = lean_unbox_usize(v_stop_2569_);
lean_dec(v_stop_2569_);
v_res_2573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_as_2567_, v_i_boxed_2571_, v_stop_boxed_2572_, v_b_2570_);
lean_dec_ref(v_as_2567_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(lean_object* v_x_2574_, lean_object* v_x_2575_){
_start:
{
if (lean_obj_tag(v_x_2574_) == 0)
{
lean_object* v_cs_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; uint8_t v___x_2579_; 
v_cs_2576_ = lean_ctor_get(v_x_2574_, 0);
v___x_2577_ = lean_unsigned_to_nat(0u);
v___x_2578_ = lean_array_get_size(v_cs_2576_);
v___x_2579_ = lean_nat_dec_lt(v___x_2577_, v___x_2578_);
if (v___x_2579_ == 0)
{
return v_x_2575_;
}
else
{
uint8_t v___x_2580_; 
v___x_2580_ = lean_nat_dec_le(v___x_2578_, v___x_2578_);
if (v___x_2580_ == 0)
{
if (v___x_2579_ == 0)
{
return v_x_2575_;
}
else
{
size_t v___x_2581_; size_t v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = ((size_t)0ULL);
v___x_2582_ = lean_usize_of_nat(v___x_2578_);
v___x_2583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_cs_2576_, v___x_2581_, v___x_2582_, v_x_2575_);
return v___x_2583_;
}
}
else
{
size_t v___x_2584_; size_t v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = ((size_t)0ULL);
v___x_2585_ = lean_usize_of_nat(v___x_2578_);
v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_cs_2576_, v___x_2584_, v___x_2585_, v_x_2575_);
return v___x_2586_;
}
}
}
else
{
lean_object* v_vs_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; 
v_vs_2587_ = lean_ctor_get(v_x_2574_, 0);
v___x_2588_ = lean_unsigned_to_nat(0u);
v___x_2589_ = lean_array_get_size(v_vs_2587_);
v___x_2590_ = lean_nat_dec_lt(v___x_2588_, v___x_2589_);
if (v___x_2590_ == 0)
{
return v_x_2575_;
}
else
{
uint8_t v___x_2591_; 
v___x_2591_ = lean_nat_dec_le(v___x_2589_, v___x_2589_);
if (v___x_2591_ == 0)
{
if (v___x_2590_ == 0)
{
return v_x_2575_;
}
else
{
size_t v___x_2592_; size_t v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = ((size_t)0ULL);
v___x_2593_ = lean_usize_of_nat(v___x_2589_);
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_2587_, v___x_2592_, v___x_2593_, v_x_2575_);
return v___x_2594_;
}
}
else
{
size_t v___x_2595_; size_t v___x_2596_; lean_object* v___x_2597_; 
v___x_2595_ = ((size_t)0ULL);
v___x_2596_ = lean_usize_of_nat(v___x_2589_);
v___x_2597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_2587_, v___x_2595_, v___x_2596_, v_x_2575_);
return v___x_2597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(lean_object* v_as_2598_, size_t v_i_2599_, size_t v_stop_2600_, lean_object* v_b_2601_){
_start:
{
uint8_t v___x_2602_; 
v___x_2602_ = lean_usize_dec_eq(v_i_2599_, v_stop_2600_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; lean_object* v___x_2604_; size_t v___x_2605_; size_t v___x_2606_; 
v___x_2603_ = lean_array_uget_borrowed(v_as_2598_, v_i_2599_);
v___x_2604_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(v___x_2603_, v_b_2601_);
v___x_2605_ = ((size_t)1ULL);
v___x_2606_ = lean_usize_add(v_i_2599_, v___x_2605_);
v_i_2599_ = v___x_2606_;
v_b_2601_ = v___x_2604_;
goto _start;
}
else
{
return v_b_2601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25___boxed(lean_object* v_as_2608_, lean_object* v_i_2609_, lean_object* v_stop_2610_, lean_object* v_b_2611_){
_start:
{
size_t v_i_boxed_2612_; size_t v_stop_boxed_2613_; lean_object* v_res_2614_; 
v_i_boxed_2612_ = lean_unbox_usize(v_i_2609_);
lean_dec(v_i_2609_);
v_stop_boxed_2613_ = lean_unbox_usize(v_stop_2610_);
lean_dec(v_stop_2610_);
v_res_2614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_as_2608_, v_i_boxed_2612_, v_stop_boxed_2613_, v_b_2611_);
lean_dec_ref(v_as_2608_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20___boxed(lean_object* v_x_2615_, lean_object* v_x_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(v_x_2615_, v_x_2616_);
lean_dec_ref(v_x_2615_);
return v_res_2617_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0(void){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(lean_object* v_x_2619_, size_t v_x_2620_, size_t v_x_2621_, lean_object* v_x_2622_){
_start:
{
if (lean_obj_tag(v_x_2619_) == 0)
{
lean_object* v_cs_2623_; lean_object* v___x_2624_; size_t v___x_2625_; lean_object* v_j_2626_; lean_object* v___x_2627_; size_t v___x_2628_; size_t v___x_2629_; size_t v___x_2630_; size_t v___x_2631_; size_t v___x_2632_; size_t v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
v_cs_2623_ = lean_ctor_get(v_x_2619_, 0);
v___x_2624_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0);
v___x_2625_ = lean_usize_shift_right(v_x_2620_, v_x_2621_);
v_j_2626_ = lean_usize_to_nat(v___x_2625_);
v___x_2627_ = lean_array_get_borrowed(v___x_2624_, v_cs_2623_, v_j_2626_);
v___x_2628_ = ((size_t)1ULL);
v___x_2629_ = lean_usize_shift_left(v___x_2628_, v_x_2621_);
v___x_2630_ = lean_usize_sub(v___x_2629_, v___x_2628_);
v___x_2631_ = lean_usize_land(v_x_2620_, v___x_2630_);
v___x_2632_ = ((size_t)5ULL);
v___x_2633_ = lean_usize_sub(v_x_2621_, v___x_2632_);
v___x_2634_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(v___x_2627_, v___x_2631_, v___x_2633_, v_x_2622_);
v___x_2635_ = lean_unsigned_to_nat(1u);
v___x_2636_ = lean_nat_add(v_j_2626_, v___x_2635_);
lean_dec(v_j_2626_);
v___x_2637_ = lean_array_get_size(v_cs_2623_);
v___x_2638_ = lean_nat_dec_lt(v___x_2636_, v___x_2637_);
if (v___x_2638_ == 0)
{
lean_dec(v___x_2636_);
return v___x_2634_;
}
else
{
uint8_t v___x_2639_; 
v___x_2639_ = lean_nat_dec_le(v___x_2637_, v___x_2637_);
if (v___x_2639_ == 0)
{
if (v___x_2638_ == 0)
{
lean_dec(v___x_2636_);
return v___x_2634_;
}
else
{
size_t v___x_2640_; size_t v___x_2641_; lean_object* v___x_2642_; 
v___x_2640_ = lean_usize_of_nat(v___x_2636_);
lean_dec(v___x_2636_);
v___x_2641_ = lean_usize_of_nat(v___x_2637_);
v___x_2642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_cs_2623_, v___x_2640_, v___x_2641_, v___x_2634_);
return v___x_2642_;
}
}
else
{
size_t v___x_2643_; size_t v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = lean_usize_of_nat(v___x_2636_);
lean_dec(v___x_2636_);
v___x_2644_ = lean_usize_of_nat(v___x_2637_);
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_cs_2623_, v___x_2643_, v___x_2644_, v___x_2634_);
return v___x_2645_;
}
}
}
else
{
lean_object* v_vs_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v_vs_2646_ = lean_ctor_get(v_x_2619_, 0);
v___x_2647_ = lean_usize_to_nat(v_x_2620_);
v___x_2648_ = lean_array_get_size(v_vs_2646_);
v___x_2649_ = lean_nat_dec_lt(v___x_2647_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_dec(v___x_2647_);
return v_x_2622_;
}
else
{
uint8_t v___x_2650_; 
v___x_2650_ = lean_nat_dec_le(v___x_2648_, v___x_2648_);
if (v___x_2650_ == 0)
{
if (v___x_2649_ == 0)
{
lean_dec(v___x_2647_);
return v_x_2622_;
}
else
{
size_t v___x_2651_; size_t v___x_2652_; lean_object* v___x_2653_; 
v___x_2651_ = lean_usize_of_nat(v___x_2647_);
lean_dec(v___x_2647_);
v___x_2652_ = lean_usize_of_nat(v___x_2648_);
v___x_2653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_2646_, v___x_2651_, v___x_2652_, v_x_2622_);
return v___x_2653_;
}
}
else
{
size_t v___x_2654_; size_t v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = lean_usize_of_nat(v___x_2647_);
lean_dec(v___x_2647_);
v___x_2655_ = lean_usize_of_nat(v___x_2648_);
v___x_2656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_2646_, v___x_2654_, v___x_2655_, v_x_2622_);
return v___x_2656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___boxed(lean_object* v_x_2657_, lean_object* v_x_2658_, lean_object* v_x_2659_, lean_object* v_x_2660_){
_start:
{
size_t v_x_92062__boxed_2661_; size_t v_x_92063__boxed_2662_; lean_object* v_res_2663_; 
v_x_92062__boxed_2661_ = lean_unbox_usize(v_x_2658_);
lean_dec(v_x_2658_);
v_x_92063__boxed_2662_ = lean_unbox_usize(v_x_2659_);
lean_dec(v_x_2659_);
v_res_2663_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(v_x_2657_, v_x_92062__boxed_2661_, v_x_92063__boxed_2662_, v_x_2660_);
lean_dec_ref(v_x_2657_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(lean_object* v_t_2664_, lean_object* v_init_2665_, lean_object* v_start_2666_){
_start:
{
lean_object* v___x_2667_; uint8_t v___x_2668_; 
v___x_2667_ = lean_unsigned_to_nat(0u);
v___x_2668_ = lean_nat_dec_eq(v_start_2666_, v___x_2667_);
if (v___x_2668_ == 0)
{
lean_object* v_root_2669_; lean_object* v_tail_2670_; size_t v_shift_2671_; lean_object* v_tailOff_2672_; uint8_t v___x_2673_; 
v_root_2669_ = lean_ctor_get(v_t_2664_, 0);
v_tail_2670_ = lean_ctor_get(v_t_2664_, 1);
v_shift_2671_ = lean_ctor_get_usize(v_t_2664_, 4);
v_tailOff_2672_ = lean_ctor_get(v_t_2664_, 3);
v___x_2673_ = lean_nat_dec_le(v_tailOff_2672_, v_start_2666_);
if (v___x_2673_ == 0)
{
size_t v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2674_ = lean_usize_of_nat(v_start_2666_);
v___x_2675_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(v_root_2669_, v___x_2674_, v_shift_2671_, v_init_2665_);
v___x_2676_ = lean_array_get_size(v_tail_2670_);
v___x_2677_ = lean_nat_dec_lt(v___x_2667_, v___x_2676_);
if (v___x_2677_ == 0)
{
return v___x_2675_;
}
else
{
uint8_t v___x_2678_; 
v___x_2678_ = lean_nat_dec_le(v___x_2676_, v___x_2676_);
if (v___x_2678_ == 0)
{
if (v___x_2677_ == 0)
{
return v___x_2675_;
}
else
{
size_t v___x_2679_; size_t v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = ((size_t)0ULL);
v___x_2680_ = lean_usize_of_nat(v___x_2676_);
v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2670_, v___x_2679_, v___x_2680_, v___x_2675_);
return v___x_2681_;
}
}
else
{
size_t v___x_2682_; size_t v___x_2683_; lean_object* v___x_2684_; 
v___x_2682_ = ((size_t)0ULL);
v___x_2683_ = lean_usize_of_nat(v___x_2676_);
v___x_2684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2670_, v___x_2682_, v___x_2683_, v___x_2675_);
return v___x_2684_;
}
}
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2685_ = lean_nat_sub(v_start_2666_, v_tailOff_2672_);
v___x_2686_ = lean_array_get_size(v_tail_2670_);
v___x_2687_ = lean_nat_dec_lt(v___x_2685_, v___x_2686_);
if (v___x_2687_ == 0)
{
lean_dec(v___x_2685_);
return v_init_2665_;
}
else
{
uint8_t v___x_2688_; 
v___x_2688_ = lean_nat_dec_le(v___x_2686_, v___x_2686_);
if (v___x_2688_ == 0)
{
if (v___x_2687_ == 0)
{
lean_dec(v___x_2685_);
return v_init_2665_;
}
else
{
size_t v___x_2689_; size_t v___x_2690_; lean_object* v___x_2691_; 
v___x_2689_ = lean_usize_of_nat(v___x_2685_);
lean_dec(v___x_2685_);
v___x_2690_ = lean_usize_of_nat(v___x_2686_);
v___x_2691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2670_, v___x_2689_, v___x_2690_, v_init_2665_);
return v___x_2691_;
}
}
else
{
size_t v___x_2692_; size_t v___x_2693_; lean_object* v___x_2694_; 
v___x_2692_ = lean_usize_of_nat(v___x_2685_);
lean_dec(v___x_2685_);
v___x_2693_ = lean_usize_of_nat(v___x_2686_);
v___x_2694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2670_, v___x_2692_, v___x_2693_, v_init_2665_);
return v___x_2694_;
}
}
}
}
else
{
lean_object* v_root_2695_; lean_object* v_tail_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; uint8_t v___x_2699_; 
v_root_2695_ = lean_ctor_get(v_t_2664_, 0);
v_tail_2696_ = lean_ctor_get(v_t_2664_, 1);
v___x_2697_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(v_root_2695_, v_init_2665_);
v___x_2698_ = lean_array_get_size(v_tail_2696_);
v___x_2699_ = lean_nat_dec_lt(v___x_2667_, v___x_2698_);
if (v___x_2699_ == 0)
{
return v___x_2697_;
}
else
{
uint8_t v___x_2700_; 
v___x_2700_ = lean_nat_dec_le(v___x_2698_, v___x_2698_);
if (v___x_2700_ == 0)
{
if (v___x_2699_ == 0)
{
return v___x_2697_;
}
else
{
size_t v___x_2701_; size_t v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = ((size_t)0ULL);
v___x_2702_ = lean_usize_of_nat(v___x_2698_);
v___x_2703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2696_, v___x_2701_, v___x_2702_, v___x_2697_);
return v___x_2703_;
}
}
else
{
size_t v___x_2704_; size_t v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = ((size_t)0ULL);
v___x_2705_ = lean_usize_of_nat(v___x_2698_);
v___x_2706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2696_, v___x_2704_, v___x_2705_, v___x_2697_);
return v___x_2706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7___boxed(lean_object* v_t_2707_, lean_object* v_init_2708_, lean_object* v_start_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(v_t_2707_, v_init_2708_, v_start_2709_);
lean_dec(v_start_2709_);
lean_dec_ref(v_t_2707_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(lean_object* v_as_2711_, size_t v_i_2712_, size_t v_stop_2713_, lean_object* v_b_2714_){
_start:
{
uint8_t v___x_2715_; 
v___x_2715_ = lean_usize_dec_eq(v_i_2712_, v_stop_2713_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; size_t v___x_2719_; size_t v___x_2720_; 
v___x_2716_ = lean_array_uget_borrowed(v_as_2711_, v_i_2712_);
v___x_2717_ = l_Lean_PersistentArray_toArray___redArg(v___x_2716_);
v___x_2718_ = l_Array_append___redArg(v_b_2714_, v___x_2717_);
lean_dec_ref(v___x_2717_);
v___x_2719_ = ((size_t)1ULL);
v___x_2720_ = lean_usize_add(v_i_2712_, v___x_2719_);
v_i_2712_ = v___x_2720_;
v_b_2714_ = v___x_2718_;
goto _start;
}
else
{
return v_b_2714_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23___boxed(lean_object* v_as_2722_, lean_object* v_i_2723_, lean_object* v_stop_2724_, lean_object* v_b_2725_){
_start:
{
size_t v_i_boxed_2726_; size_t v_stop_boxed_2727_; lean_object* v_res_2728_; 
v_i_boxed_2726_ = lean_unbox_usize(v_i_2723_);
lean_dec(v_i_2723_);
v_stop_boxed_2727_ = lean_unbox_usize(v_stop_2724_);
lean_dec(v_stop_2724_);
v_res_2728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_as_2722_, v_i_boxed_2726_, v_stop_boxed_2727_, v_b_2725_);
lean_dec_ref(v_as_2722_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(lean_object* v_x_2729_, lean_object* v_x_2730_){
_start:
{
if (lean_obj_tag(v_x_2729_) == 0)
{
lean_object* v_cs_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v_cs_2731_ = lean_ctor_get(v_x_2729_, 0);
v___x_2732_ = lean_unsigned_to_nat(0u);
v___x_2733_ = lean_array_get_size(v_cs_2731_);
v___x_2734_ = lean_nat_dec_lt(v___x_2732_, v___x_2733_);
if (v___x_2734_ == 0)
{
return v_x_2730_;
}
else
{
uint8_t v___x_2735_; 
v___x_2735_ = lean_nat_dec_le(v___x_2733_, v___x_2733_);
if (v___x_2735_ == 0)
{
if (v___x_2734_ == 0)
{
return v_x_2730_;
}
else
{
size_t v___x_2736_; size_t v___x_2737_; lean_object* v___x_2738_; 
v___x_2736_ = ((size_t)0ULL);
v___x_2737_ = lean_usize_of_nat(v___x_2733_);
v___x_2738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_cs_2731_, v___x_2736_, v___x_2737_, v_x_2730_);
return v___x_2738_;
}
}
else
{
size_t v___x_2739_; size_t v___x_2740_; lean_object* v___x_2741_; 
v___x_2739_ = ((size_t)0ULL);
v___x_2740_ = lean_usize_of_nat(v___x_2733_);
v___x_2741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_cs_2731_, v___x_2739_, v___x_2740_, v_x_2730_);
return v___x_2741_;
}
}
}
else
{
lean_object* v_vs_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; 
v_vs_2742_ = lean_ctor_get(v_x_2729_, 0);
v___x_2743_ = lean_unsigned_to_nat(0u);
v___x_2744_ = lean_array_get_size(v_vs_2742_);
v___x_2745_ = lean_nat_dec_lt(v___x_2743_, v___x_2744_);
if (v___x_2745_ == 0)
{
return v_x_2730_;
}
else
{
uint8_t v___x_2746_; 
v___x_2746_ = lean_nat_dec_le(v___x_2744_, v___x_2744_);
if (v___x_2746_ == 0)
{
if (v___x_2745_ == 0)
{
return v_x_2730_;
}
else
{
size_t v___x_2747_; size_t v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = ((size_t)0ULL);
v___x_2748_ = lean_usize_of_nat(v___x_2744_);
v___x_2749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_2742_, v___x_2747_, v___x_2748_, v_x_2730_);
return v___x_2749_;
}
}
else
{
size_t v___x_2750_; size_t v___x_2751_; lean_object* v___x_2752_; 
v___x_2750_ = ((size_t)0ULL);
v___x_2751_ = lean_usize_of_nat(v___x_2744_);
v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_2742_, v___x_2750_, v___x_2751_, v_x_2730_);
return v___x_2752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(lean_object* v_as_2753_, size_t v_i_2754_, size_t v_stop_2755_, lean_object* v_b_2756_){
_start:
{
uint8_t v___x_2757_; 
v___x_2757_ = lean_usize_dec_eq(v_i_2754_, v_stop_2755_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; lean_object* v___x_2759_; size_t v___x_2760_; size_t v___x_2761_; 
v___x_2758_ = lean_array_uget_borrowed(v_as_2753_, v_i_2754_);
v___x_2759_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(v___x_2758_, v_b_2756_);
v___x_2760_ = ((size_t)1ULL);
v___x_2761_ = lean_usize_add(v_i_2754_, v___x_2760_);
v_i_2754_ = v___x_2761_;
v_b_2756_ = v___x_2759_;
goto _start;
}
else
{
return v_b_2756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30___boxed(lean_object* v_as_2763_, lean_object* v_i_2764_, lean_object* v_stop_2765_, lean_object* v_b_2766_){
_start:
{
size_t v_i_boxed_2767_; size_t v_stop_boxed_2768_; lean_object* v_res_2769_; 
v_i_boxed_2767_ = lean_unbox_usize(v_i_2764_);
lean_dec(v_i_2764_);
v_stop_boxed_2768_ = lean_unbox_usize(v_stop_2765_);
lean_dec(v_stop_2765_);
v_res_2769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_as_2763_, v_i_boxed_2767_, v_stop_boxed_2768_, v_b_2766_);
lean_dec_ref(v_as_2763_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24___boxed(lean_object* v_x_2770_, lean_object* v_x_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(v_x_2770_, v_x_2771_);
lean_dec_ref(v_x_2770_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(lean_object* v_x_2773_, size_t v_x_2774_, size_t v_x_2775_, lean_object* v_x_2776_){
_start:
{
if (lean_obj_tag(v_x_2773_) == 0)
{
lean_object* v_cs_2777_; lean_object* v___x_2778_; size_t v___x_2779_; lean_object* v_j_2780_; lean_object* v___x_2781_; size_t v___x_2782_; size_t v___x_2783_; size_t v___x_2784_; size_t v___x_2785_; size_t v___x_2786_; size_t v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; 
v_cs_2777_ = lean_ctor_get(v_x_2773_, 0);
v___x_2778_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0);
v___x_2779_ = lean_usize_shift_right(v_x_2774_, v_x_2775_);
v_j_2780_ = lean_usize_to_nat(v___x_2779_);
v___x_2781_ = lean_array_get_borrowed(v___x_2778_, v_cs_2777_, v_j_2780_);
v___x_2782_ = ((size_t)1ULL);
v___x_2783_ = lean_usize_shift_left(v___x_2782_, v_x_2775_);
v___x_2784_ = lean_usize_sub(v___x_2783_, v___x_2782_);
v___x_2785_ = lean_usize_land(v_x_2774_, v___x_2784_);
v___x_2786_ = ((size_t)5ULL);
v___x_2787_ = lean_usize_sub(v_x_2775_, v___x_2786_);
v___x_2788_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(v___x_2781_, v___x_2785_, v___x_2787_, v_x_2776_);
v___x_2789_ = lean_unsigned_to_nat(1u);
v___x_2790_ = lean_nat_add(v_j_2780_, v___x_2789_);
lean_dec(v_j_2780_);
v___x_2791_ = lean_array_get_size(v_cs_2777_);
v___x_2792_ = lean_nat_dec_lt(v___x_2790_, v___x_2791_);
if (v___x_2792_ == 0)
{
lean_dec(v___x_2790_);
return v___x_2788_;
}
else
{
uint8_t v___x_2793_; 
v___x_2793_ = lean_nat_dec_le(v___x_2791_, v___x_2791_);
if (v___x_2793_ == 0)
{
if (v___x_2792_ == 0)
{
lean_dec(v___x_2790_);
return v___x_2788_;
}
else
{
size_t v___x_2794_; size_t v___x_2795_; lean_object* v___x_2796_; 
v___x_2794_ = lean_usize_of_nat(v___x_2790_);
lean_dec(v___x_2790_);
v___x_2795_ = lean_usize_of_nat(v___x_2791_);
v___x_2796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_cs_2777_, v___x_2794_, v___x_2795_, v___x_2788_);
return v___x_2796_;
}
}
else
{
size_t v___x_2797_; size_t v___x_2798_; lean_object* v___x_2799_; 
v___x_2797_ = lean_usize_of_nat(v___x_2790_);
lean_dec(v___x_2790_);
v___x_2798_ = lean_usize_of_nat(v___x_2791_);
v___x_2799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_cs_2777_, v___x_2797_, v___x_2798_, v___x_2788_);
return v___x_2799_;
}
}
}
else
{
lean_object* v_vs_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v_vs_2800_ = lean_ctor_get(v_x_2773_, 0);
v___x_2801_ = lean_usize_to_nat(v_x_2774_);
v___x_2802_ = lean_array_get_size(v_vs_2800_);
v___x_2803_ = lean_nat_dec_lt(v___x_2801_, v___x_2802_);
if (v___x_2803_ == 0)
{
lean_dec(v___x_2801_);
return v_x_2776_;
}
else
{
uint8_t v___x_2804_; 
v___x_2804_ = lean_nat_dec_le(v___x_2802_, v___x_2802_);
if (v___x_2804_ == 0)
{
if (v___x_2803_ == 0)
{
lean_dec(v___x_2801_);
return v_x_2776_;
}
else
{
size_t v___x_2805_; size_t v___x_2806_; lean_object* v___x_2807_; 
v___x_2805_ = lean_usize_of_nat(v___x_2801_);
lean_dec(v___x_2801_);
v___x_2806_ = lean_usize_of_nat(v___x_2802_);
v___x_2807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_2800_, v___x_2805_, v___x_2806_, v_x_2776_);
return v___x_2807_;
}
}
else
{
size_t v___x_2808_; size_t v___x_2809_; lean_object* v___x_2810_; 
v___x_2808_ = lean_usize_of_nat(v___x_2801_);
lean_dec(v___x_2801_);
v___x_2809_ = lean_usize_of_nat(v___x_2802_);
v___x_2810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_2800_, v___x_2808_, v___x_2809_, v_x_2776_);
return v___x_2810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22___boxed(lean_object* v_x_2811_, lean_object* v_x_2812_, lean_object* v_x_2813_, lean_object* v_x_2814_){
_start:
{
size_t v_x_92286__boxed_2815_; size_t v_x_92287__boxed_2816_; lean_object* v_res_2817_; 
v_x_92286__boxed_2815_ = lean_unbox_usize(v_x_2812_);
lean_dec(v_x_2812_);
v_x_92287__boxed_2816_ = lean_unbox_usize(v_x_2813_);
lean_dec(v_x_2813_);
v_res_2817_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(v_x_2811_, v_x_92286__boxed_2815_, v_x_92287__boxed_2816_, v_x_2814_);
lean_dec_ref(v_x_2811_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(lean_object* v_t_2818_, lean_object* v_init_2819_, lean_object* v_start_2820_){
_start:
{
lean_object* v___x_2821_; uint8_t v___x_2822_; 
v___x_2821_ = lean_unsigned_to_nat(0u);
v___x_2822_ = lean_nat_dec_eq(v_start_2820_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_object* v_root_2823_; lean_object* v_tail_2824_; size_t v_shift_2825_; lean_object* v_tailOff_2826_; uint8_t v___x_2827_; 
v_root_2823_ = lean_ctor_get(v_t_2818_, 0);
v_tail_2824_ = lean_ctor_get(v_t_2818_, 1);
v_shift_2825_ = lean_ctor_get_usize(v_t_2818_, 4);
v_tailOff_2826_ = lean_ctor_get(v_t_2818_, 3);
v___x_2827_ = lean_nat_dec_le(v_tailOff_2826_, v_start_2820_);
if (v___x_2827_ == 0)
{
size_t v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v___x_2828_ = lean_usize_of_nat(v_start_2820_);
v___x_2829_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(v_root_2823_, v___x_2828_, v_shift_2825_, v_init_2819_);
v___x_2830_ = lean_array_get_size(v_tail_2824_);
v___x_2831_ = lean_nat_dec_lt(v___x_2821_, v___x_2830_);
if (v___x_2831_ == 0)
{
return v___x_2829_;
}
else
{
uint8_t v___x_2832_; 
v___x_2832_ = lean_nat_dec_le(v___x_2830_, v___x_2830_);
if (v___x_2832_ == 0)
{
if (v___x_2831_ == 0)
{
return v___x_2829_;
}
else
{
size_t v___x_2833_; size_t v___x_2834_; lean_object* v___x_2835_; 
v___x_2833_ = ((size_t)0ULL);
v___x_2834_ = lean_usize_of_nat(v___x_2830_);
v___x_2835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2824_, v___x_2833_, v___x_2834_, v___x_2829_);
return v___x_2835_;
}
}
else
{
size_t v___x_2836_; size_t v___x_2837_; lean_object* v___x_2838_; 
v___x_2836_ = ((size_t)0ULL);
v___x_2837_ = lean_usize_of_nat(v___x_2830_);
v___x_2838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2824_, v___x_2836_, v___x_2837_, v___x_2829_);
return v___x_2838_;
}
}
}
else
{
lean_object* v___x_2839_; lean_object* v___x_2840_; uint8_t v___x_2841_; 
v___x_2839_ = lean_nat_sub(v_start_2820_, v_tailOff_2826_);
v___x_2840_ = lean_array_get_size(v_tail_2824_);
v___x_2841_ = lean_nat_dec_lt(v___x_2839_, v___x_2840_);
if (v___x_2841_ == 0)
{
lean_dec(v___x_2839_);
return v_init_2819_;
}
else
{
uint8_t v___x_2842_; 
v___x_2842_ = lean_nat_dec_le(v___x_2840_, v___x_2840_);
if (v___x_2842_ == 0)
{
if (v___x_2841_ == 0)
{
lean_dec(v___x_2839_);
return v_init_2819_;
}
else
{
size_t v___x_2843_; size_t v___x_2844_; lean_object* v___x_2845_; 
v___x_2843_ = lean_usize_of_nat(v___x_2839_);
lean_dec(v___x_2839_);
v___x_2844_ = lean_usize_of_nat(v___x_2840_);
v___x_2845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2824_, v___x_2843_, v___x_2844_, v_init_2819_);
return v___x_2845_;
}
}
else
{
size_t v___x_2846_; size_t v___x_2847_; lean_object* v___x_2848_; 
v___x_2846_ = lean_usize_of_nat(v___x_2839_);
lean_dec(v___x_2839_);
v___x_2847_ = lean_usize_of_nat(v___x_2840_);
v___x_2848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2824_, v___x_2846_, v___x_2847_, v_init_2819_);
return v___x_2848_;
}
}
}
}
else
{
lean_object* v_root_2849_; lean_object* v_tail_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v_root_2849_ = lean_ctor_get(v_t_2818_, 0);
v_tail_2850_ = lean_ctor_get(v_t_2818_, 1);
v___x_2851_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(v_root_2849_, v_init_2819_);
v___x_2852_ = lean_array_get_size(v_tail_2850_);
v___x_2853_ = lean_nat_dec_lt(v___x_2821_, v___x_2852_);
if (v___x_2853_ == 0)
{
return v___x_2851_;
}
else
{
uint8_t v___x_2854_; 
v___x_2854_ = lean_nat_dec_le(v___x_2852_, v___x_2852_);
if (v___x_2854_ == 0)
{
if (v___x_2853_ == 0)
{
return v___x_2851_;
}
else
{
size_t v___x_2855_; size_t v___x_2856_; lean_object* v___x_2857_; 
v___x_2855_ = ((size_t)0ULL);
v___x_2856_ = lean_usize_of_nat(v___x_2852_);
v___x_2857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2850_, v___x_2855_, v___x_2856_, v___x_2851_);
return v___x_2857_;
}
}
else
{
size_t v___x_2858_; size_t v___x_2859_; lean_object* v___x_2860_; 
v___x_2858_ = ((size_t)0ULL);
v___x_2859_ = lean_usize_of_nat(v___x_2852_);
v___x_2860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2850_, v___x_2858_, v___x_2859_, v___x_2851_);
return v___x_2860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8___boxed(lean_object* v_t_2861_, lean_object* v_init_2862_, lean_object* v_start_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_t_2861_, v_init_2862_, v_start_2863_);
lean_dec(v_start_2863_);
lean_dec_ref(v_t_2861_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(lean_object* v___x_2865_, size_t v_sz_2866_, size_t v_i_2867_, lean_object* v_bs_2868_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10___boxed(lean_object* v___x_2878_, lean_object* v_sz_2879_, lean_object* v_i_2880_, lean_object* v_bs_2881_){
_start:
{
size_t v_sz_boxed_2882_; size_t v_i_boxed_2883_; lean_object* v_res_2884_; 
v_sz_boxed_2882_ = lean_unbox_usize(v_sz_2879_);
lean_dec(v_sz_2879_);
v_i_boxed_2883_ = lean_unbox_usize(v_i_2880_);
lean_dec(v_i_2880_);
v_res_2884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v___x_2878_, v_sz_boxed_2882_, v_i_boxed_2883_, v_bs_2881_);
lean_dec_ref(v___x_2878_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(lean_object* v___x_2885_, size_t v_sz_2886_, size_t v_i_2887_, lean_object* v_bs_2888_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14___boxed(lean_object* v___x_2898_, lean_object* v_sz_2899_, lean_object* v_i_2900_, lean_object* v_bs_2901_){
_start:
{
size_t v_sz_boxed_2902_; size_t v_i_boxed_2903_; lean_object* v_res_2904_; 
v_sz_boxed_2902_ = lean_unbox_usize(v_sz_2899_);
lean_dec(v_sz_2899_);
v_i_boxed_2903_ = lean_unbox_usize(v_i_2900_);
lean_dec(v_i_2900_);
v_res_2904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v___x_2898_, v_sz_boxed_2902_, v_i_boxed_2903_, v_bs_2901_);
lean_dec_ref(v___x_2898_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37(lean_object* v_msgData_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v___x_2911_; lean_object* v_env_2912_; lean_object* v___x_2913_; lean_object* v_mctx_2914_; lean_object* v_lctx_2915_; lean_object* v_options_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2911_ = lean_st_ref_get(v___y_2909_);
v_env_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc_ref(v_env_2912_);
lean_dec(v___x_2911_);
v___x_2913_ = lean_st_ref_get(v___y_2907_);
v_mctx_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc_ref(v_mctx_2914_);
lean_dec(v___x_2913_);
v_lctx_2915_ = lean_ctor_get(v___y_2906_, 2);
v_options_2916_ = lean_ctor_get(v___y_2908_, 2);
lean_inc_ref(v_options_2916_);
lean_inc_ref(v_lctx_2915_);
v___x_2917_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2917_, 0, v_env_2912_);
lean_ctor_set(v___x_2917_, 1, v_mctx_2914_);
lean_ctor_set(v___x_2917_, 2, v_lctx_2915_);
lean_ctor_set(v___x_2917_, 3, v_options_2916_);
v___x_2918_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
lean_ctor_set(v___x_2918_, 1, v_msgData_2905_);
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37___boxed(lean_object* v_msgData_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37(v_msgData_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
return v_res_2926_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0(void){
_start:
{
lean_object* v___x_2927_; double v___x_2928_; 
v___x_2927_ = lean_unsigned_to_nat(0u);
v___x_2928_ = lean_float_of_nat(v___x_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(lean_object* v_cls_2932_, lean_object* v_msg_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_ref_2939_; lean_object* v___x_2940_; lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2985_; 
v_ref_2939_ = lean_ctor_get(v___y_2936_, 5);
v___x_2940_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37(v_msg_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_2985_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2985_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v_traceState_2946_; lean_object* v_env_2947_; lean_object* v_nextMacroScope_2948_; lean_object* v_ngen_2949_; lean_object* v_auxDeclNGen_2950_; lean_object* v_cache_2951_; lean_object* v_messages_2952_; lean_object* v_infoState_2953_; lean_object* v_snapshotTasks_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2984_; 
v___x_2945_ = lean_st_ref_take(v___y_2937_);
v_traceState_2946_ = lean_ctor_get(v___x_2945_, 4);
v_env_2947_ = lean_ctor_get(v___x_2945_, 0);
v_nextMacroScope_2948_ = lean_ctor_get(v___x_2945_, 1);
v_ngen_2949_ = lean_ctor_get(v___x_2945_, 2);
v_auxDeclNGen_2950_ = lean_ctor_get(v___x_2945_, 3);
v_cache_2951_ = lean_ctor_get(v___x_2945_, 5);
v_messages_2952_ = lean_ctor_get(v___x_2945_, 6);
v_infoState_2953_ = lean_ctor_get(v___x_2945_, 7);
v_snapshotTasks_2954_ = lean_ctor_get(v___x_2945_, 8);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2956_ = v___x_2945_;
v_isShared_2957_ = v_isSharedCheck_2984_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_snapshotTasks_2954_);
lean_inc(v_infoState_2953_);
lean_inc(v_messages_2952_);
lean_inc(v_cache_2951_);
lean_inc(v_traceState_2946_);
lean_inc(v_auxDeclNGen_2950_);
lean_inc(v_ngen_2949_);
lean_inc(v_nextMacroScope_2948_);
lean_inc(v_env_2947_);
lean_dec(v___x_2945_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2984_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
uint64_t v_tid_2958_; lean_object* v_traces_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2983_; 
v_tid_2958_ = lean_ctor_get_uint64(v_traceState_2946_, sizeof(void*)*1);
v_traces_2959_ = lean_ctor_get(v_traceState_2946_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_traceState_2946_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2961_ = v_traceState_2946_;
v_isShared_2962_ = v_isSharedCheck_2983_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_traces_2959_);
lean_dec(v_traceState_2946_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2983_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; double v___x_2964_; uint8_t v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2963_ = lean_box(0);
v___x_2964_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0);
v___x_2965_ = 0;
v___x_2966_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__1));
v___x_2967_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2967_, 0, v_cls_2932_);
lean_ctor_set(v___x_2967_, 1, v___x_2963_);
lean_ctor_set(v___x_2967_, 2, v___x_2966_);
lean_ctor_set_float(v___x_2967_, sizeof(void*)*3, v___x_2964_);
lean_ctor_set_float(v___x_2967_, sizeof(void*)*3 + 8, v___x_2964_);
lean_ctor_set_uint8(v___x_2967_, sizeof(void*)*3 + 16, v___x_2965_);
v___x_2968_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__2));
v___x_2969_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2967_);
lean_ctor_set(v___x_2969_, 1, v_a_2941_);
lean_ctor_set(v___x_2969_, 2, v___x_2968_);
lean_inc(v_ref_2939_);
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v_ref_2939_);
lean_ctor_set(v___x_2970_, 1, v___x_2969_);
v___x_2971_ = l_Lean_PersistentArray_push___redArg(v_traces_2959_, v___x_2970_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v___x_2971_);
v___x_2973_ = v___x_2961_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2971_);
lean_ctor_set_uint64(v_reuseFailAlloc_2982_, sizeof(void*)*1, v_tid_2958_);
v___x_2973_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2975_; 
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 4, v___x_2973_);
v___x_2975_ = v___x_2956_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_env_2947_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_nextMacroScope_2948_);
lean_ctor_set(v_reuseFailAlloc_2981_, 2, v_ngen_2949_);
lean_ctor_set(v_reuseFailAlloc_2981_, 3, v_auxDeclNGen_2950_);
lean_ctor_set(v_reuseFailAlloc_2981_, 4, v___x_2973_);
lean_ctor_set(v_reuseFailAlloc_2981_, 5, v_cache_2951_);
lean_ctor_set(v_reuseFailAlloc_2981_, 6, v_messages_2952_);
lean_ctor_set(v_reuseFailAlloc_2981_, 7, v_infoState_2953_);
lean_ctor_set(v_reuseFailAlloc_2981_, 8, v_snapshotTasks_2954_);
v___x_2975_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2979_; 
v___x_2976_ = lean_st_ref_set(v___y_2937_, v___x_2975_);
v___x_2977_ = lean_box(0);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2977_);
v___x_2979_ = v___x_2943_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___boxed(lean_object* v_cls_2986_, lean_object* v_msg_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(v_cls_2986_, v_msg_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(lean_object* v___x_2994_, size_t v_sz_2995_, size_t v_i_2996_, lean_object* v_bs_2997_){
_start:
{
uint8_t v___x_2998_; 
v___x_2998_ = lean_usize_dec_lt(v_i_2996_, v_sz_2995_);
if (v___x_2998_ == 0)
{
return v_bs_2997_;
}
else
{
lean_object* v_v_2999_; lean_object* v___x_3000_; lean_object* v_bs_x27_3001_; lean_object* v___x_3002_; size_t v___x_3003_; size_t v___x_3004_; lean_object* v___x_3005_; 
v_v_2999_ = lean_array_uget(v_bs_2997_, v_i_2996_);
v___x_3000_ = lean_unsigned_to_nat(0u);
v_bs_x27_3001_ = lean_array_uset(v_bs_2997_, v_i_2996_, v___x_3000_);
v___x_3002_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_v_2999_, v___x_2994_);
v___x_3003_ = ((size_t)1ULL);
v___x_3004_ = lean_usize_add(v_i_2996_, v___x_3003_);
v___x_3005_ = lean_array_uset(v_bs_x27_3001_, v_i_2996_, v___x_3002_);
v_i_2996_ = v___x_3004_;
v_bs_2997_ = v___x_3005_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12___boxed(lean_object* v___x_3007_, lean_object* v_sz_3008_, lean_object* v_i_3009_, lean_object* v_bs_3010_){
_start:
{
size_t v_sz_boxed_3011_; size_t v_i_boxed_3012_; lean_object* v_res_3013_; 
v_sz_boxed_3011_ = lean_unbox_usize(v_sz_3008_);
lean_dec(v_sz_3008_);
v_i_boxed_3012_ = lean_unbox_usize(v_i_3009_);
lean_dec(v_i_3009_);
v_res_3013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v___x_3007_, v_sz_boxed_3011_, v_i_boxed_3012_, v_bs_3010_);
lean_dec_ref(v___x_3007_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(lean_object* v_as_3014_, size_t v_sz_3015_, size_t v_i_3016_, lean_object* v_b_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
uint8_t v___x_3029_; 
v___x_3029_ = lean_usize_dec_lt(v_i_3016_, v_sz_3015_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; 
v___x_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3030_, 0, v_b_3017_);
return v___x_3030_;
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3032_; 
v_a_3031_ = lean_array_uget_borrowed(v_as_3014_, v_i_3016_);
lean_inc(v_a_3031_);
v___x_3032_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_assert(v_a_3031_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v___x_3033_; size_t v___x_3034_; size_t v___x_3035_; 
lean_dec_ref(v___x_3032_);
v___x_3033_ = lean_box(0);
v___x_3034_ = ((size_t)1ULL);
v___x_3035_ = lean_usize_add(v_i_3016_, v___x_3034_);
v_i_3016_ = v___x_3035_;
v_b_3017_ = v___x_3033_;
goto _start;
}
else
{
return v___x_3032_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15___boxed(lean_object* v_as_3037_, lean_object* v_sz_3038_, lean_object* v_i_3039_, lean_object* v_b_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
size_t v_sz_boxed_3052_; size_t v_i_boxed_3053_; lean_object* v_res_3054_; 
v_sz_boxed_3052_ = lean_unbox_usize(v_sz_3038_);
lean_dec(v_sz_3038_);
v_i_boxed_3053_ = lean_unbox_usize(v_i_3039_);
lean_dec(v_i_3039_);
v_res_3054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v_as_3037_, v_sz_boxed_3052_, v_i_boxed_3053_, v_b_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v_as_3037_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(lean_object* v_as_3055_, size_t v_sz_3056_, size_t v_i_3057_, lean_object* v_b_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
uint8_t v___x_3070_; 
v___x_3070_ = lean_usize_dec_lt(v_i_3057_, v_sz_3056_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; 
v___x_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3071_, 0, v_b_3058_);
return v___x_3071_;
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3073_; 
v_a_3072_ = lean_array_uget_borrowed(v_as_3055_, v_i_3057_);
lean_inc(v___y_3068_);
lean_inc_ref(v___y_3067_);
lean_inc(v___y_3066_);
lean_inc_ref(v___y_3065_);
lean_inc(v___y_3064_);
lean_inc_ref(v___y_3063_);
lean_inc(v___y_3062_);
lean_inc_ref(v___y_3061_);
lean_inc(v___y_3060_);
lean_inc(v___y_3059_);
lean_inc(v_a_3072_);
v___x_3073_ = lean_grind_cutsat_assert_le(v_a_3072_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v___x_3074_; size_t v___x_3075_; size_t v___x_3076_; 
lean_dec_ref(v___x_3073_);
v___x_3074_ = lean_box(0);
v___x_3075_ = ((size_t)1ULL);
v___x_3076_ = lean_usize_add(v_i_3057_, v___x_3075_);
v_i_3057_ = v___x_3076_;
v_b_3058_ = v___x_3074_;
goto _start;
}
else
{
return v___x_3073_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13___boxed(lean_object* v_as_3078_, lean_object* v_sz_3079_, lean_object* v_i_3080_, lean_object* v_b_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
size_t v_sz_boxed_3093_; size_t v_i_boxed_3094_; lean_object* v_res_3095_; 
v_sz_boxed_3093_ = lean_unbox_usize(v_sz_3079_);
lean_dec(v_sz_3079_);
v_i_boxed_3094_ = lean_unbox_usize(v_i_3080_);
lean_dec(v_i_3080_);
v_res_3095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v_as_3078_, v_sz_boxed_3093_, v_i_boxed_3094_, v_b_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v_as_3078_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(lean_object* v_a_3096_, lean_object* v_a_3097_){
_start:
{
if (lean_obj_tag(v_a_3096_) == 0)
{
lean_object* v___x_3098_; 
v___x_3098_ = l_List_reverse___redArg(v_a_3097_);
return v___x_3098_;
}
else
{
lean_object* v_head_3099_; lean_object* v_tail_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3111_; 
v_head_3099_ = lean_ctor_get(v_a_3096_, 0);
v_tail_3100_ = lean_ctor_get(v_a_3096_, 1);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_a_3096_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3102_ = v_a_3096_;
v_isShared_3103_ = v_isSharedCheck_3111_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_tail_3100_);
lean_inc(v_head_3099_);
lean_dec(v_a_3096_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3111_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3104_ = l_Nat_reprFast(v_head_3099_);
v___x_3105_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
v___x_3106_ = l_Lean_MessageData_ofFormat(v___x_3105_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 1, v_a_3097_);
lean_ctor_set(v___x_3102_, 0, v___x_3106_);
v___x_3108_ = v___x_3102_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3106_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_a_3097_);
v___x_3108_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
v_a_3096_ = v_tail_3100_;
v_a_3097_ = v___x_3108_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(lean_object* v_as_3112_, size_t v_sz_3113_, size_t v_i_3114_, lean_object* v_b_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
uint8_t v___x_3127_; 
v___x_3127_ = lean_usize_dec_lt(v_i_3114_, v_sz_3113_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3128_; 
v___x_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3128_, 0, v_b_3115_);
return v___x_3128_;
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3130_; 
v_a_3129_ = lean_array_uget_borrowed(v_as_3112_, v_i_3114_);
lean_inc_ref(v___y_3124_);
lean_inc(v_a_3129_);
v___x_3130_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_a_3129_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v___x_3131_; size_t v___x_3132_; size_t v___x_3133_; 
lean_dec_ref(v___x_3130_);
v___x_3131_ = lean_box(0);
v___x_3132_ = ((size_t)1ULL);
v___x_3133_ = lean_usize_add(v_i_3114_, v___x_3132_);
v_i_3114_ = v___x_3133_;
v_b_3115_ = v___x_3131_;
goto _start;
}
else
{
return v___x_3130_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11___boxed(lean_object* v_as_3135_, lean_object* v_sz_3136_, lean_object* v_i_3137_, lean_object* v_b_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
size_t v_sz_boxed_3150_; size_t v_i_boxed_3151_; lean_object* v_res_3152_; 
v_sz_boxed_3150_ = lean_unbox_usize(v_sz_3136_);
lean_dec(v_sz_3136_);
v_i_boxed_3151_ = lean_unbox_usize(v_i_3137_);
lean_dec(v_i_3137_);
v_res_3152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v_as_3135_, v_sz_boxed_3150_, v_i_boxed_3151_, v_b_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec_ref(v_as_3135_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(lean_object* v_as_3153_, size_t v_i_3154_, size_t v_stop_3155_, lean_object* v_b_3156_){
_start:
{
uint8_t v___x_3157_; 
v___x_3157_ = lean_usize_dec_eq(v_i_3154_, v_stop_3155_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; size_t v___x_3161_; size_t v___x_3162_; 
v___x_3158_ = lean_array_uget_borrowed(v_as_3153_, v_i_3154_);
v___x_3159_ = l_Lean_PersistentArray_toArray___redArg(v___x_3158_);
v___x_3160_ = l_Array_append___redArg(v_b_3156_, v___x_3159_);
lean_dec_ref(v___x_3159_);
v___x_3161_ = ((size_t)1ULL);
v___x_3162_ = lean_usize_add(v_i_3154_, v___x_3161_);
v_i_3154_ = v___x_3162_;
v_b_3156_ = v___x_3160_;
goto _start;
}
else
{
return v_b_3156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27___boxed(lean_object* v_as_3164_, lean_object* v_i_3165_, lean_object* v_stop_3166_, lean_object* v_b_3167_){
_start:
{
size_t v_i_boxed_3168_; size_t v_stop_boxed_3169_; lean_object* v_res_3170_; 
v_i_boxed_3168_ = lean_unbox_usize(v_i_3165_);
lean_dec(v_i_3165_);
v_stop_boxed_3169_ = lean_unbox_usize(v_stop_3166_);
lean_dec(v_stop_3166_);
v_res_3170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_as_3164_, v_i_boxed_3168_, v_stop_boxed_3169_, v_b_3167_);
lean_dec_ref(v_as_3164_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(lean_object* v_x_3171_, lean_object* v_x_3172_){
_start:
{
if (lean_obj_tag(v_x_3171_) == 0)
{
lean_object* v_cs_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; uint8_t v___x_3176_; 
v_cs_3173_ = lean_ctor_get(v_x_3171_, 0);
v___x_3174_ = lean_unsigned_to_nat(0u);
v___x_3175_ = lean_array_get_size(v_cs_3173_);
v___x_3176_ = lean_nat_dec_lt(v___x_3174_, v___x_3175_);
if (v___x_3176_ == 0)
{
return v_x_3172_;
}
else
{
uint8_t v___x_3177_; 
v___x_3177_ = lean_nat_dec_le(v___x_3175_, v___x_3175_);
if (v___x_3177_ == 0)
{
if (v___x_3176_ == 0)
{
return v_x_3172_;
}
else
{
size_t v___x_3178_; size_t v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = ((size_t)0ULL);
v___x_3179_ = lean_usize_of_nat(v___x_3175_);
v___x_3180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_cs_3173_, v___x_3178_, v___x_3179_, v_x_3172_);
return v___x_3180_;
}
}
else
{
size_t v___x_3181_; size_t v___x_3182_; lean_object* v___x_3183_; 
v___x_3181_ = ((size_t)0ULL);
v___x_3182_ = lean_usize_of_nat(v___x_3175_);
v___x_3183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_cs_3173_, v___x_3181_, v___x_3182_, v_x_3172_);
return v___x_3183_;
}
}
}
else
{
lean_object* v_vs_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; uint8_t v___x_3187_; 
v_vs_3184_ = lean_ctor_get(v_x_3171_, 0);
v___x_3185_ = lean_unsigned_to_nat(0u);
v___x_3186_ = lean_array_get_size(v_vs_3184_);
v___x_3187_ = lean_nat_dec_lt(v___x_3185_, v___x_3186_);
if (v___x_3187_ == 0)
{
return v_x_3172_;
}
else
{
uint8_t v___x_3188_; 
v___x_3188_ = lean_nat_dec_le(v___x_3186_, v___x_3186_);
if (v___x_3188_ == 0)
{
if (v___x_3187_ == 0)
{
return v_x_3172_;
}
else
{
size_t v___x_3189_; size_t v___x_3190_; lean_object* v___x_3191_; 
v___x_3189_ = ((size_t)0ULL);
v___x_3190_ = lean_usize_of_nat(v___x_3186_);
v___x_3191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_3184_, v___x_3189_, v___x_3190_, v_x_3172_);
return v___x_3191_;
}
}
else
{
size_t v___x_3192_; size_t v___x_3193_; lean_object* v___x_3194_; 
v___x_3192_ = ((size_t)0ULL);
v___x_3193_ = lean_usize_of_nat(v___x_3186_);
v___x_3194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_3184_, v___x_3192_, v___x_3193_, v_x_3172_);
return v___x_3194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(lean_object* v_as_3195_, size_t v_i_3196_, size_t v_stop_3197_, lean_object* v_b_3198_){
_start:
{
uint8_t v___x_3199_; 
v___x_3199_ = lean_usize_dec_eq(v_i_3196_, v_stop_3197_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; lean_object* v___x_3201_; size_t v___x_3202_; size_t v___x_3203_; 
v___x_3200_ = lean_array_uget_borrowed(v_as_3195_, v_i_3196_);
v___x_3201_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(v___x_3200_, v_b_3198_);
v___x_3202_ = ((size_t)1ULL);
v___x_3203_ = lean_usize_add(v_i_3196_, v___x_3202_);
v_i_3196_ = v___x_3203_;
v_b_3198_ = v___x_3201_;
goto _start;
}
else
{
return v_b_3198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35___boxed(lean_object* v_as_3205_, lean_object* v_i_3206_, lean_object* v_stop_3207_, lean_object* v_b_3208_){
_start:
{
size_t v_i_boxed_3209_; size_t v_stop_boxed_3210_; lean_object* v_res_3211_; 
v_i_boxed_3209_ = lean_unbox_usize(v_i_3206_);
lean_dec(v_i_3206_);
v_stop_boxed_3210_ = lean_unbox_usize(v_stop_3207_);
lean_dec(v_stop_3207_);
v_res_3211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_as_3205_, v_i_boxed_3209_, v_stop_boxed_3210_, v_b_3208_);
lean_dec_ref(v_as_3205_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28___boxed(lean_object* v_x_3212_, lean_object* v_x_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(v_x_3212_, v_x_3213_);
lean_dec_ref(v_x_3212_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(lean_object* v_x_3215_, size_t v_x_3216_, size_t v_x_3217_, lean_object* v_x_3218_){
_start:
{
if (lean_obj_tag(v_x_3215_) == 0)
{
lean_object* v_cs_3219_; lean_object* v___x_3220_; size_t v___x_3221_; lean_object* v_j_3222_; lean_object* v___x_3223_; size_t v___x_3224_; size_t v___x_3225_; size_t v___x_3226_; size_t v___x_3227_; size_t v___x_3228_; size_t v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; 
v_cs_3219_ = lean_ctor_get(v_x_3215_, 0);
v___x_3220_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0);
v___x_3221_ = lean_usize_shift_right(v_x_3216_, v_x_3217_);
v_j_3222_ = lean_usize_to_nat(v___x_3221_);
v___x_3223_ = lean_array_get_borrowed(v___x_3220_, v_cs_3219_, v_j_3222_);
v___x_3224_ = ((size_t)1ULL);
v___x_3225_ = lean_usize_shift_left(v___x_3224_, v_x_3217_);
v___x_3226_ = lean_usize_sub(v___x_3225_, v___x_3224_);
v___x_3227_ = lean_usize_land(v_x_3216_, v___x_3226_);
v___x_3228_ = ((size_t)5ULL);
v___x_3229_ = lean_usize_sub(v_x_3217_, v___x_3228_);
v___x_3230_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(v___x_3223_, v___x_3227_, v___x_3229_, v_x_3218_);
v___x_3231_ = lean_unsigned_to_nat(1u);
v___x_3232_ = lean_nat_add(v_j_3222_, v___x_3231_);
lean_dec(v_j_3222_);
v___x_3233_ = lean_array_get_size(v_cs_3219_);
v___x_3234_ = lean_nat_dec_lt(v___x_3232_, v___x_3233_);
if (v___x_3234_ == 0)
{
lean_dec(v___x_3232_);
return v___x_3230_;
}
else
{
uint8_t v___x_3235_; 
v___x_3235_ = lean_nat_dec_le(v___x_3233_, v___x_3233_);
if (v___x_3235_ == 0)
{
if (v___x_3234_ == 0)
{
lean_dec(v___x_3232_);
return v___x_3230_;
}
else
{
size_t v___x_3236_; size_t v___x_3237_; lean_object* v___x_3238_; 
v___x_3236_ = lean_usize_of_nat(v___x_3232_);
lean_dec(v___x_3232_);
v___x_3237_ = lean_usize_of_nat(v___x_3233_);
v___x_3238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_cs_3219_, v___x_3236_, v___x_3237_, v___x_3230_);
return v___x_3238_;
}
}
else
{
size_t v___x_3239_; size_t v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = lean_usize_of_nat(v___x_3232_);
lean_dec(v___x_3232_);
v___x_3240_ = lean_usize_of_nat(v___x_3233_);
v___x_3241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_cs_3219_, v___x_3239_, v___x_3240_, v___x_3230_);
return v___x_3241_;
}
}
}
else
{
lean_object* v_vs_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; uint8_t v___x_3245_; 
v_vs_3242_ = lean_ctor_get(v_x_3215_, 0);
v___x_3243_ = lean_usize_to_nat(v_x_3216_);
v___x_3244_ = lean_array_get_size(v_vs_3242_);
v___x_3245_ = lean_nat_dec_lt(v___x_3243_, v___x_3244_);
if (v___x_3245_ == 0)
{
lean_dec(v___x_3243_);
return v_x_3218_;
}
else
{
uint8_t v___x_3246_; 
v___x_3246_ = lean_nat_dec_le(v___x_3244_, v___x_3244_);
if (v___x_3246_ == 0)
{
if (v___x_3245_ == 0)
{
lean_dec(v___x_3243_);
return v_x_3218_;
}
else
{
size_t v___x_3247_; size_t v___x_3248_; lean_object* v___x_3249_; 
v___x_3247_ = lean_usize_of_nat(v___x_3243_);
lean_dec(v___x_3243_);
v___x_3248_ = lean_usize_of_nat(v___x_3244_);
v___x_3249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_3242_, v___x_3247_, v___x_3248_, v_x_3218_);
return v___x_3249_;
}
}
else
{
size_t v___x_3250_; size_t v___x_3251_; lean_object* v___x_3252_; 
v___x_3250_ = lean_usize_of_nat(v___x_3243_);
lean_dec(v___x_3243_);
v___x_3251_ = lean_usize_of_nat(v___x_3244_);
v___x_3252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_3242_, v___x_3250_, v___x_3251_, v_x_3218_);
return v___x_3252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26___boxed(lean_object* v_x_3253_, lean_object* v_x_3254_, lean_object* v_x_3255_, lean_object* v_x_3256_){
_start:
{
size_t v_x_92865__boxed_3257_; size_t v_x_92866__boxed_3258_; lean_object* v_res_3259_; 
v_x_92865__boxed_3257_ = lean_unbox_usize(v_x_3254_);
lean_dec(v_x_3254_);
v_x_92866__boxed_3258_ = lean_unbox_usize(v_x_3255_);
lean_dec(v_x_3255_);
v_res_3259_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(v_x_3253_, v_x_92865__boxed_3257_, v_x_92866__boxed_3258_, v_x_3256_);
lean_dec_ref(v_x_3253_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(lean_object* v_t_3260_, lean_object* v_init_3261_, lean_object* v_start_3262_){
_start:
{
lean_object* v___x_3263_; uint8_t v___x_3264_; 
v___x_3263_ = lean_unsigned_to_nat(0u);
v___x_3264_ = lean_nat_dec_eq(v_start_3262_, v___x_3263_);
if (v___x_3264_ == 0)
{
lean_object* v_root_3265_; lean_object* v_tail_3266_; size_t v_shift_3267_; lean_object* v_tailOff_3268_; uint8_t v___x_3269_; 
v_root_3265_ = lean_ctor_get(v_t_3260_, 0);
v_tail_3266_ = lean_ctor_get(v_t_3260_, 1);
v_shift_3267_ = lean_ctor_get_usize(v_t_3260_, 4);
v_tailOff_3268_ = lean_ctor_get(v_t_3260_, 3);
v___x_3269_ = lean_nat_dec_le(v_tailOff_3268_, v_start_3262_);
if (v___x_3269_ == 0)
{
size_t v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; uint8_t v___x_3273_; 
v___x_3270_ = lean_usize_of_nat(v_start_3262_);
v___x_3271_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(v_root_3265_, v___x_3270_, v_shift_3267_, v_init_3261_);
v___x_3272_ = lean_array_get_size(v_tail_3266_);
v___x_3273_ = lean_nat_dec_lt(v___x_3263_, v___x_3272_);
if (v___x_3273_ == 0)
{
return v___x_3271_;
}
else
{
uint8_t v___x_3274_; 
v___x_3274_ = lean_nat_dec_le(v___x_3272_, v___x_3272_);
if (v___x_3274_ == 0)
{
if (v___x_3273_ == 0)
{
return v___x_3271_;
}
else
{
size_t v___x_3275_; size_t v___x_3276_; lean_object* v___x_3277_; 
v___x_3275_ = ((size_t)0ULL);
v___x_3276_ = lean_usize_of_nat(v___x_3272_);
v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3266_, v___x_3275_, v___x_3276_, v___x_3271_);
return v___x_3277_;
}
}
else
{
size_t v___x_3278_; size_t v___x_3279_; lean_object* v___x_3280_; 
v___x_3278_ = ((size_t)0ULL);
v___x_3279_ = lean_usize_of_nat(v___x_3272_);
v___x_3280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3266_, v___x_3278_, v___x_3279_, v___x_3271_);
return v___x_3280_;
}
}
}
else
{
lean_object* v___x_3281_; lean_object* v___x_3282_; uint8_t v___x_3283_; 
v___x_3281_ = lean_nat_sub(v_start_3262_, v_tailOff_3268_);
v___x_3282_ = lean_array_get_size(v_tail_3266_);
v___x_3283_ = lean_nat_dec_lt(v___x_3281_, v___x_3282_);
if (v___x_3283_ == 0)
{
lean_dec(v___x_3281_);
return v_init_3261_;
}
else
{
uint8_t v___x_3284_; 
v___x_3284_ = lean_nat_dec_le(v___x_3282_, v___x_3282_);
if (v___x_3284_ == 0)
{
if (v___x_3283_ == 0)
{
lean_dec(v___x_3281_);
return v_init_3261_;
}
else
{
size_t v___x_3285_; size_t v___x_3286_; lean_object* v___x_3287_; 
v___x_3285_ = lean_usize_of_nat(v___x_3281_);
lean_dec(v___x_3281_);
v___x_3286_ = lean_usize_of_nat(v___x_3282_);
v___x_3287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3266_, v___x_3285_, v___x_3286_, v_init_3261_);
return v___x_3287_;
}
}
else
{
size_t v___x_3288_; size_t v___x_3289_; lean_object* v___x_3290_; 
v___x_3288_ = lean_usize_of_nat(v___x_3281_);
lean_dec(v___x_3281_);
v___x_3289_ = lean_usize_of_nat(v___x_3282_);
v___x_3290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3266_, v___x_3288_, v___x_3289_, v_init_3261_);
return v___x_3290_;
}
}
}
}
else
{
lean_object* v_root_3291_; lean_object* v_tail_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; uint8_t v___x_3295_; 
v_root_3291_ = lean_ctor_get(v_t_3260_, 0);
v_tail_3292_ = lean_ctor_get(v_t_3260_, 1);
v___x_3293_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(v_root_3291_, v_init_3261_);
v___x_3294_ = lean_array_get_size(v_tail_3292_);
v___x_3295_ = lean_nat_dec_lt(v___x_3263_, v___x_3294_);
if (v___x_3295_ == 0)
{
return v___x_3293_;
}
else
{
uint8_t v___x_3296_; 
v___x_3296_ = lean_nat_dec_le(v___x_3294_, v___x_3294_);
if (v___x_3296_ == 0)
{
if (v___x_3295_ == 0)
{
return v___x_3293_;
}
else
{
size_t v___x_3297_; size_t v___x_3298_; lean_object* v___x_3299_; 
v___x_3297_ = ((size_t)0ULL);
v___x_3298_ = lean_usize_of_nat(v___x_3294_);
v___x_3299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3292_, v___x_3297_, v___x_3298_, v___x_3293_);
return v___x_3299_;
}
}
else
{
size_t v___x_3300_; size_t v___x_3301_; lean_object* v___x_3302_; 
v___x_3300_ = ((size_t)0ULL);
v___x_3301_ = lean_usize_of_nat(v___x_3294_);
v___x_3302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3292_, v___x_3300_, v___x_3301_, v___x_3293_);
return v___x_3302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9___boxed(lean_object* v_t_3303_, lean_object* v_init_3304_, lean_object* v_start_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v_t_3303_, v_init_3304_, v_start_3305_);
lean_dec(v_start_3305_);
lean_dec_ref(v_t_3303_);
return v_res_3306_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6));
v___x_3324_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8));
v___x_3325_ = l_Lean_Name_append(v___x_3324_, v___x_3323_);
return v___x_3325_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11(void){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10));
v___x_3328_ = l_Lean_stringToMessageData(v___x_3327_);
return v___x_3328_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13(void){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12));
v___x_3331_ = l_Lean_stringToMessageData(v___x_3330_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
lean_object* v___x_3343_; 
v___x_3343_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3332_, v_a_3340_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3438_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3346_ = v___x_3343_;
v_isShared_3347_ = v_isSharedCheck_3438_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3343_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3438_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v_vars_3348_; lean_object* v_vars_x27_3349_; lean_object* v_dvds_3350_; lean_object* v_lowers_3351_; lean_object* v_uppers_3352_; lean_object* v_diseqs_3353_; uint8_t v___x_3354_; 
v_vars_3348_ = lean_ctor_get(v_a_3344_, 0);
lean_inc_ref(v_vars_3348_);
v_vars_x27_3349_ = lean_ctor_get(v_a_3344_, 2);
lean_inc_ref(v_vars_x27_3349_);
v_dvds_3350_ = lean_ctor_get(v_a_3344_, 6);
lean_inc_ref(v_dvds_3350_);
v_lowers_3351_ = lean_ctor_get(v_a_3344_, 7);
lean_inc_ref(v_lowers_3351_);
v_uppers_3352_ = lean_ctor_get(v_a_3344_, 8);
lean_inc_ref(v_uppers_3352_);
v_diseqs_3353_ = lean_ctor_get(v_a_3344_, 9);
lean_inc_ref(v_diseqs_3353_);
lean_dec(v_a_3344_);
v___x_3354_ = l_Lean_PersistentArray_isEmpty___redArg(v_vars_3348_);
lean_dec_ref(v_vars_3348_);
if (v___x_3354_ == 0)
{
uint8_t v___x_3355_; 
v___x_3355_ = l_Lean_PersistentArray_isEmpty___redArg(v_vars_x27_3349_);
lean_dec_ref(v_vars_x27_3349_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; lean_object* v___x_3358_; 
lean_dec_ref(v_diseqs_3353_);
lean_dec_ref(v_uppers_3352_);
lean_dec_ref(v_lowers_3351_);
lean_dec_ref(v_dvds_3350_);
v___x_3356_ = lean_box(0);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3356_);
v___x_3358_ = v___x_3346_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
else
{
lean_object* v___x_3360_; 
lean_del_object(v___x_3346_);
v___x_3360_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v___x_3361_; 
lean_dec_ref(v___x_3360_);
v___x_3361_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3363_; lean_object* v___f_3364_; lean_object* v___f_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc_n(v_a_3362_, 2);
lean_dec_ref(v___x_3361_);
v___x_3363_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_a_3362_);
lean_inc_ref_n(v___x_3363_, 2);
v___f_3364_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3364_, 0, v___x_3363_);
v___f_3365_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3365_, 0, v_a_3362_);
lean_closure_set(v___f_3365_, 1, v___f_3364_);
lean_closure_set(v___f_3365_, 2, v___x_3363_);
v___x_3366_ = lean_unsigned_to_nat(0u);
v___x_3367_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0));
v___x_3368_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(v_dvds_3350_, v___x_3367_, v___x_3366_);
lean_dec_ref(v_dvds_3350_);
v___x_3369_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_lowers_3351_, v___x_3367_, v___x_3366_);
lean_dec_ref(v_lowers_3351_);
v___x_3370_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3371_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3370_, v___f_3365_, v_a_3332_);
if (lean_obj_tag(v___x_3371_) == 0)
{
size_t v_sz_3372_; size_t v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; size_t v_sz_3376_; lean_object* v___x_3377_; 
lean_dec_ref(v___x_3371_);
v_sz_3372_ = lean_array_size(v___x_3368_);
v___x_3373_ = ((size_t)0ULL);
v___x_3374_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v___x_3363_, v_sz_3372_, v___x_3373_, v___x_3368_);
v___x_3375_ = lean_box(0);
v_sz_3376_ = lean_array_size(v___x_3374_);
v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v___x_3374_, v_sz_3376_, v___x_3373_, v___x_3375_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
lean_dec_ref(v___x_3374_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v___x_3378_; size_t v_sz_3379_; lean_object* v___x_3380_; size_t v_sz_3381_; lean_object* v___x_3382_; 
lean_dec_ref(v___x_3377_);
v___x_3378_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_uppers_3352_, v___x_3369_, v___x_3366_);
lean_dec_ref(v_uppers_3352_);
v_sz_3379_ = lean_array_size(v___x_3378_);
v___x_3380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v___x_3363_, v_sz_3379_, v___x_3373_, v___x_3378_);
v_sz_3381_ = lean_array_size(v___x_3380_);
v___x_3382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v___x_3380_, v_sz_3381_, v___x_3373_, v___x_3375_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
lean_dec_ref(v___x_3380_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v___x_3383_; size_t v_sz_3384_; lean_object* v___x_3385_; size_t v_sz_3386_; lean_object* v___x_3387_; 
lean_dec_ref(v___x_3382_);
v___x_3383_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v_diseqs_3353_, v___x_3367_, v___x_3366_);
lean_dec_ref(v_diseqs_3353_);
v_sz_3384_ = lean_array_size(v___x_3383_);
v___x_3385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v___x_3363_, v_sz_3384_, v___x_3373_, v___x_3383_);
v_sz_3386_ = lean_array_size(v___x_3385_);
v___x_3387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v___x_3385_, v_sz_3386_, v___x_3373_, v___x_3375_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
lean_dec_ref(v___x_3385_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_options_3388_; uint8_t v_hasTrace_3389_; 
lean_dec_ref(v___x_3387_);
v_options_3388_ = lean_ctor_get(v_a_3340_, 2);
v_hasTrace_3389_ = lean_ctor_get_uint8(v_options_3388_, sizeof(void*)*1);
if (v_hasTrace_3389_ == 0)
{
lean_object* v___x_3390_; 
lean_dec_ref(v___x_3363_);
lean_dec(v_a_3362_);
v___x_3390_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
return v___x_3390_;
}
else
{
lean_object* v_inheritedTraceOptions_3391_; lean_object* v___x_3392_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v_options_3403_; lean_object* v_inheritedTraceOptions_3404_; lean_object* v___y_3405_; lean_object* v___x_3417_; uint8_t v___x_3418_; 
v_inheritedTraceOptions_3391_ = lean_ctor_get(v_a_3340_, 13);
v___x_3392_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6));
v___x_3417_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9);
v___x_3418_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3391_, v_options_3388_, v___x_3417_);
if (v___x_3418_ == 0)
{
lean_dec(v_a_3362_);
v___y_3394_ = v_a_3332_;
v___y_3395_ = v_a_3333_;
v___y_3396_ = v_a_3334_;
v___y_3397_ = v_a_3335_;
v___y_3398_ = v_a_3336_;
v___y_3399_ = v_a_3337_;
v___y_3400_ = v_a_3338_;
v___y_3401_ = v_a_3339_;
v___y_3402_ = v_a_3340_;
v_options_3403_ = v_options_3388_;
v_inheritedTraceOptions_3404_ = v_inheritedTraceOptions_3391_;
v___y_3405_ = v_a_3341_;
goto v___jp_3393_;
}
else
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3419_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13);
v___x_3420_ = lean_array_to_list(v_a_3362_);
v___x_3421_ = lean_box(0);
v___x_3422_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v___x_3420_, v___x_3421_);
v___x_3423_ = l_Lean_MessageData_ofList(v___x_3422_);
v___x_3424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3419_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(v___x_3392_, v___x_3424_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_dec_ref(v___x_3425_);
v___y_3394_ = v_a_3332_;
v___y_3395_ = v_a_3333_;
v___y_3396_ = v_a_3334_;
v___y_3397_ = v_a_3335_;
v___y_3398_ = v_a_3336_;
v___y_3399_ = v_a_3337_;
v___y_3400_ = v_a_3338_;
v___y_3401_ = v_a_3339_;
v___y_3402_ = v_a_3340_;
v_options_3403_ = v_options_3388_;
v_inheritedTraceOptions_3404_ = v_inheritedTraceOptions_3391_;
v___y_3405_ = v_a_3341_;
goto v___jp_3393_;
}
else
{
lean_dec_ref(v___x_3363_);
return v___x_3425_;
}
}
v___jp_3393_:
{
lean_object* v___x_3406_; uint8_t v___x_3407_; 
v___x_3406_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9);
v___x_3407_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3404_, v_options_3403_, v___x_3406_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; 
lean_dec_ref(v___x_3363_);
v___x_3408_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3405_);
return v___x_3408_;
}
else
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3409_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11);
v___x_3410_ = lean_array_to_list(v___x_3363_);
v___x_3411_ = lean_box(0);
v___x_3412_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v___x_3410_, v___x_3411_);
v___x_3413_ = l_Lean_MessageData_ofList(v___x_3412_);
v___x_3414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3409_);
lean_ctor_set(v___x_3414_, 1, v___x_3413_);
v___x_3415_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(v___x_3392_, v___x_3414_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3405_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v___x_3416_; 
lean_dec_ref(v___x_3415_);
v___x_3416_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3405_);
return v___x_3416_;
}
else
{
return v___x_3415_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3363_);
lean_dec(v_a_3362_);
return v___x_3387_;
}
}
else
{
lean_dec_ref(v___x_3363_);
lean_dec(v_a_3362_);
lean_dec_ref(v_diseqs_3353_);
return v___x_3382_;
}
}
else
{
lean_dec_ref(v___x_3369_);
lean_dec_ref(v___x_3363_);
lean_dec(v_a_3362_);
lean_dec_ref(v_diseqs_3353_);
lean_dec_ref(v_uppers_3352_);
return v___x_3377_;
}
}
else
{
lean_dec_ref(v___x_3369_);
lean_dec_ref(v___x_3368_);
lean_dec_ref(v___x_3363_);
lean_dec(v_a_3362_);
lean_dec_ref(v_diseqs_3353_);
lean_dec_ref(v_uppers_3352_);
return v___x_3371_;
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec_ref(v_diseqs_3353_);
lean_dec_ref(v_uppers_3352_);
lean_dec_ref(v_lowers_3351_);
lean_dec_ref(v_dvds_3350_);
v_a_3426_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3361_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3361_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
else
{
lean_dec_ref(v_diseqs_3353_);
lean_dec_ref(v_uppers_3352_);
lean_dec_ref(v_lowers_3351_);
lean_dec_ref(v_dvds_3350_);
return v___x_3360_;
}
}
}
else
{
lean_object* v___x_3434_; lean_object* v___x_3436_; 
lean_dec_ref(v_diseqs_3353_);
lean_dec_ref(v_uppers_3352_);
lean_dec_ref(v_lowers_3351_);
lean_dec_ref(v_dvds_3350_);
lean_dec_ref(v_vars_x27_3349_);
v___x_3434_ = lean_box(0);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3434_);
v___x_3436_ = v___x_3346_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3434_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
v_a_3439_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3343_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3343_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___boxed(lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec_ref(v_a_3453_);
lean_dec(v_a_3452_);
lean_dec_ref(v_a_3451_);
lean_dec(v_a_3450_);
lean_dec_ref(v_a_3449_);
lean_dec(v_a_3448_);
lean_dec(v_a_3447_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(lean_object* v_00_u03b2_3459_, lean_object* v_00_u03c3_3460_, lean_object* v_pm_3461_, lean_object* v_f_3462_){
_start:
{
lean_object* v___x_3463_; 
v___x_3463_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(v_pm_3461_, v_f_3462_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(lean_object* v_cls_3464_, lean_object* v_msg_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
lean_object* v___x_3477_; 
v___x_3477_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(v_cls_3464_, v_msg_3465_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___boxed(lean_object* v_cls_3478_, lean_object* v_msg_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(v_cls_3478_, v_msg_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec(v___y_3480_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0___redArg(lean_object* v_pm_3492_, lean_object* v_f_3493_){
_start:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v_f_3493_, v_pm_3492_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0(lean_object* v_00_u03b2_3495_, lean_object* v_00_u03c3_3496_, lean_object* v_pm_3497_, lean_object* v_f_3498_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v_f_3498_, v_pm_3497_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3500_, lean_object* v_00_u03b2_3501_, lean_object* v_00_u03c3_3502_, lean_object* v_f_3503_, lean_object* v_n_3504_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v_f_3503_, v_n_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20(lean_object* v_00_u03b1_3506_, lean_object* v_00_u03b2_3507_, lean_object* v_00_u03c3_3508_, lean_object* v_f_3509_, size_t v_sz_3510_, size_t v_i_3511_, lean_object* v_bs_3512_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(v_f_3509_, v_sz_3510_, v_i_3511_, v_bs_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___boxed(lean_object* v_00_u03b1_3514_, lean_object* v_00_u03b2_3515_, lean_object* v_00_u03c3_3516_, lean_object* v_f_3517_, lean_object* v_sz_3518_, lean_object* v_i_3519_, lean_object* v_bs_3520_){
_start:
{
size_t v_sz_boxed_3521_; size_t v_i_boxed_3522_; lean_object* v_res_3523_; 
v_sz_boxed_3521_ = lean_unbox_usize(v_sz_3518_);
lean_dec(v_sz_3518_);
v_i_boxed_3522_ = lean_unbox_usize(v_i_3519_);
lean_dec(v_i_3519_);
v_res_3523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20(v_00_u03b1_3514_, v_00_u03b2_3515_, v_00_u03c3_3516_, v_f_3517_, v_sz_boxed_3521_, v_i_boxed_3522_, v_bs_3520_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21(lean_object* v_00_u03b1_3524_, lean_object* v_00_u03b2_3525_, lean_object* v_f_3526_, lean_object* v_as_3527_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(v_f_3526_, v_as_3527_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___boxed(lean_object* v_00_u03b1_3529_, lean_object* v_00_u03b2_3530_, lean_object* v_f_3531_, lean_object* v_as_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21(v_00_u03b1_3529_, v_00_u03b2_3530_, v_f_3531_, v_as_3532_);
lean_dec_ref(v_as_3532_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41(lean_object* v_00_u03b1_3534_, lean_object* v_00_u03b2_3535_, lean_object* v_f_3536_, lean_object* v_as_3537_, lean_object* v_i_3538_, lean_object* v_acc_3539_, lean_object* v_hle_3540_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(v_f_3536_, v_as_3537_, v_i_3538_, v_acc_3539_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___boxed(lean_object* v_00_u03b1_3542_, lean_object* v_00_u03b2_3543_, lean_object* v_f_3544_, lean_object* v_as_3545_, lean_object* v_i_3546_, lean_object* v_acc_3547_, lean_object* v_hle_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41(v_00_u03b1_3542_, v_00_u03b2_3543_, v_f_3544_, v_as_3545_, v_i_3546_, v_acc_3547_, v_hle_3548_);
lean_dec_ref(v_as_3545_);
return v_res_3549_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
