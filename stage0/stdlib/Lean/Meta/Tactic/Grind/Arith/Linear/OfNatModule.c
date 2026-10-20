// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.OfNatModule
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM import Init.Grind.Module.OfNatModule import Init.Grind.Module.NatModuleNorm import Lean.Meta.Tactic.Grind.Diseq import Lean.Meta.Tactic.Grind.Arith.Util import Lean.Meta.Tactic.Grind.Arith.Linear.ToExpr import Init.Data.Nat.Order import Init.Data.Order.Lemmas import Lean.Data.RArray
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_Meta_Grind_mkDiseqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Expr_toPolyN(lean_object*);
uint8_t l_Lean_Grind_Linarith_instBEqPoly_beq(lean_object*, lean_object*);
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RArray_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "`grind` internal error, invalid natStructId"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfNatModuleM_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfNatModuleM = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfNatModuleM_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "expression in two different nat module structures in linarith module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__1_value),LEAN_SCALAR_PTR_LITERAL(172, 37, 33, 120, 251, 36, 203, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__6_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__7_value),LEAN_SCALAR_PTR_LITERAL(23, 127, 6, 115, 121, 139, 223, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__9_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__10_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "IntModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OfNatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__16_value),LEAN_SCALAR_PTR_LITERAL(228, 65, 165, 57, 92, 99, 138, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "smul_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__18_value),LEAN_SCALAR_PTR_LITERAL(76, 96, 205, 43, 14, 83, 20, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toQ_zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__20_value),LEAN_SCALAR_PTR_LITERAL(127, 170, 123, 35, 245, 189, 60, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofNatModule___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Linarith"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "eq_normN"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 207, 141, 119, 115, 174, 198, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(126, 34, 3, 158, 236, 88, 5, 190)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg(lean_object* v_natStructId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc(v_a_3_);
v___x_14_ = lean_apply_12(v_x_2_, v_natStructId_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg___boxed(lean_object* v_natStructId_15_, lean_object* v_x_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg(v_natStructId_15_, v_x_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
lean_dec(v_a_26_);
lean_dec_ref(v_a_25_);
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec(v_a_20_);
lean_dec_ref(v_a_19_);
lean_dec(v_a_18_);
lean_dec(v_a_17_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run(lean_object* v_00_u03b1_29_, lean_object* v_natStructId_30_, lean_object* v_x_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; 
lean_inc(v_a_41_);
lean_inc_ref(v_a_40_);
lean_inc(v_a_39_);
lean_inc_ref(v_a_38_);
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc(v_a_33_);
lean_inc(v_a_32_);
v___x_43_ = lean_apply_12(v_x_31_, v_natStructId_30_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, lean_box(0));
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___boxed(lean_object* v_00_u03b1_44_, lean_object* v_natStructId_45_, lean_object* v_x_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run(v_00_u03b1_44_, v_natStructId_45_, v_x_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec(v_a_47_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg(lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; 
lean_inc(v_a_59_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_a_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg___boxed(lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg(v_a_62_);
lean_dec(v_a_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId(lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
lean_inc(v_a_65_);
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v_a_65_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId___boxed(lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId(v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec(v_a_79_);
lean_dec(v_a_78_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(lean_object* v_msgData_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___x_97_; lean_object* v_env_98_; uint8_t v___x_99_; lean_object* v_env_100_; lean_object* v___x_101_; lean_object* v_toCold_102_; lean_object* v_mctx_103_; lean_object* v_lctx_104_; lean_object* v_options_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_97_ = lean_st_ref_get(v___y_95_);
v_env_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref(v_env_98_);
lean_dec(v___x_97_);
v___x_99_ = 0;
v_env_100_ = l_Lean_Environment_setRecordingDeps(v_env_98_, v___x_99_);
v___x_101_ = lean_st_ref_get(v___y_93_);
v_toCold_102_ = lean_ctor_get(v___y_94_, 0);
v_mctx_103_ = lean_ctor_get(v___x_101_, 0);
lean_inc_ref(v_mctx_103_);
lean_dec(v___x_101_);
v_lctx_104_ = lean_ctor_get(v___y_92_, 2);
v_options_105_ = lean_ctor_get(v_toCold_102_, 2);
lean_inc_ref(v_options_105_);
lean_inc_ref(v_lctx_104_);
v___x_106_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_106_, 0, v_env_100_);
lean_ctor_set(v___x_106_, 1, v_mctx_103_);
lean_ctor_set(v___x_106_, 2, v_lctx_104_);
lean_ctor_set(v___x_106_, 3, v_options_105_);
v___x_107_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v_msgData_91_);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0___boxed(lean_object* v_msgData_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(v_msgData_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(lean_object* v_msg_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_ref_122_; lean_object* v___x_123_; lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_132_; 
v_ref_122_ = lean_ctor_get(v___y_119_, 2);
v___x_123_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(v_msg_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
v_a_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_132_ == 0)
{
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_132_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_132_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
lean_inc(v_ref_122_);
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v_ref_122_);
lean_ctor_set(v___x_128_, 1, v_a_124_);
if (v_isShared_127_ == 0)
{
lean_ctor_set_tag(v___x_126_, 1);
lean_ctor_set(v___x_126_, 0, v___x_128_);
v___x_130_ = v___x_126_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg___boxed(lean_object* v_msg_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(v_msg_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_139_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0));
v___x_142_ = l_Lean_stringToMessageData(v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct(lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_144_, v_a_152_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_169_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_169_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_169_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_169_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v_natStructs_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_natStructs_160_ = lean_ctor_get(v_a_156_, 5);
lean_inc_ref(v_natStructs_160_);
lean_dec(v_a_156_);
v___x_161_ = lean_array_get_size(v_natStructs_160_);
v___x_162_ = lean_nat_dec_lt(v_a_143_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec_ref(v_natStructs_160_);
lean_del_object(v___x_158_);
v___x_163_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1);
v___x_164_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(v___x_163_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_165_ = lean_array_fget(v_natStructs_160_, v_a_143_);
lean_dec_ref(v_natStructs_160_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_165_);
v___x_167_ = v___x_158_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_a_170_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_155_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_155_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct___boxed(lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec(v_a_179_);
lean_dec(v_a_178_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0(lean_object* v_00_u03b1_191_, lean_object* v_msg_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(v_msg_192_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___boxed(lean_object* v_00_u03b1_206_, lean_object* v_msg_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0(v_00_u03b1_206_, v_msg_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec(v___y_209_);
lean_dec(v___y_208_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v_structId_235_; lean_object* v___x_236_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref_known(v___x_233_, 1);
v_structId_235_ = lean_ctor_get(v_a_234_, 1);
lean_inc(v_structId_235_);
lean_dec(v_a_234_);
v___x_236_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_structId_235_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec(v_structId_235_);
return v___x_236_;
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
v_a_237_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_233_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_233_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct___boxed(lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
lean_dec(v_a_247_);
lean_dec(v_a_246_);
lean_dec(v_a_245_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0(lean_object* v_a_259_, lean_object* v_f_260_, lean_object* v_s_261_){
_start:
{
lean_object* v_structs_262_; lean_object* v_typeIdOf_263_; lean_object* v_exprToStructId_264_; lean_object* v_exprToStructIdEntries_265_; lean_object* v_forbiddenNatModules_266_; lean_object* v_natStructs_267_; lean_object* v_natTypeIdOf_268_; lean_object* v_exprToNatStructId_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v_structs_262_ = lean_ctor_get(v_s_261_, 0);
v_typeIdOf_263_ = lean_ctor_get(v_s_261_, 1);
v_exprToStructId_264_ = lean_ctor_get(v_s_261_, 2);
v_exprToStructIdEntries_265_ = lean_ctor_get(v_s_261_, 3);
v_forbiddenNatModules_266_ = lean_ctor_get(v_s_261_, 4);
v_natStructs_267_ = lean_ctor_get(v_s_261_, 5);
v_natTypeIdOf_268_ = lean_ctor_get(v_s_261_, 6);
v_exprToNatStructId_269_ = lean_ctor_get(v_s_261_, 7);
v___x_270_ = lean_array_get_size(v_natStructs_267_);
v___x_271_ = lean_nat_dec_lt(v_a_259_, v___x_270_);
if (v___x_271_ == 0)
{
lean_dec_ref(v_f_260_);
return v_s_261_;
}
else
{
lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_283_; 
lean_inc_ref(v_exprToNatStructId_269_);
lean_inc_ref(v_natTypeIdOf_268_);
lean_inc_ref(v_natStructs_267_);
lean_inc_ref(v_forbiddenNatModules_266_);
lean_inc_ref(v_exprToStructIdEntries_265_);
lean_inc_ref(v_exprToStructId_264_);
lean_inc_ref(v_typeIdOf_263_);
lean_inc_ref(v_structs_262_);
v_isSharedCheck_283_ = !lean_is_exclusive(v_s_261_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; lean_object* v_unused_285_; lean_object* v_unused_286_; lean_object* v_unused_287_; lean_object* v_unused_288_; lean_object* v_unused_289_; lean_object* v_unused_290_; lean_object* v_unused_291_; 
v_unused_284_ = lean_ctor_get(v_s_261_, 7);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_s_261_, 6);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_s_261_, 5);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_s_261_, 4);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v_s_261_, 3);
lean_dec(v_unused_288_);
v_unused_289_ = lean_ctor_get(v_s_261_, 2);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v_s_261_, 1);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_s_261_, 0);
lean_dec(v_unused_291_);
v___x_273_ = v_s_261_;
v_isShared_274_ = v_isSharedCheck_283_;
goto v_resetjp_272_;
}
else
{
lean_dec(v_s_261_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_283_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v_v_275_; lean_object* v___x_276_; lean_object* v_xs_x27_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v_v_275_ = lean_array_fget(v_natStructs_267_, v_a_259_);
v___x_276_ = lean_box(0);
v_xs_x27_277_ = lean_array_fset(v_natStructs_267_, v_a_259_, v___x_276_);
v___x_278_ = lean_apply_1(v_f_260_, v_v_275_);
v___x_279_ = lean_array_fset(v_xs_x27_277_, v_a_259_, v___x_278_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 5, v___x_279_);
v___x_281_ = v___x_273_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_structs_262_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_typeIdOf_263_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_exprToStructId_264_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v_exprToStructIdEntries_265_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v_forbiddenNatModules_266_);
lean_ctor_set(v_reuseFailAlloc_282_, 5, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_282_, 6, v_natTypeIdOf_268_);
lean_ctor_set(v_reuseFailAlloc_282_, 7, v_exprToNatStructId_269_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed(lean_object* v_a_292_, lean_object* v_f_293_, lean_object* v_s_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0(v_a_292_, v_f_293_, v_s_294_);
lean_dec(v_a_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg(lean_object* v_f_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v___f_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
lean_inc(v_a_297_);
v___f_300_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_300_, 0, v_a_297_);
lean_closure_set(v___f_300_, 1, v_f_296_);
v___x_301_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_302_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_301_, v___f_300_, v_a_298_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___boxed(lean_object* v_f_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg(v_f_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec(v_a_304_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct(lean_object* v_f_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___f_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
lean_inc(v_a_309_);
v___f_321_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_321_, 0, v_a_309_);
lean_closure_set(v___f_321_, 1, v_f_308_);
v___x_322_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_323_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_322_, v___f_321_, v_a_310_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___boxed(lean_object* v_f_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct(v_f_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec(v_a_326_);
lean_dec(v_a_325_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_338_, lean_object* v_vals_339_, lean_object* v_i_340_, lean_object* v_k_341_){
_start:
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = lean_array_get_size(v_keys_338_);
v___x_343_ = lean_nat_dec_lt(v_i_340_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
lean_dec(v_i_340_);
v___x_344_ = lean_box(0);
return v___x_344_;
}
else
{
lean_object* v_k_x27_345_; size_t v___x_346_; size_t v___x_347_; uint8_t v___x_348_; 
v_k_x27_345_ = lean_array_fget_borrowed(v_keys_338_, v_i_340_);
v___x_346_ = lean_ptr_addr(v_k_341_);
v___x_347_ = lean_ptr_addr(v_k_x27_345_);
v___x_348_ = lean_usize_dec_eq(v___x_346_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = lean_nat_add(v_i_340_, v___x_349_);
lean_dec(v_i_340_);
v_i_340_ = v___x_350_;
goto _start;
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_array_fget_borrowed(v_vals_339_, v_i_340_);
lean_dec(v_i_340_);
lean_inc(v___x_352_);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_354_, lean_object* v_vals_355_, lean_object* v_i_356_, lean_object* v_k_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_354_, v_vals_355_, v_i_356_, v_k_357_);
lean_dec_ref(v_k_357_);
lean_dec_ref(v_vals_355_);
lean_dec_ref(v_keys_354_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_359_, size_t v_x_360_, lean_object* v_x_361_){
_start:
{
if (lean_obj_tag(v_x_359_) == 0)
{
lean_object* v_es_362_; lean_object* v___x_363_; size_t v___x_364_; size_t v___x_365_; lean_object* v_j_366_; lean_object* v___x_367_; 
v_es_362_ = lean_ctor_get(v_x_359_, 0);
v___x_363_ = lean_box(2);
v___x_364_ = ((size_t)31ULL);
v___x_365_ = lean_usize_land(v_x_360_, v___x_364_);
v_j_366_ = lean_usize_to_nat(v___x_365_);
v___x_367_ = lean_array_get_borrowed(v___x_363_, v_es_362_, v_j_366_);
lean_dec(v_j_366_);
switch(lean_obj_tag(v___x_367_))
{
case 0:
{
lean_object* v_key_368_; lean_object* v_val_369_; size_t v___x_370_; size_t v___x_371_; uint8_t v___x_372_; 
v_key_368_ = lean_ctor_get(v___x_367_, 0);
v_val_369_ = lean_ctor_get(v___x_367_, 1);
v___x_370_ = lean_ptr_addr(v_x_361_);
v___x_371_ = lean_ptr_addr(v_key_368_);
v___x_372_ = lean_usize_dec_eq(v___x_370_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; 
v___x_373_ = lean_box(0);
return v___x_373_;
}
else
{
lean_object* v___x_374_; 
lean_inc(v_val_369_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v_val_369_);
return v___x_374_;
}
}
case 1:
{
lean_object* v_node_375_; size_t v___x_376_; size_t v___x_377_; 
v_node_375_ = lean_ctor_get(v___x_367_, 0);
v___x_376_ = ((size_t)5ULL);
v___x_377_ = lean_usize_shift_right(v_x_360_, v___x_376_);
v_x_359_ = v_node_375_;
v_x_360_ = v___x_377_;
goto _start;
}
default: 
{
lean_object* v___x_379_; 
v___x_379_ = lean_box(0);
return v___x_379_;
}
}
}
else
{
lean_object* v_ks_380_; lean_object* v_vs_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_ks_380_ = lean_ctor_get(v_x_359_, 0);
v_vs_381_ = lean_ctor_get(v_x_359_, 1);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_380_, v_vs_381_, v___x_382_, v_x_361_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
size_t v_x_905__boxed_387_; lean_object* v_res_388_; 
v_x_905__boxed_387_ = lean_unbox_usize(v_x_385_);
lean_dec(v_x_385_);
v_res_388_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_384_, v_x_905__boxed_387_, v_x_386_);
lean_dec_ref(v_x_386_);
lean_dec_ref(v_x_384_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(lean_object* v_x_389_, lean_object* v_x_390_){
_start:
{
size_t v___x_391_; size_t v___x_392_; size_t v___x_393_; uint64_t v___x_394_; size_t v___x_395_; lean_object* v___x_396_; 
v___x_391_ = lean_ptr_addr(v_x_390_);
v___x_392_ = ((size_t)3ULL);
v___x_393_ = lean_usize_shift_right(v___x_391_, v___x_392_);
v___x_394_ = lean_usize_to_uint64(v___x_393_);
v___x_395_ = lean_uint64_to_usize(v___x_394_);
v___x_396_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_389_, v___x_395_, v_x_390_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_x_397_, v_x_398_);
lean_dec_ref(v_x_398_);
lean_dec_ref(v_x_397_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(lean_object* v_e_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_401_, v_a_402_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_414_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_414_ == 0)
{
v___x_407_ = v___x_404_;
v_isShared_408_ = v_isSharedCheck_414_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_404_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_414_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v_exprToNatStructId_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
v_exprToNatStructId_409_ = lean_ctor_get(v_a_405_, 7);
lean_inc_ref(v_exprToNatStructId_409_);
lean_dec(v_a_405_);
v___x_410_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_exprToNatStructId_409_, v_e_400_);
lean_dec_ref(v_exprToNatStructId_409_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_410_);
v___x_412_ = v___x_407_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
v_a_415_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_404_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_404_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
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
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg___boxed(lean_object* v_e_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_e_423_, v_a_424_, v_a_425_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_e_423_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f(lean_object* v_e_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_e_428_, v_a_429_, v_a_437_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___boxed(lean_object* v_e_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f(v_e_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_e_441_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0(lean_object* v_00_u03b2_454_, lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_x_455_, v_x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0(v_00_u03b2_458_, v_x_459_, v_x_460_);
lean_dec_ref(v_x_460_);
lean_dec_ref(v_x_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_462_, lean_object* v_x_463_, size_t v_x_464_, lean_object* v_x_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_463_, v_x_464_, v_x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_467_, lean_object* v_x_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
size_t v_x_1026__boxed_471_; lean_object* v_res_472_; 
v_x_1026__boxed_471_ = lean_unbox_usize(v_x_469_);
lean_dec(v_x_469_);
v_res_472_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0(v_00_u03b2_467_, v_x_468_, v_x_1026__boxed_471_, v_x_470_);
lean_dec_ref(v_x_470_);
lean_dec_ref(v_x_468_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_473_, lean_object* v_keys_474_, lean_object* v_vals_475_, lean_object* v_heq_476_, lean_object* v_i_477_, lean_object* v_k_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_474_, v_vals_475_, v_i_477_, v_k_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_480_, lean_object* v_keys_481_, lean_object* v_vals_482_, lean_object* v_heq_483_, lean_object* v_i_484_, lean_object* v_k_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_480_, v_keys_481_, v_vals_482_, v_heq_483_, v_i_484_, v_k_485_);
lean_dec_ref(v_k_485_);
lean_dec_ref(v_vals_482_);
lean_dec_ref(v_keys_481_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(lean_object* v_a_487_, lean_object* v_b_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_a_487_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_521_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_521_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_521_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_521_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
if (lean_obj_tag(v_a_493_) == 1)
{
lean_object* v_val_497_; lean_object* v___x_498_; 
lean_del_object(v___x_495_);
v_val_497_ = lean_ctor_get(v_a_493_, 0);
v___x_498_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_b_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_516_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_516_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_516_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_516_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
if (lean_obj_tag(v_a_499_) == 1)
{
lean_object* v_val_503_; uint8_t v___x_504_; 
v_val_503_ = lean_ctor_get(v_a_499_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v_a_499_, 1);
v___x_504_ = lean_nat_dec_eq(v_val_497_, v_val_503_);
lean_dec(v_val_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_507_; 
lean_dec_ref_known(v_a_493_, 1);
v___x_505_ = lean_box(0);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_505_);
v___x_507_ = v___x_501_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
else
{
lean_object* v___x_510_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v_a_493_);
v___x_510_ = v___x_501_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_493_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
lean_object* v___x_512_; lean_object* v___x_514_; 
lean_dec(v_a_499_);
lean_dec_ref_known(v_a_493_, 1);
v___x_512_ = lean_box(0);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_512_);
v___x_514_ = v___x_501_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_493_, 1);
return v___x_498_;
}
}
else
{
lean_object* v___x_517_; lean_object* v___x_519_; 
lean_dec(v_a_493_);
v___x_517_ = lean_box(0);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_517_);
v___x_519_ = v___x_495_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
else
{
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg___boxed(lean_object* v_a_522_, lean_object* v_b_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_522_, v_b_523_, v_a_524_, v_a_525_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_b_523_);
lean_dec_ref(v_a_522_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f(lean_object* v_a_528_, lean_object* v_b_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_528_, v_b_529_, v_a_530_, v_a_538_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___boxed(lean_object* v_a_542_, lean_object* v_b_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f(v_a_542_, v_b_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_b_543_);
lean_dec_ref(v_a_542_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_556_, lean_object* v_x_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v_ks_560_; lean_object* v_vs_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_587_; 
v_ks_560_ = lean_ctor_get(v_x_556_, 0);
v_vs_561_ = lean_ctor_get(v_x_556_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_x_556_);
if (v_isSharedCheck_587_ == 0)
{
v___x_563_ = v_x_556_;
v_isShared_564_ = v_isSharedCheck_587_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_vs_561_);
lean_inc(v_ks_560_);
lean_dec(v_x_556_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_587_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_array_get_size(v_ks_560_);
v___x_566_ = lean_nat_dec_lt(v_x_557_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
lean_dec(v_x_557_);
v___x_567_ = lean_array_push(v_ks_560_, v_x_558_);
v___x_568_ = lean_array_push(v_vs_561_, v_x_559_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___x_568_);
lean_ctor_set(v___x_563_, 0, v___x_567_);
v___x_570_ = v___x_563_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
else
{
lean_object* v_k_x27_572_; size_t v___x_573_; size_t v___x_574_; uint8_t v___x_575_; 
v_k_x27_572_ = lean_array_fget_borrowed(v_ks_560_, v_x_557_);
v___x_573_ = lean_ptr_addr(v_x_558_);
v___x_574_ = lean_ptr_addr(v_k_x27_572_);
v___x_575_ = lean_usize_dec_eq(v___x_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_577_; 
if (v_isShared_564_ == 0)
{
v___x_577_ = v___x_563_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_ks_560_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_vs_561_);
v___x_577_ = v_reuseFailAlloc_581_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_add(v_x_557_, v___x_578_);
lean_dec(v_x_557_);
v_x_556_ = v___x_577_;
v_x_557_ = v___x_579_;
goto _start;
}
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_582_ = lean_array_fset(v_ks_560_, v_x_557_, v_x_558_);
v___x_583_ = lean_array_fset(v_vs_561_, v_x_557_, v_x_559_);
lean_dec(v_x_557_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___x_583_);
lean_ctor_set(v___x_563_, 0, v___x_582_);
v___x_585_ = v___x_563_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_588_, lean_object* v_k_589_, lean_object* v_v_590_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_588_, v___x_591_, v_k_589_, v_v_590_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(lean_object* v_x_594_, size_t v_x_595_, size_t v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
lean_object* v_es_599_; size_t v___x_600_; size_t v___x_601_; lean_object* v_j_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_es_599_ = lean_ctor_get(v_x_594_, 0);
v___x_600_ = ((size_t)31ULL);
v___x_601_ = lean_usize_land(v_x_595_, v___x_600_);
v_j_602_ = lean_usize_to_nat(v___x_601_);
v___x_603_ = lean_array_get_size(v_es_599_);
v___x_604_ = lean_nat_dec_lt(v_j_602_, v___x_603_);
if (v___x_604_ == 0)
{
lean_dec(v_j_602_);
lean_dec(v_x_598_);
lean_dec_ref(v_x_597_);
return v_x_594_;
}
else
{
lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_645_; 
lean_inc_ref(v_es_599_);
v_isSharedCheck_645_ = !lean_is_exclusive(v_x_594_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v_x_594_, 0);
lean_dec(v_unused_646_);
v___x_606_ = v_x_594_;
v_isShared_607_ = v_isSharedCheck_645_;
goto v_resetjp_605_;
}
else
{
lean_dec(v_x_594_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_645_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v_v_608_; lean_object* v___x_609_; lean_object* v_xs_x27_610_; lean_object* v___y_612_; 
v_v_608_ = lean_array_fget(v_es_599_, v_j_602_);
v___x_609_ = lean_box(0);
v_xs_x27_610_ = lean_array_fset(v_es_599_, v_j_602_, v___x_609_);
switch(lean_obj_tag(v_v_608_))
{
case 0:
{
lean_object* v_key_617_; lean_object* v_val_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_630_; 
v_key_617_ = lean_ctor_get(v_v_608_, 0);
v_val_618_ = lean_ctor_get(v_v_608_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v_v_608_);
if (v_isSharedCheck_630_ == 0)
{
v___x_620_ = v_v_608_;
v_isShared_621_ = v_isSharedCheck_630_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_val_618_);
lean_inc(v_key_617_);
lean_dec(v_v_608_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_630_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
size_t v___x_622_; size_t v___x_623_; uint8_t v___x_624_; 
v___x_622_ = lean_ptr_addr(v_x_597_);
v___x_623_ = lean_ptr_addr(v_key_617_);
v___x_624_ = lean_usize_dec_eq(v___x_622_, v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_del_object(v___x_620_);
v___x_625_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_617_, v_val_618_, v_x_597_, v_x_598_);
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
v___y_612_ = v___x_626_;
goto v___jp_611_;
}
else
{
lean_object* v___x_628_; 
lean_dec(v_val_618_);
lean_dec(v_key_617_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 1, v_x_598_);
lean_ctor_set(v___x_620_, 0, v_x_597_);
v___x_628_ = v___x_620_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_x_597_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_x_598_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
v___y_612_ = v___x_628_;
goto v___jp_611_;
}
}
}
}
case 1:
{
lean_object* v_node_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_643_; 
v_node_631_ = lean_ctor_get(v_v_608_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v_v_608_);
if (v_isSharedCheck_643_ == 0)
{
v___x_633_ = v_v_608_;
v_isShared_634_ = v_isSharedCheck_643_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_node_631_);
lean_dec(v_v_608_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_643_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
size_t v___x_635_; size_t v___x_636_; size_t v___x_637_; size_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_635_ = ((size_t)5ULL);
v___x_636_ = lean_usize_shift_right(v_x_595_, v___x_635_);
v___x_637_ = ((size_t)1ULL);
v___x_638_ = lean_usize_add(v_x_596_, v___x_637_);
v___x_639_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_node_631_, v___x_636_, v___x_638_, v_x_597_, v_x_598_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_639_);
v___x_641_ = v___x_633_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
v___y_612_ = v___x_641_;
goto v___jp_611_;
}
}
}
default: 
{
lean_object* v___x_644_; 
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v_x_597_);
lean_ctor_set(v___x_644_, 1, v_x_598_);
v___y_612_ = v___x_644_;
goto v___jp_611_;
}
}
v___jp_611_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = lean_array_fset(v_xs_x27_610_, v_j_602_, v___y_612_);
lean_dec(v_j_602_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_613_);
v___x_615_ = v___x_606_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
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
}
else
{
lean_object* v_ks_647_; lean_object* v_vs_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_666_; 
v_ks_647_ = lean_ctor_get(v_x_594_, 0);
v_vs_648_ = lean_ctor_get(v_x_594_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_x_594_);
if (v_isSharedCheck_666_ == 0)
{
v___x_650_ = v_x_594_;
v_isShared_651_ = v_isSharedCheck_666_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_vs_648_);
lean_inc(v_ks_647_);
lean_dec(v_x_594_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_666_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_ks_647_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_vs_648_);
v___x_653_ = v_reuseFailAlloc_665_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v_newNode_654_; size_t v___x_655_; uint8_t v___x_656_; 
v_newNode_654_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(v___x_653_, v_x_597_, v_x_598_);
v___x_655_ = ((size_t)7ULL);
v___x_656_ = lean_usize_dec_le(v___x_655_, v_x_596_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_657_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_654_);
v___x_658_ = lean_unsigned_to_nat(4u);
v___x_659_ = lean_nat_dec_lt(v___x_657_, v___x_658_);
lean_dec(v___x_657_);
if (v___x_659_ == 0)
{
lean_object* v_ks_660_; lean_object* v_vs_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_ks_660_ = lean_ctor_get(v_newNode_654_, 0);
lean_inc_ref(v_ks_660_);
v_vs_661_ = lean_ctor_get(v_newNode_654_, 1);
lean_inc_ref(v_vs_661_);
lean_dec_ref(v_newNode_654_);
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0);
v___x_664_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_x_596_, v_ks_660_, v_vs_661_, v___x_662_, v___x_663_);
lean_dec_ref(v_vs_661_);
lean_dec_ref(v_ks_660_);
return v___x_664_;
}
else
{
return v_newNode_654_;
}
}
else
{
return v_newNode_654_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(size_t v_depth_667_, lean_object* v_keys_668_, lean_object* v_vals_669_, lean_object* v_i_670_, lean_object* v_entries_671_){
_start:
{
lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_672_ = lean_array_get_size(v_keys_668_);
v___x_673_ = lean_nat_dec_lt(v_i_670_, v___x_672_);
if (v___x_673_ == 0)
{
lean_dec(v_i_670_);
return v_entries_671_;
}
else
{
lean_object* v_k_674_; lean_object* v_v_675_; size_t v___x_676_; size_t v___x_677_; size_t v___x_678_; uint64_t v___x_679_; size_t v_h_680_; size_t v___x_681_; lean_object* v___x_682_; size_t v___x_683_; size_t v___x_684_; size_t v___x_685_; size_t v_h_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_k_674_ = lean_array_fget_borrowed(v_keys_668_, v_i_670_);
v_v_675_ = lean_array_fget_borrowed(v_vals_669_, v_i_670_);
v___x_676_ = lean_ptr_addr(v_k_674_);
v___x_677_ = ((size_t)3ULL);
v___x_678_ = lean_usize_shift_right(v___x_676_, v___x_677_);
v___x_679_ = lean_usize_to_uint64(v___x_678_);
v_h_680_ = lean_uint64_to_usize(v___x_679_);
v___x_681_ = ((size_t)5ULL);
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = ((size_t)1ULL);
v___x_684_ = lean_usize_sub(v_depth_667_, v___x_683_);
v___x_685_ = lean_usize_mul(v___x_681_, v___x_684_);
v_h_686_ = lean_usize_shift_right(v_h_680_, v___x_685_);
v___x_687_ = lean_nat_add(v_i_670_, v___x_682_);
lean_dec(v_i_670_);
lean_inc(v_v_675_);
lean_inc(v_k_674_);
v___x_688_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_entries_671_, v_h_686_, v_depth_667_, v_k_674_, v_v_675_);
v_i_670_ = v___x_687_;
v_entries_671_ = v___x_688_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_690_, lean_object* v_keys_691_, lean_object* v_vals_692_, lean_object* v_i_693_, lean_object* v_entries_694_){
_start:
{
size_t v_depth_boxed_695_; lean_object* v_res_696_; 
v_depth_boxed_695_ = lean_unbox_usize(v_depth_690_);
lean_dec(v_depth_690_);
v_res_696_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_695_, v_keys_691_, v_vals_692_, v_i_693_, v_entries_694_);
lean_dec_ref(v_vals_692_);
lean_dec_ref(v_keys_691_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___boxed(lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v_x_699_, lean_object* v_x_700_, lean_object* v_x_701_){
_start:
{
size_t v_x_6361__boxed_702_; size_t v_x_6362__boxed_703_; lean_object* v_res_704_; 
v_x_6361__boxed_702_ = lean_unbox_usize(v_x_698_);
lean_dec(v_x_698_);
v_x_6362__boxed_703_ = lean_unbox_usize(v_x_699_);
lean_dec(v_x_699_);
v_res_704_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_697_, v_x_6361__boxed_702_, v_x_6362__boxed_703_, v_x_700_, v_x_701_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(lean_object* v_x_705_, lean_object* v_x_706_, lean_object* v_x_707_){
_start:
{
size_t v___x_708_; size_t v___x_709_; size_t v___x_710_; uint64_t v___x_711_; size_t v___x_712_; size_t v___x_713_; lean_object* v___x_714_; 
v___x_708_ = lean_ptr_addr(v_x_706_);
v___x_709_ = ((size_t)3ULL);
v___x_710_ = lean_usize_shift_right(v___x_708_, v___x_709_);
v___x_711_ = lean_usize_to_uint64(v___x_710_);
v___x_712_ = lean_uint64_to_usize(v___x_711_);
v___x_713_ = ((size_t)1ULL);
v___x_714_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_705_, v___x_712_, v___x_713_, v_x_706_, v_x_707_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0(lean_object* v_e_715_, lean_object* v_a_716_, lean_object* v_s_717_){
_start:
{
lean_object* v_structs_718_; lean_object* v_typeIdOf_719_; lean_object* v_exprToStructId_720_; lean_object* v_exprToStructIdEntries_721_; lean_object* v_forbiddenNatModules_722_; lean_object* v_natStructs_723_; lean_object* v_natTypeIdOf_724_; lean_object* v_exprToNatStructId_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_733_; 
v_structs_718_ = lean_ctor_get(v_s_717_, 0);
v_typeIdOf_719_ = lean_ctor_get(v_s_717_, 1);
v_exprToStructId_720_ = lean_ctor_get(v_s_717_, 2);
v_exprToStructIdEntries_721_ = lean_ctor_get(v_s_717_, 3);
v_forbiddenNatModules_722_ = lean_ctor_get(v_s_717_, 4);
v_natStructs_723_ = lean_ctor_get(v_s_717_, 5);
v_natTypeIdOf_724_ = lean_ctor_get(v_s_717_, 6);
v_exprToNatStructId_725_ = lean_ctor_get(v_s_717_, 7);
v_isSharedCheck_733_ = !lean_is_exclusive(v_s_717_);
if (v_isSharedCheck_733_ == 0)
{
v___x_727_ = v_s_717_;
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_exprToNatStructId_725_);
lean_inc(v_natTypeIdOf_724_);
lean_inc(v_natStructs_723_);
lean_inc(v_forbiddenNatModules_722_);
lean_inc(v_exprToStructIdEntries_721_);
lean_inc(v_exprToStructId_720_);
lean_inc(v_typeIdOf_719_);
lean_inc(v_structs_718_);
lean_dec(v_s_717_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
lean_inc(v_a_716_);
v___x_729_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_exprToNatStructId_725_, v_e_715_, v_a_716_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 7, v___x_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_structs_718_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_typeIdOf_719_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_exprToStructId_720_);
lean_ctor_set(v_reuseFailAlloc_732_, 3, v_exprToStructIdEntries_721_);
lean_ctor_set(v_reuseFailAlloc_732_, 4, v_forbiddenNatModules_722_);
lean_ctor_set(v_reuseFailAlloc_732_, 5, v_natStructs_723_);
lean_ctor_set(v_reuseFailAlloc_732_, 6, v_natTypeIdOf_724_);
lean_ctor_set(v_reuseFailAlloc_732_, 7, v___x_729_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0___boxed(lean_object* v_e_734_, lean_object* v_a_735_, lean_object* v_s_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0(v_e_734_, v_a_735_, v_s_736_);
lean_dec(v_a_735_);
return v_res_737_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__0));
v___x_740_ = l_Lean_stringToMessageData(v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(lean_object* v_e_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___f_754_; lean_object* v___x_755_; 
lean_inc(v_a_742_);
lean_inc_ref(v_e_741_);
v___f_754_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_754_, 0, v_e_741_);
lean_closure_set(v___f_754_, 1, v_a_742_);
v___x_755_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_e_741_, v_a_743_, v_a_748_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
if (lean_obj_tag(v_a_756_) == 1)
{
lean_object* v_val_757_; uint8_t v___x_758_; 
lean_dec_ref(v___f_754_);
v_val_757_ = lean_ctor_get(v_a_756_, 0);
lean_inc(v_val_757_);
lean_dec_ref_known(v_a_756_, 1);
v___x_758_ = lean_nat_dec_eq(v_val_757_, v_a_742_);
lean_dec(v_val_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_759_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1);
v___x_760_ = l_Lean_indentExpr(v_e_741_);
v___x_761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_759_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_744_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; uint8_t v_verbose_764_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_762_, 1);
v_verbose_764_ = lean_ctor_get_uint8(v_a_763_, 0);
lean_dec(v_a_763_);
if (v_verbose_764_ == 0)
{
lean_dec_ref_known(v___x_761_, 2);
goto v___jp_751_;
}
else
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Meta_Sym_reportIssue(v___x_761_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_dec_ref_known(v___x_765_, 1);
goto v___jp_751_;
}
else
{
return v___x_765_;
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref_known(v___x_761_, 2);
v_a_766_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_762_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_762_);
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
lean_dec_ref(v_e_741_);
goto v___jp_751_;
}
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec(v_a_756_);
lean_dec_ref(v_e_741_);
v___x_774_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_775_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_774_, v___f_754_, v_a_743_);
return v___x_775_;
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v___f_754_);
lean_dec_ref(v_e_741_);
v_a_776_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_755_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_755_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
v___jp_751_:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_box(0);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___boxed(lean_object* v_e_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(v_e_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec(v_a_785_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(lean_object* v_e_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(v_e_795_, v_a_796_, v_a_797_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___boxed(lean_object* v_e_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(v_e_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_a_812_);
lean_dec(v_a_811_);
lean_dec(v_a_810_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0(lean_object* v_00_u03b2_823_, lean_object* v_x_824_, lean_object* v_x_825_, lean_object* v_x_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_x_824_, v_x_825_, v_x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(lean_object* v_00_u03b2_828_, lean_object* v_x_829_, size_t v_x_830_, size_t v_x_831_, lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_829_, v_x_830_, v_x_831_, v_x_832_, v_x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
size_t v_x_6647__boxed_841_; size_t v_x_6648__boxed_842_; lean_object* v_res_843_; 
v_x_6647__boxed_841_ = lean_unbox_usize(v_x_837_);
lean_dec(v_x_837_);
v_x_6648__boxed_842_ = lean_unbox_usize(v_x_838_);
lean_dec(v_x_838_);
v_res_843_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(v_00_u03b2_835_, v_x_836_, v_x_6647__boxed_841_, v_x_6648__boxed_842_, v_x_839_, v_x_840_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_844_, lean_object* v_n_845_, lean_object* v_k_846_, lean_object* v_v_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(v_n_845_, v_k_846_, v_v_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_849_, size_t v_depth_850_, lean_object* v_keys_851_, lean_object* v_vals_852_, lean_object* v_heq_853_, lean_object* v_i_854_, lean_object* v_entries_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_depth_850_, v_keys_851_, v_vals_852_, v_i_854_, v_entries_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_857_, lean_object* v_depth_858_, lean_object* v_keys_859_, lean_object* v_vals_860_, lean_object* v_heq_861_, lean_object* v_i_862_, lean_object* v_entries_863_){
_start:
{
size_t v_depth_boxed_864_; lean_object* v_res_865_; 
v_depth_boxed_864_ = lean_unbox_usize(v_depth_858_);
lean_dec(v_depth_858_);
v_res_865_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(v_00_u03b2_857_, v_depth_boxed_864_, v_keys_859_, v_vals_860_, v_heq_861_, v_i_862_, v_entries_863_);
lean_dec_ref(v_vals_860_);
lean_dec_ref(v_keys_859_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_867_, v_x_868_, v_x_869_, v_x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0(lean_object* v_a_872_, lean_object* v_e_873_, lean_object* v___x_874_, lean_object* v_s_875_){
_start:
{
lean_object* v_structs_876_; lean_object* v_typeIdOf_877_; lean_object* v_exprToStructId_878_; lean_object* v_exprToStructIdEntries_879_; lean_object* v_forbiddenNatModules_880_; lean_object* v_natStructs_881_; lean_object* v_natTypeIdOf_882_; lean_object* v_exprToNatStructId_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v_structs_876_ = lean_ctor_get(v_s_875_, 0);
v_typeIdOf_877_ = lean_ctor_get(v_s_875_, 1);
v_exprToStructId_878_ = lean_ctor_get(v_s_875_, 2);
v_exprToStructIdEntries_879_ = lean_ctor_get(v_s_875_, 3);
v_forbiddenNatModules_880_ = lean_ctor_get(v_s_875_, 4);
v_natStructs_881_ = lean_ctor_get(v_s_875_, 5);
v_natTypeIdOf_882_ = lean_ctor_get(v_s_875_, 6);
v_exprToNatStructId_883_ = lean_ctor_get(v_s_875_, 7);
v___x_884_ = lean_array_get_size(v_natStructs_881_);
v___x_885_ = lean_nat_dec_lt(v_a_872_, v___x_884_);
if (v___x_885_ == 0)
{
lean_dec_ref(v___x_874_);
lean_dec_ref(v_e_873_);
return v_s_875_;
}
else
{
lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_922_; 
lean_inc_ref(v_exprToNatStructId_883_);
lean_inc_ref(v_natTypeIdOf_882_);
lean_inc_ref(v_natStructs_881_);
lean_inc_ref(v_forbiddenNatModules_880_);
lean_inc_ref(v_exprToStructIdEntries_879_);
lean_inc_ref(v_exprToStructId_878_);
lean_inc_ref(v_typeIdOf_877_);
lean_inc_ref(v_structs_876_);
v_isSharedCheck_922_ = !lean_is_exclusive(v_s_875_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; lean_object* v_unused_924_; lean_object* v_unused_925_; lean_object* v_unused_926_; lean_object* v_unused_927_; lean_object* v_unused_928_; lean_object* v_unused_929_; lean_object* v_unused_930_; 
v_unused_923_ = lean_ctor_get(v_s_875_, 7);
lean_dec(v_unused_923_);
v_unused_924_ = lean_ctor_get(v_s_875_, 6);
lean_dec(v_unused_924_);
v_unused_925_ = lean_ctor_get(v_s_875_, 5);
lean_dec(v_unused_925_);
v_unused_926_ = lean_ctor_get(v_s_875_, 4);
lean_dec(v_unused_926_);
v_unused_927_ = lean_ctor_get(v_s_875_, 3);
lean_dec(v_unused_927_);
v_unused_928_ = lean_ctor_get(v_s_875_, 2);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_s_875_, 1);
lean_dec(v_unused_929_);
v_unused_930_ = lean_ctor_get(v_s_875_, 0);
lean_dec(v_unused_930_);
v___x_887_ = v_s_875_;
v_isShared_888_ = v_isSharedCheck_922_;
goto v_resetjp_886_;
}
else
{
lean_dec(v_s_875_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_922_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_v_889_; lean_object* v_id_890_; lean_object* v_structId_891_; lean_object* v_type_892_; lean_object* v_u_893_; lean_object* v_natModuleInst_894_; lean_object* v_leInst_x3f_895_; lean_object* v_ltInst_x3f_896_; lean_object* v_lawfulOrderLTInst_x3f_897_; lean_object* v_isPreorderInst_x3f_898_; lean_object* v_orderedAddInst_x3f_899_; lean_object* v_isLinearInst_x3f_900_; lean_object* v_addRightCancelInst_x3f_901_; lean_object* v_rfl__q_902_; lean_object* v_zero_903_; lean_object* v_toQFn_904_; lean_object* v_addFn_905_; lean_object* v_smulFn_906_; lean_object* v_termMap_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_921_; 
v_v_889_ = lean_array_fget(v_natStructs_881_, v_a_872_);
v_id_890_ = lean_ctor_get(v_v_889_, 0);
v_structId_891_ = lean_ctor_get(v_v_889_, 1);
v_type_892_ = lean_ctor_get(v_v_889_, 2);
v_u_893_ = lean_ctor_get(v_v_889_, 3);
v_natModuleInst_894_ = lean_ctor_get(v_v_889_, 4);
v_leInst_x3f_895_ = lean_ctor_get(v_v_889_, 5);
v_ltInst_x3f_896_ = lean_ctor_get(v_v_889_, 6);
v_lawfulOrderLTInst_x3f_897_ = lean_ctor_get(v_v_889_, 7);
v_isPreorderInst_x3f_898_ = lean_ctor_get(v_v_889_, 8);
v_orderedAddInst_x3f_899_ = lean_ctor_get(v_v_889_, 9);
v_isLinearInst_x3f_900_ = lean_ctor_get(v_v_889_, 10);
v_addRightCancelInst_x3f_901_ = lean_ctor_get(v_v_889_, 11);
v_rfl__q_902_ = lean_ctor_get(v_v_889_, 12);
v_zero_903_ = lean_ctor_get(v_v_889_, 13);
v_toQFn_904_ = lean_ctor_get(v_v_889_, 14);
v_addFn_905_ = lean_ctor_get(v_v_889_, 15);
v_smulFn_906_ = lean_ctor_get(v_v_889_, 16);
v_termMap_907_ = lean_ctor_get(v_v_889_, 17);
v_isSharedCheck_921_ = !lean_is_exclusive(v_v_889_);
if (v_isSharedCheck_921_ == 0)
{
v___x_909_ = v_v_889_;
v_isShared_910_ = v_isSharedCheck_921_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_termMap_907_);
lean_inc(v_smulFn_906_);
lean_inc(v_addFn_905_);
lean_inc(v_toQFn_904_);
lean_inc(v_zero_903_);
lean_inc(v_rfl__q_902_);
lean_inc(v_addRightCancelInst_x3f_901_);
lean_inc(v_isLinearInst_x3f_900_);
lean_inc(v_orderedAddInst_x3f_899_);
lean_inc(v_isPreorderInst_x3f_898_);
lean_inc(v_lawfulOrderLTInst_x3f_897_);
lean_inc(v_ltInst_x3f_896_);
lean_inc(v_leInst_x3f_895_);
lean_inc(v_natModuleInst_894_);
lean_inc(v_u_893_);
lean_inc(v_type_892_);
lean_inc(v_structId_891_);
lean_inc(v_id_890_);
lean_dec(v_v_889_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_921_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v_xs_x27_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_911_ = lean_box(0);
v_xs_x27_912_ = lean_array_fset(v_natStructs_881_, v_a_872_, v___x_911_);
v___x_913_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_termMap_907_, v_e_873_, v___x_874_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 17, v___x_913_);
v___x_915_ = v___x_909_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_id_890_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_structId_891_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_type_892_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v_u_893_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v_natModuleInst_894_);
lean_ctor_set(v_reuseFailAlloc_920_, 5, v_leInst_x3f_895_);
lean_ctor_set(v_reuseFailAlloc_920_, 6, v_ltInst_x3f_896_);
lean_ctor_set(v_reuseFailAlloc_920_, 7, v_lawfulOrderLTInst_x3f_897_);
lean_ctor_set(v_reuseFailAlloc_920_, 8, v_isPreorderInst_x3f_898_);
lean_ctor_set(v_reuseFailAlloc_920_, 9, v_orderedAddInst_x3f_899_);
lean_ctor_set(v_reuseFailAlloc_920_, 10, v_isLinearInst_x3f_900_);
lean_ctor_set(v_reuseFailAlloc_920_, 11, v_addRightCancelInst_x3f_901_);
lean_ctor_set(v_reuseFailAlloc_920_, 12, v_rfl__q_902_);
lean_ctor_set(v_reuseFailAlloc_920_, 13, v_zero_903_);
lean_ctor_set(v_reuseFailAlloc_920_, 14, v_toQFn_904_);
lean_ctor_set(v_reuseFailAlloc_920_, 15, v_addFn_905_);
lean_ctor_set(v_reuseFailAlloc_920_, 16, v_smulFn_906_);
lean_ctor_set(v_reuseFailAlloc_920_, 17, v___x_913_);
v___x_915_ = v_reuseFailAlloc_920_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_916_ = lean_array_fset(v_xs_x27_912_, v_a_872_, v___x_915_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 5, v___x_916_);
v___x_918_ = v___x_887_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_structs_876_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_typeIdOf_877_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_exprToStructId_878_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_exprToStructIdEntries_879_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v_forbiddenNatModules_880_);
lean_ctor_set(v_reuseFailAlloc_919_, 5, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_919_, 6, v_natTypeIdOf_882_);
lean_ctor_set(v_reuseFailAlloc_919_, 7, v_exprToNatStructId_883_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0___boxed(lean_object* v_a_931_, lean_object* v_e_932_, lean_object* v___x_933_, lean_object* v_s_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0(v_a_931_, v_e_932_, v___x_933_, v_s_934_);
lean_dec(v_a_931_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(lean_object* v_e_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_1042_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_1042_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_1042_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_termMap_954_; lean_object* v___x_955_; 
v_termMap_954_ = lean_ctor_get(v_a_950_, 17);
lean_inc_ref(v_termMap_954_);
lean_dec(v_a_950_);
v___x_955_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_termMap_954_, v_e_936_);
lean_dec_ref(v_termMap_954_);
if (lean_obj_tag(v___x_955_) == 1)
{
lean_object* v_val_956_; lean_object* v___x_958_; 
lean_dec_ref(v_e_936_);
v_val_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_val_956_);
lean_dec_ref_known(v___x_955_, 1);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v_val_956_);
v___x_958_ = v___x_952_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_val_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
else
{
lean_object* v___x_960_; 
lean_dec(v___x_955_);
lean_del_object(v___x_952_);
v___x_960_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v_rfl__q_962_; lean_object* v_toQFn_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v_rfl__q_962_ = lean_ctor_get(v_a_961_, 12);
lean_inc_ref(v_rfl__q_962_);
v_toQFn_963_ = lean_ctor_get(v_a_961_, 14);
lean_inc_ref(v_toQFn_963_);
lean_dec(v_a_961_);
lean_inc_ref(v_e_936_);
v___x_964_ = l_Lean_Expr_app___override(v_toQFn_963_, v_e_936_);
v___x_965_ = l_Lean_Meta_Sym_shareCommon(v___x_964_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_936_, v_a_938_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = lean_box(0);
lean_inc(v_a_947_);
lean_inc_ref(v_a_946_);
lean_inc(v_a_945_);
lean_inc_ref(v_a_944_);
lean_inc(v_a_943_);
lean_inc_ref(v_a_942_);
lean_inc(v_a_941_);
lean_inc_ref(v_a_940_);
lean_inc(v_a_939_);
lean_inc(v_a_938_);
lean_inc(v_a_966_);
v___x_970_ = lean_grind_internalize(v_a_966_, v_a_968_, v___x_969_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___f_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_dec_ref_known(v___x_970_, 1);
lean_inc(v_a_966_);
v___x_971_ = l_Lean_Expr_app___override(v_rfl__q_962_, v_a_966_);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v_a_966_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
lean_inc_ref(v___x_972_);
lean_inc_ref(v_e_936_);
lean_inc(v_a_937_);
v___f_973_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0___boxed), 4, 3);
lean_closure_set(v___f_973_, 0, v_a_937_);
lean_closure_set(v___f_973_, 1, v_e_936_);
lean_closure_set(v___f_973_, 2, v___x_972_);
v___x_974_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_975_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_974_, v___f_973_, v_a_938_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v___x_976_; 
lean_dec_ref_known(v___x_975_, 1);
lean_inc_ref(v_e_936_);
v___x_976_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(v_e_936_, v_a_937_, v_a_938_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v___x_977_; 
lean_dec_ref_known(v___x_976_, 1);
v___x_977_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_974_, v_e_936_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_984_ == 0)
{
lean_object* v_unused_985_; 
v_unused_985_ = lean_ctor_get(v___x_977_, 0);
lean_dec(v_unused_985_);
v___x_979_ = v___x_977_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_dec(v___x_977_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_972_);
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_972_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec_ref_known(v___x_972_, 2);
v_a_986_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_977_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_977_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec_ref_known(v___x_972_, 2);
lean_dec_ref(v_e_936_);
v_a_994_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_976_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_976_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec_ref_known(v___x_972_, 2);
lean_dec_ref(v_e_936_);
v_a_1002_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_975_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_975_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
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
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v_a_966_);
lean_dec_ref(v_rfl__q_962_);
lean_dec_ref(v_e_936_);
v_a_1010_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_970_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_970_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec(v_a_966_);
lean_dec_ref(v_rfl__q_962_);
lean_dec_ref(v_e_936_);
v_a_1018_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_967_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_967_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec_ref(v_rfl__q_962_);
lean_dec_ref(v_e_936_);
v_a_1026_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_965_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_965_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref(v_e_936_);
v_a_1034_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_960_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_960_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec_ref(v_e_936_);
v_a_1043_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_949_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_949_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___boxed(lean_object* v_e_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec(v_a_1052_);
return v_res_1064_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(lean_object* v_natStruct_1065_, lean_object* v_inst_1066_){
_start:
{
lean_object* v_addFn_1067_; lean_object* v___x_1068_; size_t v___x_1069_; size_t v___x_1070_; uint8_t v___x_1071_; 
v_addFn_1067_ = lean_ctor_get(v_natStruct_1065_, 15);
v___x_1068_ = l_Lean_Expr_appArg_x21(v_addFn_1067_);
v___x_1069_ = lean_ptr_addr(v___x_1068_);
lean_dec_ref(v___x_1068_);
v___x_1070_ = lean_ptr_addr(v_inst_1066_);
v___x_1071_ = lean_usize_dec_eq(v___x_1069_, v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst___boxed(lean_object* v_natStruct_1072_, lean_object* v_inst_1073_){
_start:
{
uint8_t v_res_1074_; lean_object* v_r_1075_; 
v_res_1074_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_natStruct_1072_, v_inst_1073_);
lean_dec_ref(v_inst_1073_);
lean_dec_ref(v_natStruct_1072_);
v_r_1075_ = lean_box(v_res_1074_);
return v_r_1075_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(lean_object* v_natStruct_1076_, lean_object* v_inst_1077_){
_start:
{
lean_object* v_zero_1078_; lean_object* v___x_1079_; size_t v___x_1080_; size_t v___x_1081_; uint8_t v___x_1082_; 
v_zero_1078_ = lean_ctor_get(v_natStruct_1076_, 13);
v___x_1079_ = l_Lean_Expr_appArg_x21(v_zero_1078_);
v___x_1080_ = lean_ptr_addr(v___x_1079_);
lean_dec_ref(v___x_1079_);
v___x_1081_ = lean_ptr_addr(v_inst_1077_);
v___x_1082_ = lean_usize_dec_eq(v___x_1080_, v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst___boxed(lean_object* v_natStruct_1083_, lean_object* v_inst_1084_){
_start:
{
uint8_t v_res_1085_; lean_object* v_r_1086_; 
v_res_1085_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_natStruct_1083_, v_inst_1084_);
lean_dec_ref(v_inst_1084_);
lean_dec_ref(v_natStruct_1083_);
v_r_1086_ = lean_box(v_res_1085_);
return v_r_1086_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(lean_object* v_natStruct_1087_, lean_object* v_inst_1088_){
_start:
{
lean_object* v_smulFn_1089_; lean_object* v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; uint8_t v___x_1093_; 
v_smulFn_1089_ = lean_ctor_get(v_natStruct_1087_, 16);
v___x_1090_ = l_Lean_Expr_appArg_x21(v_smulFn_1089_);
v___x_1091_ = lean_ptr_addr(v___x_1090_);
lean_dec_ref(v___x_1090_);
v___x_1092_ = lean_ptr_addr(v_inst_1088_);
v___x_1093_ = lean_usize_dec_eq(v___x_1091_, v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst___boxed(lean_object* v_natStruct_1094_, lean_object* v_inst_1095_){
_start:
{
uint8_t v_res_1096_; lean_object* v_r_1097_; 
v_res_1096_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_natStruct_1094_, v_inst_1095_);
lean_dec_ref(v_inst_1095_);
lean_dec_ref(v_natStruct_1094_);
v_r_1097_ = lean_box(v_res_1096_);
return v_r_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(lean_object* v_e_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1158_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1158_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1160_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
lean_inc_ref(v_e_1143_);
v___x_1160_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1143_, v_a_1152_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1311_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1311_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1311_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = l_Lean_Expr_cleanupAnnotations(v_a_1161_);
v___x_1166_ = l_Lean_Expr_isApp(v___x_1165_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
lean_dec_ref(v___x_1165_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1159_);
lean_dec(v_a_1157_);
v___x_1167_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1167_;
}
else
{
lean_object* v_arg_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v_arg_1168_ = lean_ctor_get(v___x_1165_, 1);
lean_inc_ref(v_arg_1168_);
v___x_1169_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1165_);
v___x_1170_ = l_Lean_Expr_isApp(v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; 
lean_dec_ref(v___x_1169_);
lean_dec_ref(v_arg_1168_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1159_);
lean_dec(v_a_1157_);
v___x_1171_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1171_;
}
else
{
lean_object* v_arg_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v_arg_1172_ = lean_ctor_get(v___x_1169_, 1);
lean_inc_ref(v_arg_1172_);
v___x_1173_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1169_);
v___x_1174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2));
v___x_1175_ = l_Lean_Expr_isConstOf(v___x_1173_, v___x_1174_);
if (v___x_1175_ == 0)
{
uint8_t v___x_1176_; 
lean_del_object(v___x_1163_);
v___x_1176_ = l_Lean_Expr_isApp(v___x_1173_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; 
lean_dec_ref(v___x_1173_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_arg_1168_);
lean_dec(v_a_1159_);
lean_dec(v_a_1157_);
v___x_1177_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1177_;
}
else
{
lean_object* v_arg_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v_arg_1178_ = lean_ctor_get(v___x_1173_, 1);
lean_inc_ref(v_arg_1178_);
v___x_1179_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1173_);
v___x_1180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5));
v___x_1181_ = l_Lean_Expr_isConstOf(v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
uint8_t v___x_1182_; 
v___x_1182_ = l_Lean_Expr_isApp(v___x_1179_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
lean_dec_ref(v___x_1179_);
lean_dec_ref(v_arg_1178_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_arg_1168_);
lean_dec(v_a_1159_);
lean_dec(v_a_1157_);
v___x_1183_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1183_;
}
else
{
lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1179_);
v___x_1185_ = l_Lean_Expr_isApp(v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; 
lean_dec_ref(v___x_1184_);
lean_dec_ref(v_arg_1178_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_arg_1168_);
lean_dec(v_a_1159_);
lean_dec(v_a_1157_);
v___x_1186_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1184_);
v___x_1188_ = l_Lean_Expr_isApp(v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; 
lean_dec_ref(v___x_1187_);
lean_dec_ref(v_arg_1178_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_arg_1168_);
lean_dec(v_a_1159_);
lean_dec(v_a_1157_);
v___x_1189_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1189_;
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1190_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1187_);
v___x_1191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8));
v___x_1192_ = l_Lean_Expr_isConstOf(v___x_1190_, v___x_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11));
v___x_1194_ = l_Lean_Expr_isConstOf(v___x_1190_, v___x_1193_);
lean_dec_ref(v___x_1190_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
lean_dec_ref(v_arg_1178_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_arg_1168_);
lean_dec(v_a_1159_);
lean_dec(v_a_1157_);
v___x_1195_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1195_;
}
else
{
uint8_t v___x_1196_; 
v___x_1196_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_1159_, v_arg_1178_);
lean_dec_ref(v_arg_1178_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; 
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_arg_1168_);
lean_dec(v_a_1159_);
lean_dec(v_a_1157_);
v___x_1197_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1197_;
}
else
{
lean_object* v___x_1198_; 
lean_dec_ref(v_e_1143_);
lean_inc_ref(v_arg_1172_);
v___x_1198_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_1172_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v_fst_1200_; lean_object* v_snd_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1235_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v_fst_1200_ = lean_ctor_get(v_a_1199_, 0);
v_snd_1201_ = lean_ctor_get(v_a_1199_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_a_1199_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1203_ = v_a_1199_;
v_isShared_1204_ = v_isSharedCheck_1235_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_snd_1201_);
lean_inc(v_fst_1200_);
lean_dec(v_a_1199_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1235_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; 
lean_inc_ref(v_arg_1168_);
v___x_1205_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_1168_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1234_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1234_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1234_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v_fst_1210_; lean_object* v_snd_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1233_; 
v_fst_1210_ = lean_ctor_get(v_a_1206_, 0);
v_snd_1211_ = lean_ctor_get(v_a_1206_, 1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_a_1206_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1213_ = v_a_1206_;
v_isShared_1214_ = v_isSharedCheck_1233_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_snd_1211_);
lean_inc(v_fst_1210_);
lean_dec(v_a_1206_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1233_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_addFn_1215_; lean_object* v_type_1216_; lean_object* v_u_1217_; lean_object* v_natModuleInst_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v_addFn_1215_ = lean_ctor_get(v_a_1157_, 22);
lean_inc_ref(v_addFn_1215_);
lean_dec(v_a_1157_);
v_type_1216_ = lean_ctor_get(v_a_1159_, 2);
lean_inc_ref(v_type_1216_);
v_u_1217_ = lean_ctor_get(v_a_1159_, 3);
lean_inc(v_u_1217_);
v_natModuleInst_1218_ = lean_ctor_get(v_a_1159_, 4);
lean_inc_ref(v_natModuleInst_1218_);
lean_dec(v_a_1159_);
lean_inc(v_fst_1210_);
lean_inc(v_fst_1200_);
v___x_1219_ = l_Lean_mkAppB(v_addFn_1215_, v_fst_1200_, v_fst_1210_);
v___x_1220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17));
v___x_1221_ = lean_box(0);
if (v_isShared_1204_ == 0)
{
lean_ctor_set_tag(v___x_1203_, 1);
lean_ctor_set(v___x_1203_, 1, v___x_1221_);
lean_ctor_set(v___x_1203_, 0, v_u_1217_);
v___x_1223_ = v___x_1203_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_u_1217_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1224_ = l_Lean_mkConst(v___x_1220_, v___x_1223_);
v___x_1225_ = l_Lean_mkApp8(v___x_1224_, v_type_1216_, v_natModuleInst_1218_, v_arg_1172_, v_arg_1168_, v_fst_1200_, v_fst_1210_, v_snd_1201_, v_snd_1211_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 1, v___x_1225_);
lean_ctor_set(v___x_1213_, 0, v___x_1219_);
v___x_1227_ = v___x_1213_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1229_; 
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1227_);
v___x_1229_ = v___x_1208_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1203_);
lean_dec(v_snd_1201_);
lean_dec(v_fst_1200_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_arg_1168_);
lean_dec(v_a_1159_);
lean_dec(v_a_1157_);
return v___x_1205_;
}
}
}
else
{
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_arg_1168_);
lean_dec(v_a_1159_);
lean_dec(v_a_1157_);
return v___x_1198_;
}
}
}
}
else
{
uint8_t v___x_1236_; 
lean_dec_ref(v___x_1190_);
v___x_1236_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_a_1159_, v_arg_1178_);
lean_dec_ref(v_arg_1178_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_arg_1168_);
lean_dec(v_a_1159_);
lean_dec(v_a_1157_);
v___x_1237_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1237_;
}
else
{
lean_object* v___x_1238_; 
lean_dec_ref(v_e_1143_);
lean_inc_ref(v_arg_1168_);
v___x_1238_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_1168_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1265_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1265_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1265_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v_fst_1243_; lean_object* v_snd_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1264_; 
v_fst_1243_ = lean_ctor_get(v_a_1239_, 0);
v_snd_1244_ = lean_ctor_get(v_a_1239_, 1);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_a_1239_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1246_ = v_a_1239_;
v_isShared_1247_ = v_isSharedCheck_1264_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_snd_1244_);
lean_inc(v_fst_1243_);
lean_dec(v_a_1239_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1264_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_nsmulFn_1248_; lean_object* v_type_1249_; lean_object* v_u_1250_; lean_object* v_natModuleInst_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v_nsmulFn_1248_ = lean_ctor_get(v_a_1157_, 24);
lean_inc_ref(v_nsmulFn_1248_);
lean_dec(v_a_1157_);
v_type_1249_ = lean_ctor_get(v_a_1159_, 2);
lean_inc_ref(v_type_1249_);
v_u_1250_ = lean_ctor_get(v_a_1159_, 3);
lean_inc(v_u_1250_);
v_natModuleInst_1251_ = lean_ctor_get(v_a_1159_, 4);
lean_inc_ref(v_natModuleInst_1251_);
lean_dec(v_a_1159_);
lean_inc(v_fst_1243_);
lean_inc_ref(v_arg_1172_);
v___x_1252_ = l_Lean_mkAppB(v_nsmulFn_1248_, v_arg_1172_, v_fst_1243_);
v___x_1253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19));
v___x_1254_ = lean_box(0);
v___x_1255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1255_, 0, v_u_1250_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___x_1256_ = l_Lean_mkConst(v___x_1253_, v___x_1255_);
v___x_1257_ = l_Lean_mkApp6(v___x_1256_, v_type_1249_, v_natModuleInst_1251_, v_arg_1172_, v_arg_1168_, v_fst_1243_, v_snd_1244_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1257_);
lean_ctor_set(v___x_1246_, 0, v___x_1252_);
v___x_1259_ = v___x_1246_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1261_; 
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v___x_1259_);
v___x_1261_ = v___x_1241_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_arg_1168_);
lean_dec(v_a_1159_);
lean_dec(v_a_1157_);
return v___x_1238_;
}
}
}
}
}
}
}
else
{
lean_object* v_type_1266_; lean_object* v_u_1267_; lean_object* v_natModuleInst_1268_; lean_object* v_zero_1269_; lean_object* v___x_1270_; 
lean_dec_ref(v___x_1179_);
lean_dec_ref(v_arg_1178_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_arg_1168_);
v_type_1266_ = lean_ctor_get(v_a_1159_, 2);
lean_inc_ref(v_type_1266_);
v_u_1267_ = lean_ctor_get(v_a_1159_, 3);
lean_inc(v_u_1267_);
v_natModuleInst_1268_ = lean_ctor_get(v_a_1159_, 4);
lean_inc_ref(v_natModuleInst_1268_);
v_zero_1269_ = lean_ctor_get(v_a_1159_, 13);
lean_inc_ref(v_zero_1269_);
lean_dec(v_a_1159_);
lean_inc_ref(v_e_1143_);
v___x_1270_ = l_Lean_Meta_isDefEqD(v_e_1143_, v_zero_1269_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1287_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1287_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1287_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
uint8_t v___x_1275_; 
v___x_1275_ = lean_unbox(v_a_1271_);
lean_dec(v_a_1271_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; 
lean_del_object(v___x_1273_);
lean_dec_ref(v_natModuleInst_1268_);
lean_dec(v_u_1267_);
lean_dec_ref(v_type_1266_);
lean_dec(v_a_1157_);
v___x_1276_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1276_;
}
else
{
lean_object* v_zero_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
lean_dec_ref(v_e_1143_);
v_zero_1277_ = lean_ctor_get(v_a_1157_, 17);
lean_inc_ref(v_zero_1277_);
lean_dec(v_a_1157_);
v___x_1278_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21));
v___x_1279_ = lean_box(0);
v___x_1280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1280_, 0, v_u_1267_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = l_Lean_mkConst(v___x_1278_, v___x_1280_);
v___x_1282_ = l_Lean_mkAppB(v___x_1281_, v_type_1266_, v_natModuleInst_1268_);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v_zero_1277_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1283_);
v___x_1285_ = v___x_1273_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_natModuleInst_1268_);
lean_dec(v_u_1267_);
lean_dec_ref(v_type_1266_);
lean_dec(v_a_1157_);
lean_dec_ref(v_e_1143_);
v_a_1288_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1270_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1270_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
}
else
{
uint8_t v___x_1296_; 
lean_dec_ref(v___x_1173_);
lean_dec_ref(v_arg_1172_);
v___x_1296_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_1159_, v_arg_1168_);
lean_dec_ref(v_arg_1168_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; 
lean_del_object(v___x_1163_);
lean_dec(v_a_1159_);
lean_dec(v_a_1157_);
v___x_1297_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1297_;
}
else
{
lean_object* v_zero_1298_; lean_object* v_type_1299_; lean_object* v_u_1300_; lean_object* v_natModuleInst_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1309_; 
lean_dec_ref(v_e_1143_);
v_zero_1298_ = lean_ctor_get(v_a_1157_, 17);
lean_inc_ref(v_zero_1298_);
lean_dec(v_a_1157_);
v_type_1299_ = lean_ctor_get(v_a_1159_, 2);
lean_inc_ref(v_type_1299_);
v_u_1300_ = lean_ctor_get(v_a_1159_, 3);
lean_inc(v_u_1300_);
v_natModuleInst_1301_ = lean_ctor_get(v_a_1159_, 4);
lean_inc_ref(v_natModuleInst_1301_);
lean_dec(v_a_1159_);
v___x_1302_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21));
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1304_, 0, v_u_1300_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = l_Lean_mkConst(v___x_1302_, v___x_1304_);
v___x_1306_ = l_Lean_mkAppB(v___x_1305_, v_type_1299_, v_natModuleInst_1301_);
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v_zero_1298_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1307_);
v___x_1309_ = v___x_1163_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec(v_a_1159_);
lean_dec(v_a_1157_);
lean_dec_ref(v_e_1143_);
v_a_1312_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1160_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1160_);
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
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec(v_a_1157_);
lean_dec_ref(v_e_1143_);
v_a_1320_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1158_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1158_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v_e_1143_);
v_a_1328_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1156_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1156_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___boxed(lean_object* v_e_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_e_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
lean_dec(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec(v_a_1337_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0(lean_object* v___y_1350_, lean_object* v_e_1351_, lean_object* v_____x_1352_, lean_object* v_s_1353_){
_start:
{
lean_object* v_structs_1354_; lean_object* v_typeIdOf_1355_; lean_object* v_exprToStructId_1356_; lean_object* v_exprToStructIdEntries_1357_; lean_object* v_forbiddenNatModules_1358_; lean_object* v_natStructs_1359_; lean_object* v_natTypeIdOf_1360_; lean_object* v_exprToNatStructId_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v_structs_1354_ = lean_ctor_get(v_s_1353_, 0);
v_typeIdOf_1355_ = lean_ctor_get(v_s_1353_, 1);
v_exprToStructId_1356_ = lean_ctor_get(v_s_1353_, 2);
v_exprToStructIdEntries_1357_ = lean_ctor_get(v_s_1353_, 3);
v_forbiddenNatModules_1358_ = lean_ctor_get(v_s_1353_, 4);
v_natStructs_1359_ = lean_ctor_get(v_s_1353_, 5);
v_natTypeIdOf_1360_ = lean_ctor_get(v_s_1353_, 6);
v_exprToNatStructId_1361_ = lean_ctor_get(v_s_1353_, 7);
v___x_1362_ = lean_array_get_size(v_natStructs_1359_);
v___x_1363_ = lean_nat_dec_lt(v___y_1350_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_dec_ref(v_____x_1352_);
lean_dec_ref(v_e_1351_);
return v_s_1353_;
}
else
{
lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1400_; 
lean_inc_ref(v_exprToNatStructId_1361_);
lean_inc_ref(v_natTypeIdOf_1360_);
lean_inc_ref(v_natStructs_1359_);
lean_inc_ref(v_forbiddenNatModules_1358_);
lean_inc_ref(v_exprToStructIdEntries_1357_);
lean_inc_ref(v_exprToStructId_1356_);
lean_inc_ref(v_typeIdOf_1355_);
lean_inc_ref(v_structs_1354_);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_s_1353_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; lean_object* v_unused_1402_; lean_object* v_unused_1403_; lean_object* v_unused_1404_; lean_object* v_unused_1405_; lean_object* v_unused_1406_; lean_object* v_unused_1407_; lean_object* v_unused_1408_; 
v_unused_1401_ = lean_ctor_get(v_s_1353_, 7);
lean_dec(v_unused_1401_);
v_unused_1402_ = lean_ctor_get(v_s_1353_, 6);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_s_1353_, 5);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_s_1353_, 4);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_s_1353_, 3);
lean_dec(v_unused_1405_);
v_unused_1406_ = lean_ctor_get(v_s_1353_, 2);
lean_dec(v_unused_1406_);
v_unused_1407_ = lean_ctor_get(v_s_1353_, 1);
lean_dec(v_unused_1407_);
v_unused_1408_ = lean_ctor_get(v_s_1353_, 0);
lean_dec(v_unused_1408_);
v___x_1365_ = v_s_1353_;
v_isShared_1366_ = v_isSharedCheck_1400_;
goto v_resetjp_1364_;
}
else
{
lean_dec(v_s_1353_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1400_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v_v_1367_; lean_object* v_id_1368_; lean_object* v_structId_1369_; lean_object* v_type_1370_; lean_object* v_u_1371_; lean_object* v_natModuleInst_1372_; lean_object* v_leInst_x3f_1373_; lean_object* v_ltInst_x3f_1374_; lean_object* v_lawfulOrderLTInst_x3f_1375_; lean_object* v_isPreorderInst_x3f_1376_; lean_object* v_orderedAddInst_x3f_1377_; lean_object* v_isLinearInst_x3f_1378_; lean_object* v_addRightCancelInst_x3f_1379_; lean_object* v_rfl__q_1380_; lean_object* v_zero_1381_; lean_object* v_toQFn_1382_; lean_object* v_addFn_1383_; lean_object* v_smulFn_1384_; lean_object* v_termMap_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1399_; 
v_v_1367_ = lean_array_fget(v_natStructs_1359_, v___y_1350_);
v_id_1368_ = lean_ctor_get(v_v_1367_, 0);
v_structId_1369_ = lean_ctor_get(v_v_1367_, 1);
v_type_1370_ = lean_ctor_get(v_v_1367_, 2);
v_u_1371_ = lean_ctor_get(v_v_1367_, 3);
v_natModuleInst_1372_ = lean_ctor_get(v_v_1367_, 4);
v_leInst_x3f_1373_ = lean_ctor_get(v_v_1367_, 5);
v_ltInst_x3f_1374_ = lean_ctor_get(v_v_1367_, 6);
v_lawfulOrderLTInst_x3f_1375_ = lean_ctor_get(v_v_1367_, 7);
v_isPreorderInst_x3f_1376_ = lean_ctor_get(v_v_1367_, 8);
v_orderedAddInst_x3f_1377_ = lean_ctor_get(v_v_1367_, 9);
v_isLinearInst_x3f_1378_ = lean_ctor_get(v_v_1367_, 10);
v_addRightCancelInst_x3f_1379_ = lean_ctor_get(v_v_1367_, 11);
v_rfl__q_1380_ = lean_ctor_get(v_v_1367_, 12);
v_zero_1381_ = lean_ctor_get(v_v_1367_, 13);
v_toQFn_1382_ = lean_ctor_get(v_v_1367_, 14);
v_addFn_1383_ = lean_ctor_get(v_v_1367_, 15);
v_smulFn_1384_ = lean_ctor_get(v_v_1367_, 16);
v_termMap_1385_ = lean_ctor_get(v_v_1367_, 17);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_v_1367_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1387_ = v_v_1367_;
v_isShared_1388_ = v_isSharedCheck_1399_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_termMap_1385_);
lean_inc(v_smulFn_1384_);
lean_inc(v_addFn_1383_);
lean_inc(v_toQFn_1382_);
lean_inc(v_zero_1381_);
lean_inc(v_rfl__q_1380_);
lean_inc(v_addRightCancelInst_x3f_1379_);
lean_inc(v_isLinearInst_x3f_1378_);
lean_inc(v_orderedAddInst_x3f_1377_);
lean_inc(v_isPreorderInst_x3f_1376_);
lean_inc(v_lawfulOrderLTInst_x3f_1375_);
lean_inc(v_ltInst_x3f_1374_);
lean_inc(v_leInst_x3f_1373_);
lean_inc(v_natModuleInst_1372_);
lean_inc(v_u_1371_);
lean_inc(v_type_1370_);
lean_inc(v_structId_1369_);
lean_inc(v_id_1368_);
lean_dec(v_v_1367_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1399_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v_xs_x27_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1389_ = lean_box(0);
v_xs_x27_1390_ = lean_array_fset(v_natStructs_1359_, v___y_1350_, v___x_1389_);
v___x_1391_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_termMap_1385_, v_e_1351_, v_____x_1352_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 17, v___x_1391_);
v___x_1393_ = v___x_1387_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_id_1368_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_structId_1369_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_type_1370_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v_u_1371_);
lean_ctor_set(v_reuseFailAlloc_1398_, 4, v_natModuleInst_1372_);
lean_ctor_set(v_reuseFailAlloc_1398_, 5, v_leInst_x3f_1373_);
lean_ctor_set(v_reuseFailAlloc_1398_, 6, v_ltInst_x3f_1374_);
lean_ctor_set(v_reuseFailAlloc_1398_, 7, v_lawfulOrderLTInst_x3f_1375_);
lean_ctor_set(v_reuseFailAlloc_1398_, 8, v_isPreorderInst_x3f_1376_);
lean_ctor_set(v_reuseFailAlloc_1398_, 9, v_orderedAddInst_x3f_1377_);
lean_ctor_set(v_reuseFailAlloc_1398_, 10, v_isLinearInst_x3f_1378_);
lean_ctor_set(v_reuseFailAlloc_1398_, 11, v_addRightCancelInst_x3f_1379_);
lean_ctor_set(v_reuseFailAlloc_1398_, 12, v_rfl__q_1380_);
lean_ctor_set(v_reuseFailAlloc_1398_, 13, v_zero_1381_);
lean_ctor_set(v_reuseFailAlloc_1398_, 14, v_toQFn_1382_);
lean_ctor_set(v_reuseFailAlloc_1398_, 15, v_addFn_1383_);
lean_ctor_set(v_reuseFailAlloc_1398_, 16, v_smulFn_1384_);
lean_ctor_set(v_reuseFailAlloc_1398_, 17, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1394_ = lean_array_fset(v_xs_x27_1390_, v___y_1350_, v___x_1393_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 5, v___x_1394_);
v___x_1396_ = v___x_1365_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_structs_1354_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_typeIdOf_1355_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_exprToStructId_1356_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_exprToStructIdEntries_1357_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v_forbiddenNatModules_1358_);
lean_ctor_set(v_reuseFailAlloc_1397_, 5, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1397_, 6, v_natTypeIdOf_1360_);
lean_ctor_set(v_reuseFailAlloc_1397_, 7, v_exprToNatStructId_1361_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0___boxed(lean_object* v___y_1409_, lean_object* v_e_1410_, lean_object* v_____x_1411_, lean_object* v_s_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0(v___y_1409_, v_e_1410_, v_____x_1411_, v_s_1412_);
lean_dec(v___y_1409_);
return v_res_1413_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofNatModule___closed__0(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
v___x_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule(lean_object* v_e_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v_____x_1430_; lean_object* v_fst_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1540_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1540_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1540_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v_termMap_1496_; lean_object* v___x_1497_; 
v_termMap_1496_ = lean_ctor_get(v_a_1492_, 17);
lean_inc_ref(v_termMap_1496_);
lean_dec(v_a_1492_);
v___x_1497_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_termMap_1496_, v_e_1416_);
lean_dec_ref(v_termMap_1496_);
if (lean_obj_tag(v___x_1497_) == 1)
{
lean_object* v_val_1498_; lean_object* v___x_1500_; 
lean_dec_ref(v_e_1416_);
v_val_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_val_1498_);
lean_dec_ref_known(v___x_1497_, 1);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v_val_1498_);
v___x_1500_ = v___x_1494_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_val_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
else
{
lean_object* v___x_1502_; 
lean_dec(v___x_1497_);
lean_del_object(v___x_1494_);
lean_inc_ref(v_e_1416_);
v___x_1502_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_e_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v_fst_1504_; lean_object* v_snd_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1539_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1502_, 1);
v_fst_1504_ = lean_ctor_get(v_a_1503_, 0);
v_snd_1505_ = lean_ctor_get(v_a_1503_, 1);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_a_1503_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1507_ = v_a_1503_;
v_isShared_1508_ = v_isSharedCheck_1539_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_snd_1505_);
lean_inc(v_fst_1504_);
lean_dec(v_a_1503_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1539_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; 
lean_inc(v_a_1427_);
lean_inc_ref(v_a_1426_);
lean_inc(v_a_1425_);
lean_inc_ref(v_a_1424_);
lean_inc(v_a_1423_);
lean_inc_ref(v_a_1422_);
lean_inc(v_a_1421_);
lean_inc_ref(v_a_1420_);
lean_inc(v_a_1419_);
lean_inc(v_a_1418_);
v___x_1509_ = lean_grind_preprocess(v_fst_1504_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v_proof_x3f_1511_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1509_, 1);
v_proof_x3f_1511_ = lean_ctor_get(v_a_1510_, 1);
if (lean_obj_tag(v_proof_x3f_1511_) == 1)
{
lean_object* v_expr_1512_; lean_object* v_val_1513_; lean_object* v___x_1514_; 
lean_inc_ref(v_proof_x3f_1511_);
v_expr_1512_ = lean_ctor_get(v_a_1510_, 0);
lean_inc_ref(v_expr_1512_);
lean_dec(v_a_1510_);
v_val_1513_ = lean_ctor_get(v_proof_x3f_1511_, 0);
lean_inc(v_val_1513_);
lean_dec_ref_known(v_proof_x3f_1511_, 1);
v___x_1514_ = l_Lean_Meta_mkEqTrans(v_snd_1505_, v_val_1513_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
lean_inc_ref(v_expr_1512_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v_a_1515_);
lean_ctor_set(v___x_1507_, 0, v_expr_1512_);
v___x_1517_ = v___x_1507_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_expr_1512_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_a_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
v_____x_1430_ = v___x_1517_;
v_fst_1431_ = v_expr_1512_;
v___y_1432_ = v_a_1417_;
v___y_1433_ = v_a_1418_;
v___y_1434_ = v_a_1419_;
v___y_1435_ = v_a_1420_;
v___y_1436_ = v_a_1421_;
v___y_1437_ = v_a_1422_;
v___y_1438_ = v_a_1423_;
v___y_1439_ = v_a_1424_;
v___y_1440_ = v_a_1425_;
v___y_1441_ = v_a_1426_;
v___y_1442_ = v_a_1427_;
goto v___jp_1429_;
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v_expr_1512_);
lean_del_object(v___x_1507_);
lean_dec_ref(v_e_1416_);
v_a_1519_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1514_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1514_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
lean_object* v_expr_1527_; lean_object* v___x_1529_; 
v_expr_1527_ = lean_ctor_get(v_a_1510_, 0);
lean_inc_ref_n(v_expr_1527_, 2);
lean_dec(v_a_1510_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v_expr_1527_);
v___x_1529_ = v___x_1507_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_expr_1527_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_snd_1505_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
v_____x_1430_ = v___x_1529_;
v_fst_1431_ = v_expr_1527_;
v___y_1432_ = v_a_1417_;
v___y_1433_ = v_a_1418_;
v___y_1434_ = v_a_1419_;
v___y_1435_ = v_a_1420_;
v___y_1436_ = v_a_1421_;
v___y_1437_ = v_a_1422_;
v___y_1438_ = v_a_1423_;
v___y_1439_ = v_a_1424_;
v___y_1440_ = v_a_1425_;
v___y_1441_ = v_a_1426_;
v___y_1442_ = v_a_1427_;
goto v___jp_1429_;
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_del_object(v___x_1507_);
lean_dec(v_snd_1505_);
lean_dec_ref(v_e_1416_);
v_a_1531_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1509_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1509_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1416_);
return v___x_1502_;
}
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec_ref(v_e_1416_);
v_a_1541_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1491_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1491_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
v___jp_1429_:
{
lean_object* v___f_1443_; lean_object* v___x_1444_; 
lean_inc_ref(v_____x_1430_);
lean_inc_ref(v_e_1416_);
lean_inc(v___y_1432_);
v___f_1443_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1443_, 0, v___y_1432_);
lean_closure_set(v___f_1443_, 1, v_e_1416_);
lean_closure_set(v___f_1443_, 2, v_____x_1430_);
v___x_1444_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1416_, v___y_1433_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v___x_1446_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofNatModule___closed__0, &l_Lean_Meta_Grind_Arith_Linear_ofNatModule___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofNatModule___closed__0);
lean_inc(v___y_1442_);
lean_inc_ref(v___y_1441_);
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
lean_inc(v___y_1438_);
lean_inc_ref(v___y_1437_);
lean_inc(v___y_1436_);
lean_inc_ref(v___y_1435_);
lean_inc(v___y_1434_);
lean_inc(v___y_1433_);
v___x_1447_ = lean_grind_internalize(v_fst_1431_, v_a_1445_, v___x_1446_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v___x_1448_; 
lean_dec_ref_known(v___x_1447_, 1);
v___x_1448_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(v_e_1416_, v___y_1432_, v___y_1433_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec_ref_known(v___x_1448_, 1);
v___x_1449_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1450_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1449_, v___f_1443_, v___y_1433_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v___x_1450_, 0);
lean_dec(v_unused_1458_);
v___x_1452_ = v___x_1450_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_dec(v___x_1450_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v_____x_1430_);
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_____x_1430_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_dec_ref(v_____x_1430_);
v_a_1459_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1450_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1450_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec_ref(v___f_1443_);
lean_dec_ref(v_____x_1430_);
v_a_1467_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1448_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1448_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec_ref(v___f_1443_);
lean_dec_ref(v_____x_1430_);
lean_dec_ref(v_e_1416_);
v_a_1475_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1447_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1447_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec_ref(v___f_1443_);
lean_dec_ref(v_fst_1431_);
lean_dec_ref(v_____x_1430_);
lean_dec_ref(v_e_1416_);
v_a_1483_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1444_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1444_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___boxed(lean_object* v_e_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_e_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec_ref(v_a_1553_);
lean_dec(v_a_1552_);
lean_dec(v_a_1551_);
lean_dec(v_a_1550_);
return v_res_1562_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_unsigned_to_nat(16u);
v___x_1565_ = lean_mk_array(v___x_1564_, v___x_1563_);
return v___x_1565_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1566_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0);
v___x_1567_ = lean_unsigned_to_nat(0u);
v___x_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v___x_1566_);
return v___x_1568_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2));
v___x_1572_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1);
v___x_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
lean_ctor_set(v___x_1573_, 1, v___x_1571_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(lean_object* v_x_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1587_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
v___x_1588_ = lean_st_mk_ref(v___x_1587_);
lean_inc(v_a_1585_);
lean_inc_ref(v_a_1584_);
lean_inc(v_a_1583_);
lean_inc_ref(v_a_1582_);
lean_inc(v_a_1581_);
lean_inc_ref(v_a_1580_);
lean_inc(v_a_1579_);
lean_inc_ref(v_a_1578_);
lean_inc(v_a_1577_);
lean_inc(v_a_1576_);
lean_inc(v_a_1575_);
lean_inc(v___x_1588_);
v___x_1589_ = lean_apply_13(v_x_1574_, v___x_1588_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, lean_box(0));
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1598_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1598_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1598_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1596_; 
v___x_1594_ = lean_st_ref_get(v___x_1588_);
lean_dec(v___x_1588_);
lean_dec(v___x_1594_);
if (v_isShared_1593_ == 0)
{
v___x_1596_ = v___x_1592_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1590_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
else
{
lean_dec(v___x_1588_);
return v___x_1589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___boxed(lean_object* v_x_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(v_x_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
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
lean_dec(v_a_1600_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(lean_object* v_00_u03b1_1613_, lean_object* v_x_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1627_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
v___x_1628_ = lean_st_mk_ref(v___x_1627_);
lean_inc(v_a_1625_);
lean_inc_ref(v_a_1624_);
lean_inc(v_a_1623_);
lean_inc_ref(v_a_1622_);
lean_inc(v_a_1621_);
lean_inc_ref(v_a_1620_);
lean_inc(v_a_1619_);
lean_inc_ref(v_a_1618_);
lean_inc(v_a_1617_);
lean_inc(v_a_1616_);
lean_inc(v_a_1615_);
lean_inc(v___x_1628_);
v___x_1629_ = lean_apply_13(v_x_1614_, v___x_1628_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, lean_box(0));
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1638_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1638_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1638_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1634_ = lean_st_ref_get(v___x_1628_);
lean_dec(v___x_1628_);
lean_dec(v___x_1634_);
if (v_isShared_1633_ == 0)
{
v___x_1636_ = v___x_1632_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1630_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
else
{
lean_dec(v___x_1628_);
return v___x_1629_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___boxed(lean_object* v_00_u03b1_1639_, lean_object* v_x_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(v_00_u03b1_1639_, v_x_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec(v_a_1642_);
lean_dec(v_a_1641_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(lean_object* v_a_1654_, lean_object* v_b_1655_, lean_object* v_x_1656_){
_start:
{
if (lean_obj_tag(v_x_1656_) == 0)
{
lean_dec(v_b_1655_);
lean_dec_ref(v_a_1654_);
return v_x_1656_;
}
else
{
lean_object* v_key_1657_; lean_object* v_value_1658_; lean_object* v_tail_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1673_; 
v_key_1657_ = lean_ctor_get(v_x_1656_, 0);
v_value_1658_ = lean_ctor_get(v_x_1656_, 1);
v_tail_1659_ = lean_ctor_get(v_x_1656_, 2);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_x_1656_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1661_ = v_x_1656_;
v_isShared_1662_ = v_isSharedCheck_1673_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_tail_1659_);
lean_inc(v_value_1658_);
lean_inc(v_key_1657_);
lean_dec(v_x_1656_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1673_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
size_t v___x_1663_; size_t v___x_1664_; uint8_t v___x_1665_; 
v___x_1663_ = lean_ptr_addr(v_key_1657_);
v___x_1664_ = lean_ptr_addr(v_a_1654_);
v___x_1665_ = lean_usize_dec_eq(v___x_1663_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1666_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_1654_, v_b_1655_, v_tail_1659_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 2, v___x_1666_);
v___x_1668_ = v___x_1661_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_key_1657_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_value_1658_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
else
{
lean_object* v___x_1671_; 
lean_dec(v_value_1658_);
lean_dec(v_key_1657_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 1, v_b_1655_);
lean_ctor_set(v___x_1661_, 0, v_a_1654_);
v___x_1671_ = v___x_1661_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1654_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_b_1655_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v_tail_1659_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1674_, lean_object* v_x_1675_){
_start:
{
if (lean_obj_tag(v_x_1675_) == 0)
{
return v_x_1674_;
}
else
{
lean_object* v_key_1676_; lean_object* v_value_1677_; lean_object* v_tail_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1704_; 
v_key_1676_ = lean_ctor_get(v_x_1675_, 0);
v_value_1677_ = lean_ctor_get(v_x_1675_, 1);
v_tail_1678_ = lean_ctor_get(v_x_1675_, 2);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_x_1675_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1680_ = v_x_1675_;
v_isShared_1681_ = v_isSharedCheck_1704_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_tail_1678_);
lean_inc(v_value_1677_);
lean_inc(v_key_1676_);
lean_dec(v_x_1675_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1704_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; size_t v___x_1683_; size_t v___x_1684_; size_t v___x_1685_; uint64_t v___x_1686_; uint64_t v___x_1687_; uint64_t v___x_1688_; uint64_t v_fold_1689_; uint64_t v___x_1690_; uint64_t v___x_1691_; uint64_t v___x_1692_; size_t v___x_1693_; size_t v___x_1694_; size_t v___x_1695_; size_t v___x_1696_; size_t v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1682_ = lean_array_get_size(v_x_1674_);
v___x_1683_ = lean_ptr_addr(v_key_1676_);
v___x_1684_ = ((size_t)3ULL);
v___x_1685_ = lean_usize_shift_right(v___x_1683_, v___x_1684_);
v___x_1686_ = lean_usize_to_uint64(v___x_1685_);
v___x_1687_ = 32ULL;
v___x_1688_ = lean_uint64_shift_right(v___x_1686_, v___x_1687_);
v_fold_1689_ = lean_uint64_xor(v___x_1686_, v___x_1688_);
v___x_1690_ = 16ULL;
v___x_1691_ = lean_uint64_shift_right(v_fold_1689_, v___x_1690_);
v___x_1692_ = lean_uint64_xor(v_fold_1689_, v___x_1691_);
v___x_1693_ = lean_uint64_to_usize(v___x_1692_);
v___x_1694_ = lean_usize_of_nat(v___x_1682_);
v___x_1695_ = ((size_t)1ULL);
v___x_1696_ = lean_usize_sub(v___x_1694_, v___x_1695_);
v___x_1697_ = lean_usize_land(v___x_1693_, v___x_1696_);
v___x_1698_ = lean_array_uget_borrowed(v_x_1674_, v___x_1697_);
lean_inc(v___x_1698_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 2, v___x_1698_);
v___x_1700_ = v___x_1680_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_key_1676_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_value_1677_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_array_uset(v_x_1674_, v___x_1697_, v___x_1700_);
v_x_1674_ = v___x_1701_;
v_x_1675_ = v_tail_1678_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1705_, lean_object* v_source_1706_, lean_object* v_target_1707_){
_start:
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = lean_array_get_size(v_source_1706_);
v___x_1709_ = lean_nat_dec_lt(v_i_1705_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_dec_ref(v_source_1706_);
lean_dec(v_i_1705_);
return v_target_1707_;
}
else
{
lean_object* v_es_1710_; lean_object* v___x_1711_; lean_object* v_source_1712_; lean_object* v_target_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_es_1710_ = lean_array_fget(v_source_1706_, v_i_1705_);
v___x_1711_ = lean_box(0);
v_source_1712_ = lean_array_fset(v_source_1706_, v_i_1705_, v___x_1711_);
v_target_1713_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1707_, v_es_1710_);
v___x_1714_ = lean_unsigned_to_nat(1u);
v___x_1715_ = lean_nat_add(v_i_1705_, v___x_1714_);
lean_dec(v_i_1705_);
v_i_1705_ = v___x_1715_;
v_source_1706_ = v_source_1712_;
v_target_1707_ = v_target_1713_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(lean_object* v_data_1717_){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v_nbuckets_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1718_ = lean_array_get_size(v_data_1717_);
v___x_1719_ = lean_unsigned_to_nat(2u);
v_nbuckets_1720_ = lean_nat_mul(v___x_1718_, v___x_1719_);
v___x_1721_ = lean_unsigned_to_nat(0u);
v___x_1722_ = lean_box(0);
v___x_1723_ = lean_mk_array(v_nbuckets_1720_, v___x_1722_);
v___x_1724_ = lean_array_propagate_mark(v_data_1717_, v___x_1723_);
v___x_1725_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(v___x_1721_, v_data_1717_, v___x_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(lean_object* v_a_1726_, lean_object* v_x_1727_){
_start:
{
if (lean_obj_tag(v_x_1727_) == 0)
{
uint8_t v___x_1728_; 
v___x_1728_ = 0;
return v___x_1728_;
}
else
{
lean_object* v_key_1729_; lean_object* v_tail_1730_; size_t v___x_1731_; size_t v___x_1732_; uint8_t v___x_1733_; 
v_key_1729_ = lean_ctor_get(v_x_1727_, 0);
v_tail_1730_ = lean_ctor_get(v_x_1727_, 2);
v___x_1731_ = lean_ptr_addr(v_key_1729_);
v___x_1732_ = lean_ptr_addr(v_a_1726_);
v___x_1733_ = lean_usize_dec_eq(v___x_1731_, v___x_1732_);
if (v___x_1733_ == 0)
{
v_x_1727_ = v_tail_1730_;
goto _start;
}
else
{
return v___x_1733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg___boxed(lean_object* v_a_1735_, lean_object* v_x_1736_){
_start:
{
uint8_t v_res_1737_; lean_object* v_r_1738_; 
v_res_1737_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_1735_, v_x_1736_);
lean_dec(v_x_1736_);
lean_dec_ref(v_a_1735_);
v_r_1738_ = lean_box(v_res_1737_);
return v_r_1738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(lean_object* v_m_1739_, lean_object* v_a_1740_, lean_object* v_b_1741_){
_start:
{
lean_object* v_size_1742_; lean_object* v_buckets_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1789_; 
v_size_1742_ = lean_ctor_get(v_m_1739_, 0);
v_buckets_1743_ = lean_ctor_get(v_m_1739_, 1);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_m_1739_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1745_ = v_m_1739_;
v_isShared_1746_ = v_isSharedCheck_1789_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_buckets_1743_);
lean_inc(v_size_1742_);
lean_dec(v_m_1739_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1789_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; size_t v___x_1748_; size_t v___x_1749_; size_t v___x_1750_; uint64_t v___x_1751_; uint64_t v___x_1752_; uint64_t v___x_1753_; uint64_t v_fold_1754_; uint64_t v___x_1755_; uint64_t v___x_1756_; uint64_t v___x_1757_; size_t v___x_1758_; size_t v___x_1759_; size_t v___x_1760_; size_t v___x_1761_; size_t v___x_1762_; lean_object* v_bkt_1763_; uint8_t v___x_1764_; 
v___x_1747_ = lean_array_get_size(v_buckets_1743_);
v___x_1748_ = lean_ptr_addr(v_a_1740_);
v___x_1749_ = ((size_t)3ULL);
v___x_1750_ = lean_usize_shift_right(v___x_1748_, v___x_1749_);
v___x_1751_ = lean_usize_to_uint64(v___x_1750_);
v___x_1752_ = 32ULL;
v___x_1753_ = lean_uint64_shift_right(v___x_1751_, v___x_1752_);
v_fold_1754_ = lean_uint64_xor(v___x_1751_, v___x_1753_);
v___x_1755_ = 16ULL;
v___x_1756_ = lean_uint64_shift_right(v_fold_1754_, v___x_1755_);
v___x_1757_ = lean_uint64_xor(v_fold_1754_, v___x_1756_);
v___x_1758_ = lean_uint64_to_usize(v___x_1757_);
v___x_1759_ = lean_usize_of_nat(v___x_1747_);
v___x_1760_ = ((size_t)1ULL);
v___x_1761_ = lean_usize_sub(v___x_1759_, v___x_1760_);
v___x_1762_ = lean_usize_land(v___x_1758_, v___x_1761_);
v_bkt_1763_ = lean_array_uget_borrowed(v_buckets_1743_, v___x_1762_);
v___x_1764_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_1740_, v_bkt_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; lean_object* v_size_x27_1766_; lean_object* v___x_1767_; lean_object* v_buckets_x27_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1765_ = lean_unsigned_to_nat(1u);
v_size_x27_1766_ = lean_nat_add(v_size_1742_, v___x_1765_);
lean_dec(v_size_1742_);
lean_inc(v_bkt_1763_);
v___x_1767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1767_, 0, v_a_1740_);
lean_ctor_set(v___x_1767_, 1, v_b_1741_);
lean_ctor_set(v___x_1767_, 2, v_bkt_1763_);
v_buckets_x27_1768_ = lean_array_uset(v_buckets_1743_, v___x_1762_, v___x_1767_);
v___x_1769_ = lean_unsigned_to_nat(4u);
v___x_1770_ = lean_nat_mul(v_size_x27_1766_, v___x_1769_);
v___x_1771_ = lean_unsigned_to_nat(3u);
v___x_1772_ = lean_nat_div(v___x_1770_, v___x_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_array_get_size(v_buckets_x27_1768_);
v___x_1774_ = lean_nat_dec_le(v___x_1772_, v___x_1773_);
lean_dec(v___x_1772_);
if (v___x_1774_ == 0)
{
lean_object* v_val_1775_; lean_object* v___x_1777_; 
v_val_1775_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(v_buckets_x27_1768_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v_val_1775_);
lean_ctor_set(v___x_1745_, 0, v_size_x27_1766_);
v___x_1777_ = v___x_1745_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_size_x27_1766_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_val_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
else
{
lean_object* v___x_1780_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v_buckets_x27_1768_);
lean_ctor_set(v___x_1745_, 0, v_size_x27_1766_);
v___x_1780_ = v___x_1745_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_size_x27_1766_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_buckets_x27_1768_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
else
{
lean_object* v___x_1782_; lean_object* v_buckets_x27_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
lean_inc(v_bkt_1763_);
v___x_1782_ = lean_box(0);
v_buckets_x27_1783_ = lean_array_uset(v_buckets_1743_, v___x_1762_, v___x_1782_);
v___x_1784_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_1740_, v_b_1741_, v_bkt_1763_);
v___x_1785_ = lean_array_uset(v_buckets_x27_1783_, v___x_1762_, v___x_1784_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v___x_1785_);
v___x_1787_ = v___x_1745_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_size_1742_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(lean_object* v_a_1790_, lean_object* v_x_1791_){
_start:
{
if (lean_obj_tag(v_x_1791_) == 0)
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_box(0);
return v___x_1792_;
}
else
{
lean_object* v_key_1793_; lean_object* v_value_1794_; lean_object* v_tail_1795_; size_t v___x_1796_; size_t v___x_1797_; uint8_t v___x_1798_; 
v_key_1793_ = lean_ctor_get(v_x_1791_, 0);
v_value_1794_ = lean_ctor_get(v_x_1791_, 1);
v_tail_1795_ = lean_ctor_get(v_x_1791_, 2);
v___x_1796_ = lean_ptr_addr(v_key_1793_);
v___x_1797_ = lean_ptr_addr(v_a_1790_);
v___x_1798_ = lean_usize_dec_eq(v___x_1796_, v___x_1797_);
if (v___x_1798_ == 0)
{
v_x_1791_ = v_tail_1795_;
goto _start;
}
else
{
lean_object* v___x_1800_; 
lean_inc(v_value_1794_);
v___x_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1800_, 0, v_value_1794_);
return v___x_1800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_1801_, lean_object* v_x_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_1801_, v_x_1802_);
lean_dec(v_x_1802_);
lean_dec_ref(v_a_1801_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(lean_object* v_m_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_buckets_1806_; lean_object* v___x_1807_; size_t v___x_1808_; size_t v___x_1809_; size_t v___x_1810_; uint64_t v___x_1811_; uint64_t v___x_1812_; uint64_t v___x_1813_; uint64_t v_fold_1814_; uint64_t v___x_1815_; uint64_t v___x_1816_; uint64_t v___x_1817_; size_t v___x_1818_; size_t v___x_1819_; size_t v___x_1820_; size_t v___x_1821_; size_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v_buckets_1806_ = lean_ctor_get(v_m_1804_, 1);
v___x_1807_ = lean_array_get_size(v_buckets_1806_);
v___x_1808_ = lean_ptr_addr(v_a_1805_);
v___x_1809_ = ((size_t)3ULL);
v___x_1810_ = lean_usize_shift_right(v___x_1808_, v___x_1809_);
v___x_1811_ = lean_usize_to_uint64(v___x_1810_);
v___x_1812_ = 32ULL;
v___x_1813_ = lean_uint64_shift_right(v___x_1811_, v___x_1812_);
v_fold_1814_ = lean_uint64_xor(v___x_1811_, v___x_1813_);
v___x_1815_ = 16ULL;
v___x_1816_ = lean_uint64_shift_right(v_fold_1814_, v___x_1815_);
v___x_1817_ = lean_uint64_xor(v_fold_1814_, v___x_1816_);
v___x_1818_ = lean_uint64_to_usize(v___x_1817_);
v___x_1819_ = lean_usize_of_nat(v___x_1807_);
v___x_1820_ = ((size_t)1ULL);
v___x_1821_ = lean_usize_sub(v___x_1819_, v___x_1820_);
v___x_1822_ = lean_usize_land(v___x_1818_, v___x_1821_);
v___x_1823_ = lean_array_uget_borrowed(v_buckets_1806_, v___x_1822_);
v___x_1824_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_1805_, v___x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg___boxed(lean_object* v_m_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_m_1825_, v_a_1826_);
lean_dec_ref(v_a_1826_);
lean_dec_ref(v_m_1825_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(lean_object* v_e_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v___x_1831_; lean_object* v_varMap_1832_; lean_object* v___x_1833_; 
v___x_1831_ = lean_st_ref_get(v_a_1829_);
v_varMap_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc_ref(v_varMap_1832_);
lean_dec(v___x_1831_);
v___x_1833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_varMap_1832_, v_e_1828_);
lean_dec_ref(v_varMap_1832_);
if (lean_obj_tag(v___x_1833_) == 1)
{
lean_object* v_val_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1842_; 
lean_dec_ref(v_e_1828_);
v_val_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_val_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_val_1834_);
v___x_1839_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
return v___x_1840_;
}
}
}
else
{
lean_object* v___x_1843_; lean_object* v_vars_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v_varMap_1847_; lean_object* v_vars_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1860_; 
lean_dec(v___x_1833_);
v___x_1843_ = lean_st_ref_get(v_a_1829_);
v_vars_1844_ = lean_ctor_get(v___x_1843_, 1);
lean_inc_ref(v_vars_1844_);
lean_dec(v___x_1843_);
v___x_1845_ = lean_array_get_size(v_vars_1844_);
lean_dec_ref(v_vars_1844_);
v___x_1846_ = lean_st_ref_take(v_a_1829_);
v_varMap_1847_ = lean_ctor_get(v___x_1846_, 0);
v_vars_1848_ = lean_ctor_get(v___x_1846_, 1);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1850_ = v___x_1846_;
v_isShared_1851_ = v_isSharedCheck_1860_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_vars_1848_);
lean_inc(v_varMap_1847_);
lean_dec(v___x_1846_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1860_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1855_; 
lean_inc_ref(v_e_1828_);
v___x_1852_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(v_varMap_1847_, v_e_1828_, v___x_1845_);
v___x_1853_ = lean_array_push(v_vars_1848_, v_e_1828_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 1, v___x_1853_);
lean_ctor_set(v___x_1850_, 0, v___x_1852_);
v___x_1855_ = v___x_1850_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = lean_st_ref_put(v_a_1829_, v___x_1855_);
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1845_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg___boxed(lean_object* v_e_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1861_, v_a_1862_);
lean_dec(v_a_1862_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(lean_object* v_e_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1865_, v_a_1866_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___boxed(lean_object* v_e_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(v_e_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
lean_dec(v_a_1884_);
lean_dec(v_a_1883_);
lean_dec(v_a_1882_);
lean_dec(v_a_1881_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0(lean_object* v_00_u03b2_1895_, lean_object* v_m_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_m_1896_, v_a_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___boxed(lean_object* v_00_u03b2_1899_, lean_object* v_m_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0(v_00_u03b2_1899_, v_m_1900_, v_a_1901_);
lean_dec_ref(v_a_1901_);
lean_dec_ref(v_m_1900_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1(lean_object* v_00_u03b2_1903_, lean_object* v_m_1904_, lean_object* v_a_1905_, lean_object* v_b_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(v_m_1904_, v_a_1905_, v_b_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0(lean_object* v_00_u03b2_1908_, lean_object* v_a_1909_, lean_object* v_x_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_1909_, v_x_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1912_, lean_object* v_a_1913_, lean_object* v_x_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0(v_00_u03b2_1912_, v_a_1913_, v_x_1914_);
lean_dec(v_x_1914_);
lean_dec_ref(v_a_1913_);
return v_res_1915_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(lean_object* v_00_u03b2_1916_, lean_object* v_a_1917_, lean_object* v_x_1918_){
_start:
{
uint8_t v___x_1919_; 
v___x_1919_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_1917_, v_x_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1920_, lean_object* v_a_1921_, lean_object* v_x_1922_){
_start:
{
uint8_t v_res_1923_; lean_object* v_r_1924_; 
v_res_1923_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(v_00_u03b2_1920_, v_a_1921_, v_x_1922_);
lean_dec(v_x_1922_);
lean_dec_ref(v_a_1921_);
v_r_1924_ = lean_box(v_res_1923_);
return v_r_1924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3(lean_object* v_00_u03b2_1925_, lean_object* v_data_1926_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(v_data_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4(lean_object* v_00_u03b2_1928_, lean_object* v_a_1929_, lean_object* v_b_1930_, lean_object* v_x_1931_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_1929_, v_b_1930_, v_x_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1933_, lean_object* v_i_1934_, lean_object* v_source_1935_, lean_object* v_target_1936_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(v_i_1934_, v_source_1935_, v_target_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1938_, lean_object* v_x_1939_, lean_object* v_x_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1939_, v_x_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(lean_object* v_e_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1958_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1956_, 1);
lean_inc_ref(v_e_1942_);
v___x_1958_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1942_, v_a_1952_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_2059_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_2059_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_2059_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1963_ = l_Lean_Expr_cleanupAnnotations(v_a_1959_);
v___x_1964_ = l_Lean_Expr_isApp(v___x_1963_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; 
lean_dec_ref(v___x_1963_);
lean_del_object(v___x_1961_);
lean_dec(v_a_1957_);
v___x_1965_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1942_, v_a_1943_);
return v___x_1965_;
}
else
{
lean_object* v_arg_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v_arg_1966_ = lean_ctor_get(v___x_1963_, 1);
lean_inc_ref(v_arg_1966_);
v___x_1967_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1963_);
v___x_1968_ = l_Lean_Expr_isApp(v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; 
lean_dec_ref(v___x_1967_);
lean_dec_ref(v_arg_1966_);
lean_del_object(v___x_1961_);
lean_dec(v_a_1957_);
v___x_1969_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1942_, v_a_1943_);
return v___x_1969_;
}
else
{
lean_object* v_arg_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; 
v_arg_1970_ = lean_ctor_get(v___x_1967_, 1);
lean_inc_ref(v_arg_1970_);
v___x_1971_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1967_);
v___x_1972_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2));
v___x_1973_ = l_Lean_Expr_isConstOf(v___x_1971_, v___x_1972_);
if (v___x_1973_ == 0)
{
uint8_t v___x_1974_; 
lean_del_object(v___x_1961_);
v___x_1974_ = l_Lean_Expr_isApp(v___x_1971_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; 
lean_dec_ref(v___x_1971_);
lean_dec_ref(v_arg_1970_);
lean_dec_ref(v_arg_1966_);
lean_dec(v_a_1957_);
v___x_1975_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1942_, v_a_1943_);
return v___x_1975_;
}
else
{
lean_object* v_arg_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v_arg_1976_ = lean_ctor_get(v___x_1971_, 1);
lean_inc_ref(v_arg_1976_);
v___x_1977_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1971_);
v___x_1978_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5));
v___x_1979_ = l_Lean_Expr_isConstOf(v___x_1977_, v___x_1978_);
if (v___x_1979_ == 0)
{
uint8_t v___x_1980_; 
v___x_1980_ = l_Lean_Expr_isApp(v___x_1977_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; 
lean_dec_ref(v___x_1977_);
lean_dec_ref(v_arg_1976_);
lean_dec_ref(v_arg_1970_);
lean_dec_ref(v_arg_1966_);
lean_dec(v_a_1957_);
v___x_1981_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1942_, v_a_1943_);
return v___x_1981_;
}
else
{
lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1982_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1977_);
v___x_1983_ = l_Lean_Expr_isApp(v___x_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; 
lean_dec_ref(v___x_1982_);
lean_dec_ref(v_arg_1976_);
lean_dec_ref(v_arg_1970_);
lean_dec_ref(v_arg_1966_);
lean_dec(v_a_1957_);
v___x_1984_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1942_, v_a_1943_);
return v___x_1984_;
}
else
{
lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1985_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1982_);
v___x_1986_ = l_Lean_Expr_isApp(v___x_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; 
lean_dec_ref(v___x_1985_);
lean_dec_ref(v_arg_1976_);
lean_dec_ref(v_arg_1970_);
lean_dec_ref(v_arg_1966_);
lean_dec(v_a_1957_);
v___x_1987_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1942_, v_a_1943_);
return v___x_1987_;
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1988_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1985_);
v___x_1989_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8));
v___x_1990_ = l_Lean_Expr_isConstOf(v___x_1988_, v___x_1989_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; uint8_t v___x_1992_; 
v___x_1991_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11));
v___x_1992_ = l_Lean_Expr_isConstOf(v___x_1988_, v___x_1991_);
lean_dec_ref(v___x_1988_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; 
lean_dec_ref(v_arg_1976_);
lean_dec_ref(v_arg_1970_);
lean_dec_ref(v_arg_1966_);
lean_dec(v_a_1957_);
v___x_1993_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1942_, v_a_1943_);
return v___x_1993_;
}
else
{
uint8_t v___x_1994_; 
v___x_1994_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_1957_, v_arg_1976_);
lean_dec_ref(v_arg_1976_);
lean_dec(v_a_1957_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; 
lean_dec_ref(v_arg_1970_);
lean_dec_ref(v_arg_1966_);
v___x_1995_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1942_, v_a_1943_);
return v___x_1995_;
}
else
{
lean_object* v___x_1996_; 
lean_dec_ref(v_e_1942_);
v___x_1996_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_1970_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1998_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v___x_1998_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_1966_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2007_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2007_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2007_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2003_, 0, v_a_1997_);
lean_ctor_set(v___x_2003_, 1, v_a_1999_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2003_);
v___x_2005_ = v___x_2001_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
else
{
lean_dec(v_a_1997_);
return v___x_1998_;
}
}
else
{
lean_dec_ref(v_arg_1966_);
return v___x_1996_;
}
}
}
}
else
{
uint8_t v___x_2008_; 
lean_dec_ref(v___x_1988_);
v___x_2008_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_a_1957_, v_arg_1976_);
lean_dec_ref(v_arg_1976_);
lean_dec(v_a_1957_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
lean_dec_ref(v_arg_1970_);
lean_dec_ref(v_arg_1966_);
v___x_2009_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1942_, v_a_1943_);
return v___x_2009_;
}
else
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_Meta_getNatValue_x3f(v_arg_1970_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
lean_dec_ref(v_arg_1970_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
if (lean_obj_tag(v_a_2011_) == 1)
{
lean_object* v_val_2012_; lean_object* v___x_2013_; 
lean_dec_ref(v_e_1942_);
v_val_2012_ = lean_ctor_get(v_a_2011_, 0);
lean_inc(v_val_2012_);
lean_dec_ref_known(v_a_2011_, 1);
v___x_2013_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_1966_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2022_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2016_ = v___x_2013_;
v_isShared_2017_ = v_isSharedCheck_2022_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2013_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2022_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2018_, 0, v_val_2012_);
lean_ctor_set(v___x_2018_, 1, v_a_2014_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2018_);
v___x_2020_ = v___x_2016_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
else
{
lean_dec(v_val_2012_);
return v___x_2013_;
}
}
else
{
lean_object* v___x_2023_; 
lean_dec(v_a_2011_);
lean_dec_ref(v_arg_1966_);
v___x_2023_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1942_, v_a_1943_);
return v___x_2023_;
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec_ref(v_arg_1966_);
lean_dec_ref(v_e_1942_);
v_a_2024_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2010_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2010_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_zero_2032_; lean_object* v___x_2033_; 
lean_dec_ref(v___x_1977_);
lean_dec_ref(v_arg_1976_);
lean_dec_ref(v_arg_1970_);
lean_dec_ref(v_arg_1966_);
v_zero_2032_ = lean_ctor_get(v_a_1957_, 13);
lean_inc_ref(v_zero_2032_);
lean_dec(v_a_1957_);
lean_inc_ref(v_e_1942_);
v___x_2033_ = l_Lean_Meta_isDefEqD(v_e_1942_, v_zero_2032_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2044_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2036_ = v___x_2033_;
v_isShared_2037_ = v_isSharedCheck_2044_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2044_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
uint8_t v___x_2038_; 
v___x_2038_ = lean_unbox(v_a_2034_);
lean_dec(v_a_2034_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; 
lean_del_object(v___x_2036_);
v___x_2039_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1942_, v_a_1943_);
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
lean_dec_ref(v_e_1942_);
v___x_2040_ = lean_box(0);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2040_);
v___x_2042_ = v___x_2036_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec_ref(v_e_1942_);
v_a_2045_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2033_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2033_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
}
else
{
uint8_t v___x_2053_; 
lean_dec_ref(v___x_1971_);
lean_dec_ref(v_arg_1970_);
v___x_2053_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_1957_, v_arg_1966_);
lean_dec_ref(v_arg_1966_);
lean_dec(v_a_1957_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; 
lean_del_object(v___x_1961_);
v___x_2054_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1942_, v_a_1943_);
return v___x_2054_;
}
else
{
lean_object* v___x_2055_; lean_object* v___x_2057_; 
lean_dec_ref(v_e_1942_);
v___x_2055_ = lean_box(0);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_2055_);
v___x_2057_ = v___x_1961_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v_a_1957_);
lean_dec_ref(v_e_1942_);
v_a_2060_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_1958_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_1958_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec_ref(v_e_1942_);
v_a_2068_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_1956_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_1956_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify___boxed(lean_object* v_e_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_e_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
lean_dec(v_a_2088_);
lean_dec_ref(v_a_2087_);
lean_dec(v_a_2086_);
lean_dec_ref(v_a_2085_);
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec(v_a_2078_);
lean_dec(v_a_2077_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(lean_object* v___y_2091_){
_start:
{
lean_inc_ref(v___y_2091_);
return v___y_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___boxed(lean_object* v___y_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(v___y_2092_);
lean_dec_ref(v___y_2092_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2(lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_b_2105_, lean_object* v_ctx_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v_type_2120_; lean_object* v_u_2121_; lean_object* v_natModuleInst_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_type_2120_ = lean_ctor_get(v_a_2101_, 2);
lean_inc_ref(v_type_2120_);
v_u_2121_ = lean_ctor_get(v_a_2101_, 3);
lean_inc(v_u_2121_);
v_natModuleInst_2122_ = lean_ctor_get(v_a_2101_, 4);
lean_inc_ref(v_natModuleInst_2122_);
lean_dec_ref(v_a_2101_);
v___x_2123_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__2));
v___x_2124_ = lean_box(0);
v___x_2125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2125_, 0, v_u_2121_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = l_Lean_mkConst(v___x_2123_, v___x_2125_);
v___x_2127_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_2102_);
v___x_2128_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_2103_);
v___x_2129_ = l_Lean_eagerReflBoolTrue;
v___x_2130_ = l_Lean_mkApp6(v___x_2126_, v_type_2120_, v_natModuleInst_2122_, v_ctx_2106_, v___x_2127_, v___x_2128_, v___x_2129_);
v___x_2131_ = l_Lean_Meta_Grind_mkDiseqProof(v_a_2104_, v_b_2105_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
v___x_2133_ = l_Lean_Expr_app___override(v_a_2132_, v___x_2130_);
v___x_2134_ = l_Lean_Meta_Grind_closeGoal(v___x_2133_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
return v___x_2134_;
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec_ref(v___x_2130_);
v_a_2135_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2131_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2131_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___boxed(lean_object** _args){
lean_object* v_a_2143_ = _args[0];
lean_object* v_a_2144_ = _args[1];
lean_object* v_a_2145_ = _args[2];
lean_object* v_a_2146_ = _args[3];
lean_object* v_b_2147_ = _args[4];
lean_object* v_ctx_2148_ = _args[5];
lean_object* v___y_2149_ = _args[6];
lean_object* v___y_2150_ = _args[7];
lean_object* v___y_2151_ = _args[8];
lean_object* v___y_2152_ = _args[9];
lean_object* v___y_2153_ = _args[10];
lean_object* v___y_2154_ = _args[11];
lean_object* v___y_2155_ = _args[12];
lean_object* v___y_2156_ = _args[13];
lean_object* v___y_2157_ = _args[14];
lean_object* v___y_2158_ = _args[15];
lean_object* v___y_2159_ = _args[16];
lean_object* v___y_2160_ = _args[17];
lean_object* v___y_2161_ = _args[18];
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2(v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_b_2147_, v_ctx_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec(v___y_2149_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(lean_object* v_vars_2163_, lean_object* v_x_2164_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_array_fget_borrowed(v_vars_2163_, v_x_2164_);
lean_inc(v___x_2165_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1___boxed(lean_object* v_vars_2166_, lean_object* v_x_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(v_vars_2166_, v_x_2167_);
lean_dec(v_x_2167_);
lean_dec_ref(v_vars_2166_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(lean_object* v_a_2170_, lean_object* v_b_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_){
_start:
{
lean_object* v___f_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v_a_2189_; lean_object* v___y_2193_; lean_object* v___x_2195_; 
v___f_2184_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0));
v___x_2185_ = lean_unsigned_to_nat(0u);
v___x_2186_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
v___x_2187_ = lean_st_mk_ref(v___x_2186_);
lean_inc_ref(v_a_2170_);
v___x_2195_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_a_2170_, v___x_2187_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2197_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2195_, 1);
lean_inc_ref(v_b_2171_);
v___x_2197_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_b_2171_, v___x_2187_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc_n(v_a_2198_, 2);
lean_dec_ref_known(v___x_2197_, 1);
lean_inc(v_a_2196_);
v___x_2199_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_2196_);
v___x_2200_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_2198_);
v___x_2201_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_2199_, v___x_2200_);
lean_dec(v___x_2200_);
lean_dec(v___x_2199_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; 
lean_dec(v_a_2198_);
lean_dec(v_a_2196_);
lean_dec_ref(v_b_2171_);
lean_dec_ref(v_a_2170_);
v___x_2202_ = lean_box(0);
v_a_2189_ = v___x_2202_;
goto v___jp_2188_;
}
else
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2205_; lean_object* v_vars_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v___x_2205_ = lean_st_ref_get(v___x_2187_);
v_vars_2206_ = lean_ctor_get(v___x_2205_, 1);
lean_inc_ref(v_vars_2206_);
lean_dec(v___x_2205_);
v___x_2207_ = lean_array_get_size(v_vars_2206_);
v___x_2208_ = lean_nat_dec_lt(v___x_2185_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_object* v_type_2209_; lean_object* v_zero_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
lean_dec_ref(v_vars_2206_);
v_type_2209_ = lean_ctor_get(v_a_2204_, 2);
v_zero_2210_ = lean_ctor_get(v_a_2204_, 13);
lean_inc_ref(v_zero_2210_);
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v_zero_2210_);
lean_inc_ref(v_type_2209_);
v___x_2212_ = l_Lean_RArray_toExpr___redArg(v_type_2209_, v___f_2184_, v___x_2211_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2214_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v___x_2212_, 1);
v___x_2214_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2(v_a_2204_, v_a_2196_, v_a_2198_, v_a_2170_, v_b_2171_, v_a_2213_, v___x_2187_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
v___y_2193_ = v___x_2214_;
goto v___jp_2192_;
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec(v_a_2204_);
lean_dec(v_a_2198_);
lean_dec(v_a_2196_);
lean_dec(v___x_2187_);
lean_dec_ref(v_b_2171_);
lean_dec_ref(v_a_2170_);
v_a_2215_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2212_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2212_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
else
{
lean_object* v_type_2223_; lean_object* v___f_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v_type_2223_ = lean_ctor_get(v_a_2204_, 2);
v___f_2224_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2224_, 0, v_vars_2206_);
v___x_2225_ = l_Lean_RArray_ofFn___redArg(v___x_2207_, v___f_2224_);
lean_inc_ref(v_type_2223_);
v___x_2226_ = l_Lean_RArray_toExpr___redArg(v_type_2223_, v___f_2184_, v___x_2225_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2228_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v___x_2228_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2(v_a_2204_, v_a_2196_, v_a_2198_, v_a_2170_, v_b_2171_, v_a_2227_, v___x_2187_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
v___y_2193_ = v___x_2228_;
goto v___jp_2192_;
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec(v_a_2204_);
lean_dec(v_a_2198_);
lean_dec(v_a_2196_);
lean_dec(v___x_2187_);
lean_dec_ref(v_b_2171_);
lean_dec_ref(v_a_2170_);
v_a_2229_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2226_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2226_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_dec(v_a_2198_);
lean_dec(v_a_2196_);
lean_dec(v___x_2187_);
lean_dec_ref(v_b_2171_);
lean_dec_ref(v_a_2170_);
v_a_2237_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2203_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2203_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec(v_a_2196_);
lean_dec(v___x_2187_);
lean_dec_ref(v_b_2171_);
lean_dec_ref(v_a_2170_);
v_a_2245_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2197_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2197_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec(v___x_2187_);
lean_dec_ref(v_b_2171_);
lean_dec_ref(v_a_2170_);
v_a_2253_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2195_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2195_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
v___jp_2188_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_st_ref_get(v___x_2187_);
lean_dec(v___x_2187_);
lean_dec(v___x_2190_);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v_a_2189_);
return v___x_2191_;
}
v___jp_2192_:
{
if (lean_obj_tag(v___y_2193_) == 0)
{
lean_object* v_a_2194_; 
v_a_2194_ = lean_ctor_get(v___y_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___y_2193_, 1);
v_a_2189_ = v_a_2194_;
goto v___jp_2188_;
}
else
{
lean_dec(v___x_2187_);
return v___y_2193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___boxed(lean_object* v_a_2261_, lean_object* v_b_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_2261_, v_b_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
lean_dec(v_a_2273_);
lean_dec_ref(v_a_2272_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec(v_a_2264_);
lean_dec(v_a_2263_);
return v_res_2275_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_OfNatModule(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_NatModuleNorm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_RArray(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Module_OfNatModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Module_NatModuleNorm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* initialize_Init_Grind_Module_OfNatModule(uint8_t builtin);
lean_object* initialize_Init_Grind_Module_NatModuleNorm(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Lean_Data_RArray(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Module_OfNatModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Module_NatModuleNorm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
}
#ifdef __cplusplus
}
#endif
