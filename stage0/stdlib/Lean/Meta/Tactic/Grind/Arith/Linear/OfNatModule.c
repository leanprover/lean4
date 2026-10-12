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
lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg(lean_object* v_natStructId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_natStructId_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_a_9_ = stack[8].m_obj;
lean_object* v_a_10_ = stack[9].m_obj;
lean_object* v_a_11_ = stack[10].m_obj;
lean_object* v_a_12_ = stack[11].m_obj;
lean_object* v_res_15_;
v_res_15_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg(v_natStructId_1_, v_x_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg___boxed(lean_object* v_natStructId_16_, lean_object* v_x_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg(v_natStructId_16_, v_x_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
lean_dec(v_a_25_);
lean_dec_ref(v_a_24_);
lean_dec(v_a_23_);
lean_dec_ref(v_a_22_);
lean_dec(v_a_21_);
lean_dec_ref(v_a_20_);
lean_dec(v_a_19_);
lean_dec(v_a_18_);
return v_res_29_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run(lean_object* v_00_u03b1_30_, lean_object* v_natStructId_31_, lean_object* v_x_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v___x_44_; 
lean_inc(v_a_42_);
lean_inc_ref(v_a_41_);
lean_inc(v_a_40_);
lean_inc_ref(v_a_39_);
lean_inc(v_a_38_);
lean_inc_ref(v_a_37_);
lean_inc(v_a_36_);
lean_inc_ref(v_a_35_);
lean_inc(v_a_34_);
lean_inc(v_a_33_);
v___x_44_ = lean_apply_12(v_x_32_, v_natStructId_31_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, lean_box(0));
return v___x_44_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_natStructId_31_ = stack[1].m_obj;
lean_object* v_x_32_ = stack[2].m_obj;
lean_object* v_a_33_ = stack[3].m_obj;
lean_object* v_a_34_ = stack[4].m_obj;
lean_object* v_a_35_ = stack[5].m_obj;
lean_object* v_a_36_ = stack[6].m_obj;
lean_object* v_a_37_ = stack[7].m_obj;
lean_object* v_a_38_ = stack[8].m_obj;
lean_object* v_a_39_ = stack[9].m_obj;
lean_object* v_a_40_ = stack[10].m_obj;
lean_object* v_a_41_ = stack[11].m_obj;
lean_object* v_a_42_ = stack[12].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run(lean_box(0), v_natStructId_31_, v_x_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___boxed(lean_object* v_00_u03b1_46_, lean_object* v_natStructId_47_, lean_object* v_x_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run(v_00_u03b1_46_, v_natStructId_47_, v_x_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec(v_a_49_);
return v_res_60_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg(lean_object* v_a_61_){
_start:
{
lean_object* v___x_63_; 
lean_inc(v_a_61_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v_a_61_);
return v___x_63_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_61_ = stack[0].m_obj;
lean_object* v_res_64_;
v_res_64_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg(v_a_61_);
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg___boxed(lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg(v_a_65_);
lean_dec(v_a_65_);
return v_res_67_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId(lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_80_; 
lean_inc(v_a_68_);
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v_a_68_);
return v___x_80_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getNatStructId_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_68_ = stack[0].m_obj;
lean_object* v_a_69_ = stack[1].m_obj;
lean_object* v_a_70_ = stack[2].m_obj;
lean_object* v_a_71_ = stack[3].m_obj;
lean_object* v_a_72_ = stack[4].m_obj;
lean_object* v_a_73_ = stack[5].m_obj;
lean_object* v_a_74_ = stack[6].m_obj;
lean_object* v_a_75_ = stack[7].m_obj;
lean_object* v_a_76_ = stack[8].m_obj;
lean_object* v_a_77_ = stack[9].m_obj;
lean_object* v_a_78_ = stack[10].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId(v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId___boxed(lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId(v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec(v_a_83_);
lean_dec(v_a_82_);
return v_res_94_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(lean_object* v_msgData_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v___x_101_; lean_object* v_env_102_; uint8_t v___x_103_; lean_object* v_env_104_; lean_object* v___x_105_; lean_object* v_toCold_106_; lean_object* v_mctx_107_; lean_object* v_lctx_108_; lean_object* v_options_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_101_ = lean_st_ref_get(v___y_99_);
v_env_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc_ref(v_env_102_);
lean_dec(v___x_101_);
v___x_103_ = 0;
v_env_104_ = l_Lean_Environment_setRecordingDeps(v_env_102_, v___x_103_);
v___x_105_ = lean_st_ref_get(v___y_97_);
v_toCold_106_ = lean_ctor_get(v___y_98_, 0);
v_mctx_107_ = lean_ctor_get(v___x_105_, 0);
lean_inc_ref(v_mctx_107_);
lean_dec(v___x_105_);
v_lctx_108_ = lean_ctor_get(v___y_96_, 2);
v_options_109_ = lean_ctor_get(v_toCold_106_, 2);
lean_inc_ref(v_options_109_);
lean_inc_ref(v_lctx_108_);
v___x_110_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_110_, 0, v_env_104_);
lean_ctor_set(v___x_110_, 1, v_mctx_107_);
lean_ctor_set(v___x_110_, 2, v_lctx_108_);
lean_ctor_set(v___x_110_, 3, v_options_109_);
v___x_111_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_msgData_95_);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_95_ = stack[0].m_obj;
lean_object* v___y_96_ = stack[1].m_obj;
lean_object* v___y_97_ = stack[2].m_obj;
lean_object* v___y_98_ = stack[3].m_obj;
lean_object* v___y_99_ = stack[4].m_obj;
lean_object* v_res_113_;
v_res_113_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(v_msgData_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0___boxed(lean_object* v_msgData_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(v_msgData_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
return v_res_120_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(lean_object* v_msg_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_ref_127_; lean_object* v___x_128_; lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_137_; 
v_ref_127_ = lean_ctor_get(v___y_124_, 2);
v___x_128_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(v_msg_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
v_a_129_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_137_ == 0)
{
v___x_131_ = v___x_128_;
v_isShared_132_ = v_isSharedCheck_137_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_128_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_137_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v___x_135_; 
lean_inc(v_ref_127_);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v_ref_127_);
lean_ctor_set(v___x_133_, 1, v_a_129_);
if (v_isShared_132_ == 0)
{
lean_ctor_set_tag(v___x_131_, 1);
lean_ctor_set(v___x_131_, 0, v___x_133_);
v___x_135_ = v___x_131_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_121_ = stack[0].m_obj;
lean_object* v___y_122_ = stack[1].m_obj;
lean_object* v___y_123_ = stack[2].m_obj;
lean_object* v___y_124_ = stack[3].m_obj;
lean_object* v___y_125_ = stack[4].m_obj;
lean_object* v_res_138_;
v_res_138_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(v_msg_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg___boxed(lean_object* v_msg_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(v_msg_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
return v_res_145_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0));
v___x_148_ = l_Lean_stringToMessageData(v___x_147_);
return v___x_148_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct(lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_150_, v_a_158_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_175_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_175_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_175_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_175_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v_natStructs_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_natStructs_166_ = lean_ctor_get(v_a_162_, 5);
lean_inc_ref(v_natStructs_166_);
lean_dec(v_a_162_);
v___x_167_ = lean_array_get_size(v_natStructs_166_);
v___x_168_ = lean_nat_dec_lt(v_a_149_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec_ref(v_natStructs_166_);
lean_del_object(v___x_164_);
v___x_169_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1);
v___x_170_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(v___x_169_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_171_ = lean_array_fget(v_natStructs_166_, v_a_149_);
lean_dec_ref(v_natStructs_166_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_171_);
v___x_173_ = v___x_164_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
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
v_a_176_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_161_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_161_);
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
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getNatStruct_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_149_ = stack[0].m_obj;
lean_object* v_a_150_ = stack[1].m_obj;
lean_object* v_a_151_ = stack[2].m_obj;
lean_object* v_a_152_ = stack[3].m_obj;
lean_object* v_a_153_ = stack[4].m_obj;
lean_object* v_a_154_ = stack[5].m_obj;
lean_object* v_a_155_ = stack[6].m_obj;
lean_object* v_a_156_ = stack[7].m_obj;
lean_object* v_a_157_ = stack[8].m_obj;
lean_object* v_a_158_ = stack[9].m_obj;
lean_object* v_a_159_ = stack[10].m_obj;
lean_object* v_res_184_;
v_res_184_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct___boxed(lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec(v_a_186_);
lean_dec(v_a_185_);
return v_res_197_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0(lean_object* v_00_u03b1_198_, lean_object* v_msg_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(v_msg_199_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
return v___x_212_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_199_ = stack[1].m_obj;
lean_object* v___y_200_ = stack[2].m_obj;
lean_object* v___y_201_ = stack[3].m_obj;
lean_object* v___y_202_ = stack[4].m_obj;
lean_object* v___y_203_ = stack[5].m_obj;
lean_object* v___y_204_ = stack[6].m_obj;
lean_object* v___y_205_ = stack[7].m_obj;
lean_object* v___y_206_ = stack[8].m_obj;
lean_object* v___y_207_ = stack[9].m_obj;
lean_object* v___y_208_ = stack[10].m_obj;
lean_object* v___y_209_ = stack[11].m_obj;
lean_object* v___y_210_ = stack[12].m_obj;
lean_object* v_res_213_;
v_res_213_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0(lean_box(0), v_msg_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
stack->m_obj
 = v_res_213_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___boxed(lean_object* v_00_u03b1_214_, lean_object* v_msg_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0(v_00_u03b1_214_, v_msg_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec(v___y_217_);
lean_dec(v___y_216_);
return v_res_228_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v_structId_243_; lean_object* v___x_244_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_a_242_);
lean_dec_ref_known(v___x_241_, 1);
v_structId_243_ = lean_ctor_get(v_a_242_, 1);
lean_inc(v_structId_243_);
lean_dec(v_a_242_);
v___x_244_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_structId_243_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
lean_dec(v_structId_243_);
return v___x_244_;
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
v_a_245_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_241_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_241_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_229_ = stack[0].m_obj;
lean_object* v_a_230_ = stack[1].m_obj;
lean_object* v_a_231_ = stack[2].m_obj;
lean_object* v_a_232_ = stack[3].m_obj;
lean_object* v_a_233_ = stack[4].m_obj;
lean_object* v_a_234_ = stack[5].m_obj;
lean_object* v_a_235_ = stack[6].m_obj;
lean_object* v_a_236_ = stack[7].m_obj;
lean_object* v_a_237_ = stack[8].m_obj;
lean_object* v_a_238_ = stack[9].m_obj;
lean_object* v_a_239_ = stack[10].m_obj;
lean_object* v_res_253_;
v_res_253_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct___boxed(lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec(v_a_255_);
lean_dec(v_a_254_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0(lean_object* v_a_268_, lean_object* v_f_269_, lean_object* v_s_270_){
_start:
{
lean_object* v_structs_271_; lean_object* v_typeIdOf_272_; lean_object* v_exprToStructId_273_; lean_object* v_exprToStructIdEntries_274_; lean_object* v_forbiddenNatModules_275_; lean_object* v_natStructs_276_; lean_object* v_natTypeIdOf_277_; lean_object* v_exprToNatStructId_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v_structs_271_ = lean_ctor_get(v_s_270_, 0);
v_typeIdOf_272_ = lean_ctor_get(v_s_270_, 1);
v_exprToStructId_273_ = lean_ctor_get(v_s_270_, 2);
v_exprToStructIdEntries_274_ = lean_ctor_get(v_s_270_, 3);
v_forbiddenNatModules_275_ = lean_ctor_get(v_s_270_, 4);
v_natStructs_276_ = lean_ctor_get(v_s_270_, 5);
v_natTypeIdOf_277_ = lean_ctor_get(v_s_270_, 6);
v_exprToNatStructId_278_ = lean_ctor_get(v_s_270_, 7);
v___x_279_ = lean_array_get_size(v_natStructs_276_);
v___x_280_ = lean_nat_dec_lt(v_a_268_, v___x_279_);
if (v___x_280_ == 0)
{
lean_dec_ref(v_f_269_);
return v_s_270_;
}
else
{
lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_292_; 
lean_inc_ref(v_exprToNatStructId_278_);
lean_inc_ref(v_natTypeIdOf_277_);
lean_inc_ref(v_natStructs_276_);
lean_inc_ref(v_forbiddenNatModules_275_);
lean_inc_ref(v_exprToStructIdEntries_274_);
lean_inc_ref(v_exprToStructId_273_);
lean_inc_ref(v_typeIdOf_272_);
lean_inc_ref(v_structs_271_);
v_isSharedCheck_292_ = !lean_is_exclusive(v_s_270_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; lean_object* v_unused_294_; lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; lean_object* v_unused_298_; lean_object* v_unused_299_; lean_object* v_unused_300_; 
v_unused_293_ = lean_ctor_get(v_s_270_, 7);
lean_dec(v_unused_293_);
v_unused_294_ = lean_ctor_get(v_s_270_, 6);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v_s_270_, 5);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_s_270_, 4);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_s_270_, 3);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_s_270_, 2);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_s_270_, 1);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_s_270_, 0);
lean_dec(v_unused_300_);
v___x_282_ = v_s_270_;
v_isShared_283_ = v_isSharedCheck_292_;
goto v_resetjp_281_;
}
else
{
lean_dec(v_s_270_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_292_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v_v_284_; lean_object* v___x_285_; lean_object* v_xs_x27_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v_v_284_ = lean_array_fget(v_natStructs_276_, v_a_268_);
v___x_285_ = lean_box(0);
v_xs_x27_286_ = lean_array_fset(v_natStructs_276_, v_a_268_, v___x_285_);
v___x_287_ = lean_apply_1(v_f_269_, v_v_284_);
v___x_288_ = lean_array_fset(v_xs_x27_286_, v_a_268_, v___x_287_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 5, v___x_288_);
v___x_290_ = v___x_282_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_structs_271_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_typeIdOf_272_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_exprToStructId_273_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v_exprToStructIdEntries_274_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v_forbiddenNatModules_275_);
lean_ctor_set(v_reuseFailAlloc_291_, 5, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_291_, 6, v_natTypeIdOf_277_);
lean_ctor_set(v_reuseFailAlloc_291_, 7, v_exprToNatStructId_278_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed(lean_object* v_a_301_, lean_object* v_f_302_, lean_object* v_s_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0(v_a_301_, v_f_302_, v_s_303_);
lean_dec(v_a_301_);
return v_res_304_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg(lean_object* v_f_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___f_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
lean_inc(v_a_306_);
v___f_309_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_309_, 0, v_a_306_);
lean_closure_set(v___f_309_, 1, v_f_305_);
v___x_310_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_311_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_310_, v___f_309_, v_a_307_);
return v___x_311_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_305_ = stack[0].m_obj;
lean_object* v_a_306_ = stack[1].m_obj;
lean_object* v_a_307_ = stack[2].m_obj;
lean_object* v_res_312_;
v_res_312_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg(v_f_305_, v_a_306_, v_a_307_);
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___boxed(lean_object* v_f_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg(v_f_313_, v_a_314_, v_a_315_);
lean_dec(v_a_315_);
lean_dec(v_a_314_);
return v_res_317_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct(lean_object* v_f_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___f_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
lean_inc(v_a_319_);
v___f_331_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_331_, 0, v_a_319_);
lean_closure_set(v___f_331_, 1, v_f_318_);
v___x_332_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_333_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_332_, v___f_331_, v_a_320_);
return v___x_333_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_318_ = stack[0].m_obj;
lean_object* v_a_319_ = stack[1].m_obj;
lean_object* v_a_320_ = stack[2].m_obj;
lean_object* v_a_321_ = stack[3].m_obj;
lean_object* v_a_322_ = stack[4].m_obj;
lean_object* v_a_323_ = stack[5].m_obj;
lean_object* v_a_324_ = stack[6].m_obj;
lean_object* v_a_325_ = stack[7].m_obj;
lean_object* v_a_326_ = stack[8].m_obj;
lean_object* v_a_327_ = stack[9].m_obj;
lean_object* v_a_328_ = stack[10].m_obj;
lean_object* v_a_329_ = stack[11].m_obj;
lean_object* v_res_334_;
v_res_334_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct(v_f_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
stack->m_obj
 = v_res_334_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___boxed(lean_object* v_f_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct(v_f_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec(v_a_337_);
lean_dec(v_a_336_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_349_, lean_object* v_vals_350_, lean_object* v_i_351_, lean_object* v_k_352_){
_start:
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = lean_array_get_size(v_keys_349_);
v___x_354_ = lean_nat_dec_lt(v_i_351_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
lean_dec(v_i_351_);
v___x_355_ = lean_box(0);
return v___x_355_;
}
else
{
lean_object* v_k_x27_356_; size_t v___x_357_; size_t v___x_358_; uint8_t v___x_359_; 
v_k_x27_356_ = lean_array_fget_borrowed(v_keys_349_, v_i_351_);
v___x_357_ = lean_ptr_addr(v_k_352_);
v___x_358_ = lean_ptr_addr(v_k_x27_356_);
v___x_359_ = lean_usize_dec_eq(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_unsigned_to_nat(1u);
v___x_361_ = lean_nat_add(v_i_351_, v___x_360_);
lean_dec(v_i_351_);
v_i_351_ = v___x_361_;
goto _start;
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_array_fget_borrowed(v_vals_350_, v_i_351_);
lean_dec(v_i_351_);
lean_inc(v___x_363_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_365_, lean_object* v_vals_366_, lean_object* v_i_367_, lean_object* v_k_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_365_, v_vals_366_, v_i_367_, v_k_368_);
lean_dec_ref(v_k_368_);
lean_dec_ref(v_vals_366_);
lean_dec_ref(v_keys_365_);
return v_res_369_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_370_, size_t v_x_371_, lean_object* v_x_372_){
_start:
{
if (lean_obj_tag(v_x_370_) == 0)
{
lean_object* v_es_373_; lean_object* v___x_374_; size_t v___x_375_; size_t v___x_376_; lean_object* v_j_377_; lean_object* v___x_378_; 
v_es_373_ = lean_ctor_get(v_x_370_, 0);
v___x_374_ = lean_box(2);
v___x_375_ = ((size_t)31ULL);
v___x_376_ = lean_usize_land(v_x_371_, v___x_375_);
v_j_377_ = lean_usize_to_nat(v___x_376_);
v___x_378_ = lean_array_get_borrowed(v___x_374_, v_es_373_, v_j_377_);
lean_dec(v_j_377_);
switch(lean_obj_tag(v___x_378_))
{
case 0:
{
lean_object* v_key_379_; lean_object* v_val_380_; size_t v___x_381_; size_t v___x_382_; uint8_t v___x_383_; 
v_key_379_ = lean_ctor_get(v___x_378_, 0);
v_val_380_ = lean_ctor_get(v___x_378_, 1);
v___x_381_ = lean_ptr_addr(v_x_372_);
v___x_382_ = lean_ptr_addr(v_key_379_);
v___x_383_ = lean_usize_dec_eq(v___x_381_, v___x_382_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; 
v___x_384_ = lean_box(0);
return v___x_384_;
}
else
{
lean_object* v___x_385_; 
lean_inc(v_val_380_);
v___x_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_385_, 0, v_val_380_);
return v___x_385_;
}
}
case 1:
{
lean_object* v_node_386_; size_t v___x_387_; size_t v___x_388_; 
v_node_386_ = lean_ctor_get(v___x_378_, 0);
v___x_387_ = ((size_t)5ULL);
v___x_388_ = lean_usize_shift_right(v_x_371_, v___x_387_);
v_x_370_ = v_node_386_;
v_x_371_ = v___x_388_;
goto _start;
}
default: 
{
lean_object* v___x_390_; 
v___x_390_ = lean_box(0);
return v___x_390_;
}
}
}
else
{
lean_object* v_ks_391_; lean_object* v_vs_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_ks_391_ = lean_ctor_get(v_x_370_, 0);
v_vs_392_ = lean_ctor_get(v_x_370_, 1);
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_391_, v_vs_392_, v___x_393_, v_x_372_);
return v___x_394_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_370_ = stack[0].m_obj;
size_t v_x_371_ = stack[1].m_num;
lean_object* v_x_372_ = stack[2].m_obj;
lean_object* v_res_395_;
v_res_395_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_370_, v_x_371_, v_x_372_);
stack->m_obj
 = v_res_395_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
size_t v_x_916__boxed_399_; lean_object* v_res_400_; 
v_x_916__boxed_399_ = lean_unbox_usize(v_x_397_);
lean_dec(v_x_397_);
v_res_400_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_396_, v_x_916__boxed_399_, v_x_398_);
lean_dec_ref(v_x_398_);
lean_dec_ref(v_x_396_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(lean_object* v_x_401_, lean_object* v_x_402_){
_start:
{
size_t v___x_403_; size_t v___x_404_; size_t v___x_405_; uint64_t v___x_406_; size_t v___x_407_; lean_object* v___x_408_; 
v___x_403_ = lean_ptr_addr(v_x_402_);
v___x_404_ = ((size_t)3ULL);
v___x_405_ = lean_usize_shift_right(v___x_403_, v___x_404_);
v___x_406_ = lean_usize_to_uint64(v___x_405_);
v___x_407_ = lean_uint64_to_usize(v___x_406_);
v___x_408_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_401_, v___x_407_, v_x_402_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_409_, lean_object* v_x_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_x_409_, v_x_410_);
lean_dec_ref(v_x_410_);
lean_dec_ref(v_x_409_);
return v_res_411_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(lean_object* v_e_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_426_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_426_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_426_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_426_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v_exprToNatStructId_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v_exprToNatStructId_421_ = lean_ctor_get(v_a_417_, 7);
lean_inc_ref(v_exprToNatStructId_421_);
lean_dec(v_a_417_);
v___x_422_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_exprToNatStructId_421_, v_e_412_);
lean_dec_ref(v_exprToNatStructId_421_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_422_);
v___x_424_ = v___x_419_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
v_a_427_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_416_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_416_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_412_ = stack[0].m_obj;
lean_object* v_a_413_ = stack[1].m_obj;
lean_object* v_a_414_ = stack[2].m_obj;
lean_object* v_res_435_;
v_res_435_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_e_412_, v_a_413_, v_a_414_);
stack->m_obj
 = v_res_435_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg___boxed(lean_object* v_e_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_e_436_, v_a_437_, v_a_438_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_e_436_);
return v_res_440_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f(lean_object* v_e_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_e_441_, v_a_442_, v_a_450_);
return v___x_453_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_441_ = stack[0].m_obj;
lean_object* v_a_442_ = stack[1].m_obj;
lean_object* v_a_443_ = stack[2].m_obj;
lean_object* v_a_444_ = stack[3].m_obj;
lean_object* v_a_445_ = stack[4].m_obj;
lean_object* v_a_446_ = stack[5].m_obj;
lean_object* v_a_447_ = stack[6].m_obj;
lean_object* v_a_448_ = stack[7].m_obj;
lean_object* v_a_449_ = stack[8].m_obj;
lean_object* v_a_450_ = stack[9].m_obj;
lean_object* v_a_451_ = stack[10].m_obj;
lean_object* v_res_454_;
v_res_454_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f(v_e_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
stack->m_obj
 = v_res_454_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___boxed(lean_object* v_e_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f(v_e_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec(v_a_456_);
lean_dec_ref(v_e_455_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0(lean_object* v_00_u03b2_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_x_469_, v_x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_472_, lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0(v_00_u03b2_472_, v_x_473_, v_x_474_);
lean_dec_ref(v_x_474_);
lean_dec_ref(v_x_473_);
return v_res_475_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_476_, lean_object* v_x_477_, size_t v_x_478_, lean_object* v_x_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_477_, v_x_478_, v_x_479_);
return v___x_480_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_477_ = stack[1].m_obj;
size_t v_x_478_ = stack[2].m_num;
lean_object* v_x_479_ = stack[3].m_obj;
lean_object* v_res_481_;
v_res_481_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0(lean_box(0), v_x_477_, v_x_478_, v_x_479_);
stack->m_obj
 = v_res_481_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_482_, lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
size_t v_x_1102__boxed_486_; lean_object* v_res_487_; 
v_x_1102__boxed_486_ = lean_unbox_usize(v_x_484_);
lean_dec(v_x_484_);
v_res_487_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0(v_00_u03b2_482_, v_x_483_, v_x_1102__boxed_486_, v_x_485_);
lean_dec_ref(v_x_485_);
lean_dec_ref(v_x_483_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_488_, lean_object* v_keys_489_, lean_object* v_vals_490_, lean_object* v_heq_491_, lean_object* v_i_492_, lean_object* v_k_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_489_, v_vals_490_, v_i_492_, v_k_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_495_, lean_object* v_keys_496_, lean_object* v_vals_497_, lean_object* v_heq_498_, lean_object* v_i_499_, lean_object* v_k_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_495_, v_keys_496_, v_vals_497_, v_heq_498_, v_i_499_, v_k_500_);
lean_dec_ref(v_k_500_);
lean_dec_ref(v_vals_497_);
lean_dec_ref(v_keys_496_);
return v_res_501_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(lean_object* v_a_502_, lean_object* v_b_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_a_502_, v_a_504_, v_a_505_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_536_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_536_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_536_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_536_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
if (lean_obj_tag(v_a_508_) == 1)
{
lean_object* v_val_512_; lean_object* v___x_513_; 
lean_del_object(v___x_510_);
v_val_512_ = lean_ctor_get(v_a_508_, 0);
v___x_513_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_b_503_, v_a_504_, v_a_505_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_531_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_531_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_531_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_531_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
if (lean_obj_tag(v_a_514_) == 1)
{
lean_object* v_val_518_; uint8_t v___x_519_; 
v_val_518_ = lean_ctor_get(v_a_514_, 0);
lean_inc(v_val_518_);
lean_dec_ref_known(v_a_514_, 1);
v___x_519_ = lean_nat_dec_eq(v_val_512_, v_val_518_);
lean_dec(v_val_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_522_; 
lean_dec_ref_known(v_a_508_, 1);
v___x_520_ = lean_box(0);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_520_);
v___x_522_ = v___x_516_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
else
{
lean_object* v___x_525_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v_a_508_);
v___x_525_ = v___x_516_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_508_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
lean_object* v___x_527_; lean_object* v___x_529_; 
lean_dec(v_a_514_);
lean_dec_ref_known(v_a_508_, 1);
v___x_527_ = lean_box(0);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_527_);
v___x_529_ = v___x_516_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_508_, 1);
return v___x_513_;
}
}
else
{
lean_object* v___x_532_; lean_object* v___x_534_; 
lean_dec(v_a_508_);
v___x_532_ = lean_box(0);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_532_);
v___x_534_ = v___x_510_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
return v___x_507_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_502_ = stack[0].m_obj;
lean_object* v_b_503_ = stack[1].m_obj;
lean_object* v_a_504_ = stack[2].m_obj;
lean_object* v_a_505_ = stack[3].m_obj;
lean_object* v_res_537_;
v_res_537_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_502_, v_b_503_, v_a_504_, v_a_505_);
stack->m_obj
 = v_res_537_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg___boxed(lean_object* v_a_538_, lean_object* v_b_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_538_, v_b_539_, v_a_540_, v_a_541_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_b_539_);
lean_dec_ref(v_a_538_);
return v_res_543_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f(lean_object* v_a_544_, lean_object* v_b_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_544_, v_b_545_, v_a_546_, v_a_554_);
return v___x_557_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_544_ = stack[0].m_obj;
lean_object* v_b_545_ = stack[1].m_obj;
lean_object* v_a_546_ = stack[2].m_obj;
lean_object* v_a_547_ = stack[3].m_obj;
lean_object* v_a_548_ = stack[4].m_obj;
lean_object* v_a_549_ = stack[5].m_obj;
lean_object* v_a_550_ = stack[6].m_obj;
lean_object* v_a_551_ = stack[7].m_obj;
lean_object* v_a_552_ = stack[8].m_obj;
lean_object* v_a_553_ = stack[9].m_obj;
lean_object* v_a_554_ = stack[10].m_obj;
lean_object* v_a_555_ = stack[11].m_obj;
lean_object* v_res_558_;
v_res_558_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f(v_a_544_, v_b_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
stack->m_obj
 = v_res_558_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___boxed(lean_object* v_a_559_, lean_object* v_b_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f(v_a_559_, v_b_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_b_560_);
lean_dec_ref(v_a_559_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_573_, lean_object* v_x_574_, lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
lean_object* v_ks_577_; lean_object* v_vs_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_604_; 
v_ks_577_ = lean_ctor_get(v_x_573_, 0);
v_vs_578_ = lean_ctor_get(v_x_573_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_x_573_);
if (v_isSharedCheck_604_ == 0)
{
v___x_580_ = v_x_573_;
v_isShared_581_ = v_isSharedCheck_604_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_vs_578_);
lean_inc(v_ks_577_);
lean_dec(v_x_573_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_604_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_array_get_size(v_ks_577_);
v___x_583_ = lean_nat_dec_lt(v_x_574_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
lean_dec(v_x_574_);
v___x_584_ = lean_array_push(v_ks_577_, v_x_575_);
v___x_585_ = lean_array_push(v_vs_578_, v_x_576_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_585_);
lean_ctor_set(v___x_580_, 0, v___x_584_);
v___x_587_ = v___x_580_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
else
{
lean_object* v_k_x27_589_; size_t v___x_590_; size_t v___x_591_; uint8_t v___x_592_; 
v_k_x27_589_ = lean_array_fget_borrowed(v_ks_577_, v_x_574_);
v___x_590_ = lean_ptr_addr(v_x_575_);
v___x_591_ = lean_ptr_addr(v_k_x27_589_);
v___x_592_ = lean_usize_dec_eq(v___x_590_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_594_; 
if (v_isShared_581_ == 0)
{
v___x_594_ = v___x_580_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_ks_577_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_vs_578_);
v___x_594_ = v_reuseFailAlloc_598_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(1u);
v___x_596_ = lean_nat_add(v_x_574_, v___x_595_);
lean_dec(v_x_574_);
v_x_573_ = v___x_594_;
v_x_574_ = v___x_596_;
goto _start;
}
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_599_ = lean_array_fset(v_ks_577_, v_x_574_, v_x_575_);
v___x_600_ = lean_array_fset(v_vs_578_, v_x_574_, v_x_576_);
lean_dec(v_x_574_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_600_);
lean_ctor_set(v___x_580_, 0, v___x_599_);
v___x_602_ = v___x_580_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_605_, lean_object* v_k_606_, lean_object* v_v_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_605_, v___x_608_, v_k_606_, v_v_607_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_610_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(lean_object* v_x_611_, size_t v_x_612_, size_t v_x_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_611_) == 0)
{
lean_object* v_es_616_; size_t v___x_617_; size_t v___x_618_; lean_object* v_j_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_es_616_ = lean_ctor_get(v_x_611_, 0);
v___x_617_ = ((size_t)31ULL);
v___x_618_ = lean_usize_land(v_x_612_, v___x_617_);
v_j_619_ = lean_usize_to_nat(v___x_618_);
v___x_620_ = lean_array_get_size(v_es_616_);
v___x_621_ = lean_nat_dec_lt(v_j_619_, v___x_620_);
if (v___x_621_ == 0)
{
lean_dec(v_j_619_);
lean_dec(v_x_615_);
lean_dec_ref(v_x_614_);
return v_x_611_;
}
else
{
lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_662_; 
lean_inc_ref(v_es_616_);
v_isSharedCheck_662_ = !lean_is_exclusive(v_x_611_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v_x_611_, 0);
lean_dec(v_unused_663_);
v___x_623_ = v_x_611_;
v_isShared_624_ = v_isSharedCheck_662_;
goto v_resetjp_622_;
}
else
{
lean_dec(v_x_611_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_662_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_v_625_; lean_object* v___x_626_; lean_object* v_xs_x27_627_; lean_object* v___y_629_; 
v_v_625_ = lean_array_fget(v_es_616_, v_j_619_);
v___x_626_ = lean_box(0);
v_xs_x27_627_ = lean_array_fset(v_es_616_, v_j_619_, v___x_626_);
switch(lean_obj_tag(v_v_625_))
{
case 0:
{
lean_object* v_key_634_; lean_object* v_val_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_647_; 
v_key_634_ = lean_ctor_get(v_v_625_, 0);
v_val_635_ = lean_ctor_get(v_v_625_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_v_625_);
if (v_isSharedCheck_647_ == 0)
{
v___x_637_ = v_v_625_;
v_isShared_638_ = v_isSharedCheck_647_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_val_635_);
lean_inc(v_key_634_);
lean_dec(v_v_625_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_647_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
size_t v___x_639_; size_t v___x_640_; uint8_t v___x_641_; 
v___x_639_ = lean_ptr_addr(v_x_614_);
v___x_640_ = lean_ptr_addr(v_key_634_);
v___x_641_ = lean_usize_dec_eq(v___x_639_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; 
lean_del_object(v___x_637_);
v___x_642_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_634_, v_val_635_, v_x_614_, v_x_615_);
v___x_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
v___y_629_ = v___x_643_;
goto v___jp_628_;
}
else
{
lean_object* v___x_645_; 
lean_dec(v_val_635_);
lean_dec(v_key_634_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v_x_615_);
lean_ctor_set(v___x_637_, 0, v_x_614_);
v___x_645_ = v___x_637_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_x_614_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_x_615_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
v___y_629_ = v___x_645_;
goto v___jp_628_;
}
}
}
}
case 1:
{
lean_object* v_node_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_660_; 
v_node_648_ = lean_ctor_get(v_v_625_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_v_625_);
if (v_isSharedCheck_660_ == 0)
{
v___x_650_ = v_v_625_;
v_isShared_651_ = v_isSharedCheck_660_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_node_648_);
lean_dec(v_v_625_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_660_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
size_t v___x_652_; size_t v___x_653_; size_t v___x_654_; size_t v___x_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_652_ = ((size_t)5ULL);
v___x_653_ = lean_usize_shift_right(v_x_612_, v___x_652_);
v___x_654_ = ((size_t)1ULL);
v___x_655_ = lean_usize_add(v_x_613_, v___x_654_);
v___x_656_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_node_648_, v___x_653_, v___x_655_, v_x_614_, v_x_615_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_656_);
v___x_658_ = v___x_650_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
v___y_629_ = v___x_658_;
goto v___jp_628_;
}
}
}
default: 
{
lean_object* v___x_661_; 
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v_x_614_);
lean_ctor_set(v___x_661_, 1, v_x_615_);
v___y_629_ = v___x_661_;
goto v___jp_628_;
}
}
v___jp_628_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = lean_array_fset(v_xs_x27_627_, v_j_619_, v___y_629_);
lean_dec(v_j_619_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_630_);
v___x_632_ = v___x_623_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
else
{
lean_object* v_ks_664_; lean_object* v_vs_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_683_; 
v_ks_664_ = lean_ctor_get(v_x_611_, 0);
v_vs_665_ = lean_ctor_get(v_x_611_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_x_611_);
if (v_isSharedCheck_683_ == 0)
{
v___x_667_ = v_x_611_;
v_isShared_668_ = v_isSharedCheck_683_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_vs_665_);
lean_inc(v_ks_664_);
lean_dec(v_x_611_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_683_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_ks_664_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_vs_665_);
v___x_670_ = v_reuseFailAlloc_682_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v_newNode_671_; size_t v___x_672_; uint8_t v___x_673_; 
v_newNode_671_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(v___x_670_, v_x_614_, v_x_615_);
v___x_672_ = ((size_t)7ULL);
v___x_673_ = lean_usize_dec_le(v___x_672_, v_x_613_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_674_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_671_);
v___x_675_ = lean_unsigned_to_nat(4u);
v___x_676_ = lean_nat_dec_lt(v___x_674_, v___x_675_);
lean_dec(v___x_674_);
if (v___x_676_ == 0)
{
lean_object* v_ks_677_; lean_object* v_vs_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v_ks_677_ = lean_ctor_get(v_newNode_671_, 0);
lean_inc_ref(v_ks_677_);
v_vs_678_ = lean_ctor_get(v_newNode_671_, 1);
lean_inc_ref(v_vs_678_);
lean_dec_ref(v_newNode_671_);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0);
v___x_681_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_x_613_, v_ks_677_, v_vs_678_, v___x_679_, v___x_680_);
lean_dec_ref(v_vs_678_);
lean_dec_ref(v_ks_677_);
return v___x_681_;
}
else
{
return v_newNode_671_;
}
}
else
{
return v_newNode_671_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_611_ = stack[0].m_obj;
size_t v_x_612_ = stack[1].m_num;
size_t v_x_613_ = stack[2].m_num;
lean_object* v_x_614_ = stack[3].m_obj;
lean_object* v_x_615_ = stack[4].m_obj;
lean_object* v_res_684_;
v_res_684_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_611_, v_x_612_, v_x_613_, v_x_614_, v_x_615_);
stack->m_obj
 = v_res_684_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(size_t v_depth_685_, lean_object* v_keys_686_, lean_object* v_vals_687_, lean_object* v_i_688_, lean_object* v_entries_689_){
_start:
{
lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = lean_array_get_size(v_keys_686_);
v___x_691_ = lean_nat_dec_lt(v_i_688_, v___x_690_);
if (v___x_691_ == 0)
{
lean_dec(v_i_688_);
return v_entries_689_;
}
else
{
lean_object* v_k_692_; lean_object* v_v_693_; size_t v___x_694_; size_t v___x_695_; size_t v___x_696_; uint64_t v___x_697_; size_t v_h_698_; size_t v___x_699_; lean_object* v___x_700_; size_t v___x_701_; size_t v___x_702_; size_t v___x_703_; size_t v_h_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_k_692_ = lean_array_fget_borrowed(v_keys_686_, v_i_688_);
v_v_693_ = lean_array_fget_borrowed(v_vals_687_, v_i_688_);
v___x_694_ = lean_ptr_addr(v_k_692_);
v___x_695_ = ((size_t)3ULL);
v___x_696_ = lean_usize_shift_right(v___x_694_, v___x_695_);
v___x_697_ = lean_usize_to_uint64(v___x_696_);
v_h_698_ = lean_uint64_to_usize(v___x_697_);
v___x_699_ = ((size_t)5ULL);
v___x_700_ = lean_unsigned_to_nat(1u);
v___x_701_ = ((size_t)1ULL);
v___x_702_ = lean_usize_sub(v_depth_685_, v___x_701_);
v___x_703_ = lean_usize_mul(v___x_699_, v___x_702_);
v_h_704_ = lean_usize_shift_right(v_h_698_, v___x_703_);
v___x_705_ = lean_nat_add(v_i_688_, v___x_700_);
lean_dec(v_i_688_);
lean_inc(v_v_693_);
lean_inc(v_k_692_);
v___x_706_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_entries_689_, v_h_704_, v_depth_685_, v_k_692_, v_v_693_);
v_i_688_ = v___x_705_;
v_entries_689_ = v___x_706_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_685_ = stack[0].m_num;
lean_object* v_keys_686_ = stack[1].m_obj;
lean_object* v_vals_687_ = stack[2].m_obj;
lean_object* v_i_688_ = stack[3].m_obj;
lean_object* v_entries_689_ = stack[4].m_obj;
lean_object* v_res_708_;
v_res_708_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_depth_685_, v_keys_686_, v_vals_687_, v_i_688_, v_entries_689_);
stack->m_obj
 = v_res_708_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_709_, lean_object* v_keys_710_, lean_object* v_vals_711_, lean_object* v_i_712_, lean_object* v_entries_713_){
_start:
{
size_t v_depth_boxed_714_; lean_object* v_res_715_; 
v_depth_boxed_714_ = lean_unbox_usize(v_depth_709_);
lean_dec(v_depth_709_);
v_res_715_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_714_, v_keys_710_, v_vals_711_, v_i_712_, v_entries_713_);
lean_dec_ref(v_vals_711_);
lean_dec_ref(v_keys_710_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___boxed(lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_x_719_, lean_object* v_x_720_){
_start:
{
size_t v_x_6394__boxed_721_; size_t v_x_6395__boxed_722_; lean_object* v_res_723_; 
v_x_6394__boxed_721_ = lean_unbox_usize(v_x_717_);
lean_dec(v_x_717_);
v_x_6395__boxed_722_ = lean_unbox_usize(v_x_718_);
lean_dec(v_x_718_);
v_res_723_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_716_, v_x_6394__boxed_721_, v_x_6395__boxed_722_, v_x_719_, v_x_720_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
size_t v___x_727_; size_t v___x_728_; size_t v___x_729_; uint64_t v___x_730_; size_t v___x_731_; size_t v___x_732_; lean_object* v___x_733_; 
v___x_727_ = lean_ptr_addr(v_x_725_);
v___x_728_ = ((size_t)3ULL);
v___x_729_ = lean_usize_shift_right(v___x_727_, v___x_728_);
v___x_730_ = lean_usize_to_uint64(v___x_729_);
v___x_731_ = lean_uint64_to_usize(v___x_730_);
v___x_732_ = ((size_t)1ULL);
v___x_733_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_724_, v___x_731_, v___x_732_, v_x_725_, v_x_726_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0(lean_object* v_e_734_, lean_object* v_a_735_, lean_object* v_s_736_){
_start:
{
lean_object* v_structs_737_; lean_object* v_typeIdOf_738_; lean_object* v_exprToStructId_739_; lean_object* v_exprToStructIdEntries_740_; lean_object* v_forbiddenNatModules_741_; lean_object* v_natStructs_742_; lean_object* v_natTypeIdOf_743_; lean_object* v_exprToNatStructId_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_752_; 
v_structs_737_ = lean_ctor_get(v_s_736_, 0);
v_typeIdOf_738_ = lean_ctor_get(v_s_736_, 1);
v_exprToStructId_739_ = lean_ctor_get(v_s_736_, 2);
v_exprToStructIdEntries_740_ = lean_ctor_get(v_s_736_, 3);
v_forbiddenNatModules_741_ = lean_ctor_get(v_s_736_, 4);
v_natStructs_742_ = lean_ctor_get(v_s_736_, 5);
v_natTypeIdOf_743_ = lean_ctor_get(v_s_736_, 6);
v_exprToNatStructId_744_ = lean_ctor_get(v_s_736_, 7);
v_isSharedCheck_752_ = !lean_is_exclusive(v_s_736_);
if (v_isSharedCheck_752_ == 0)
{
v___x_746_ = v_s_736_;
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_exprToNatStructId_744_);
lean_inc(v_natTypeIdOf_743_);
lean_inc(v_natStructs_742_);
lean_inc(v_forbiddenNatModules_741_);
lean_inc(v_exprToStructIdEntries_740_);
lean_inc(v_exprToStructId_739_);
lean_inc(v_typeIdOf_738_);
lean_inc(v_structs_737_);
lean_dec(v_s_736_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
lean_inc(v_a_735_);
v___x_748_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_exprToNatStructId_744_, v_e_734_, v_a_735_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 7, v___x_748_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_structs_737_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_typeIdOf_738_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v_exprToStructId_739_);
lean_ctor_set(v_reuseFailAlloc_751_, 3, v_exprToStructIdEntries_740_);
lean_ctor_set(v_reuseFailAlloc_751_, 4, v_forbiddenNatModules_741_);
lean_ctor_set(v_reuseFailAlloc_751_, 5, v_natStructs_742_);
lean_ctor_set(v_reuseFailAlloc_751_, 6, v_natTypeIdOf_743_);
lean_ctor_set(v_reuseFailAlloc_751_, 7, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0___boxed(lean_object* v_e_753_, lean_object* v_a_754_, lean_object* v_s_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0(v_e_753_, v_a_754_, v_s_755_);
lean_dec(v_a_754_);
return v_res_756_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__0));
v___x_759_ = l_Lean_stringToMessageData(v___x_758_);
return v___x_759_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(lean_object* v_e_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v___f_773_; lean_object* v___x_774_; 
lean_inc(v_a_761_);
lean_inc_ref(v_e_760_);
v___f_773_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_773_, 0, v_e_760_);
lean_closure_set(v___f_773_, 1, v_a_761_);
v___x_774_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_e_760_, v_a_762_, v_a_767_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_774_, 1);
if (lean_obj_tag(v_a_775_) == 1)
{
lean_object* v_val_776_; uint8_t v___x_777_; 
lean_dec_ref(v___f_773_);
v_val_776_ = lean_ctor_get(v_a_775_, 0);
lean_inc(v_val_776_);
lean_dec_ref_known(v_a_775_, 1);
v___x_777_ = lean_nat_dec_eq(v_val_776_, v_a_761_);
lean_dec(v_val_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_778_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1);
v___x_779_ = l_Lean_indentExpr(v_e_760_);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_763_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; uint8_t v_verbose_783_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
v_verbose_783_ = lean_ctor_get_uint8(v_a_782_, 0);
lean_dec(v_a_782_);
if (v_verbose_783_ == 0)
{
lean_dec_ref_known(v___x_780_, 2);
goto v___jp_770_;
}
else
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Meta_Sym_reportIssue(v___x_780_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_dec_ref_known(v___x_784_, 1);
goto v___jp_770_;
}
else
{
return v___x_784_;
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec_ref_known(v___x_780_, 2);
v_a_785_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_781_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_781_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
else
{
lean_dec_ref(v_e_760_);
goto v___jp_770_;
}
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; 
lean_dec(v_a_775_);
lean_dec_ref(v_e_760_);
v___x_793_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_794_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_793_, v___f_773_, v_a_762_);
return v___x_794_;
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v___f_773_);
lean_dec_ref(v_e_760_);
v_a_795_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_774_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_774_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
v___jp_770_:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_box(0);
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
return v___x_772_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_760_ = stack[0].m_obj;
lean_object* v_a_761_ = stack[1].m_obj;
lean_object* v_a_762_ = stack[2].m_obj;
lean_object* v_a_763_ = stack[3].m_obj;
lean_object* v_a_764_ = stack[4].m_obj;
lean_object* v_a_765_ = stack[5].m_obj;
lean_object* v_a_766_ = stack[6].m_obj;
lean_object* v_a_767_ = stack[7].m_obj;
lean_object* v_a_768_ = stack[8].m_obj;
lean_object* v_res_803_;
v_res_803_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(v_e_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_);
stack->m_obj
 = v_res_803_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___boxed(lean_object* v_e_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(v_e_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec(v_a_805_);
return v_res_814_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(lean_object* v_e_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(v_e_815_, v_a_816_, v_a_817_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
return v___x_828_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_815_ = stack[0].m_obj;
lean_object* v_a_816_ = stack[1].m_obj;
lean_object* v_a_817_ = stack[2].m_obj;
lean_object* v_a_818_ = stack[3].m_obj;
lean_object* v_a_819_ = stack[4].m_obj;
lean_object* v_a_820_ = stack[5].m_obj;
lean_object* v_a_821_ = stack[6].m_obj;
lean_object* v_a_822_ = stack[7].m_obj;
lean_object* v_a_823_ = stack[8].m_obj;
lean_object* v_a_824_ = stack[9].m_obj;
lean_object* v_a_825_ = stack[10].m_obj;
lean_object* v_a_826_ = stack[11].m_obj;
lean_object* v_res_829_;
v_res_829_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(v_e_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
stack->m_obj
 = v_res_829_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___boxed(lean_object* v_e_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(v_e_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec(v_a_832_);
lean_dec(v_a_831_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0(lean_object* v_00_u03b2_844_, lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v_x_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_x_845_, v_x_846_, v_x_847_);
return v___x_848_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(lean_object* v_00_u03b2_849_, lean_object* v_x_850_, size_t v_x_851_, size_t v_x_852_, lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_850_, v_x_851_, v_x_852_, v_x_853_, v_x_854_);
return v___x_855_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_850_ = stack[1].m_obj;
size_t v_x_851_ = stack[2].m_num;
size_t v_x_852_ = stack[3].m_num;
lean_object* v_x_853_ = stack[4].m_obj;
lean_object* v_x_854_ = stack[5].m_obj;
lean_object* v_res_856_;
v_res_856_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(lean_box(0), v_x_850_, v_x_851_, v_x_852_, v_x_853_, v_x_854_);
stack->m_obj
 = v_res_856_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_857_, lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
size_t v_x_6831__boxed_863_; size_t v_x_6832__boxed_864_; lean_object* v_res_865_; 
v_x_6831__boxed_863_ = lean_unbox_usize(v_x_859_);
lean_dec(v_x_859_);
v_x_6832__boxed_864_ = lean_unbox_usize(v_x_860_);
lean_dec(v_x_860_);
v_res_865_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(v_00_u03b2_857_, v_x_858_, v_x_6831__boxed_863_, v_x_6832__boxed_864_, v_x_861_, v_x_862_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_866_, lean_object* v_n_867_, lean_object* v_k_868_, lean_object* v_v_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(v_n_867_, v_k_868_, v_v_869_);
return v___x_870_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_871_, size_t v_depth_872_, lean_object* v_keys_873_, lean_object* v_vals_874_, lean_object* v_heq_875_, lean_object* v_i_876_, lean_object* v_entries_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_depth_872_, v_keys_873_, v_vals_874_, v_i_876_, v_entries_877_);
return v___x_878_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_872_ = stack[1].m_num;
lean_object* v_keys_873_ = stack[2].m_obj;
lean_object* v_vals_874_ = stack[3].m_obj;
lean_object* v_i_876_ = stack[5].m_obj;
lean_object* v_entries_877_ = stack[6].m_obj;
lean_object* v_res_879_;
v_res_879_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(lean_box(0), v_depth_872_, v_keys_873_, v_vals_874_, lean_box(0), v_i_876_, v_entries_877_);
stack->m_obj
 = v_res_879_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_880_, lean_object* v_depth_881_, lean_object* v_keys_882_, lean_object* v_vals_883_, lean_object* v_heq_884_, lean_object* v_i_885_, lean_object* v_entries_886_){
_start:
{
size_t v_depth_boxed_887_; lean_object* v_res_888_; 
v_depth_boxed_887_ = lean_unbox_usize(v_depth_881_);
lean_dec(v_depth_881_);
v_res_888_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(v_00_u03b2_880_, v_depth_boxed_887_, v_keys_882_, v_vals_883_, v_heq_884_, v_i_885_, v_entries_886_);
lean_dec_ref(v_vals_883_);
lean_dec_ref(v_keys_882_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_889_, lean_object* v_x_890_, lean_object* v_x_891_, lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_890_, v_x_891_, v_x_892_, v_x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0(lean_object* v_a_895_, lean_object* v_e_896_, lean_object* v___x_897_, lean_object* v_s_898_){
_start:
{
lean_object* v_structs_899_; lean_object* v_typeIdOf_900_; lean_object* v_exprToStructId_901_; lean_object* v_exprToStructIdEntries_902_; lean_object* v_forbiddenNatModules_903_; lean_object* v_natStructs_904_; lean_object* v_natTypeIdOf_905_; lean_object* v_exprToNatStructId_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_structs_899_ = lean_ctor_get(v_s_898_, 0);
v_typeIdOf_900_ = lean_ctor_get(v_s_898_, 1);
v_exprToStructId_901_ = lean_ctor_get(v_s_898_, 2);
v_exprToStructIdEntries_902_ = lean_ctor_get(v_s_898_, 3);
v_forbiddenNatModules_903_ = lean_ctor_get(v_s_898_, 4);
v_natStructs_904_ = lean_ctor_get(v_s_898_, 5);
v_natTypeIdOf_905_ = lean_ctor_get(v_s_898_, 6);
v_exprToNatStructId_906_ = lean_ctor_get(v_s_898_, 7);
v___x_907_ = lean_array_get_size(v_natStructs_904_);
v___x_908_ = lean_nat_dec_lt(v_a_895_, v___x_907_);
if (v___x_908_ == 0)
{
lean_dec_ref(v___x_897_);
lean_dec_ref(v_e_896_);
return v_s_898_;
}
else
{
lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_945_; 
lean_inc_ref(v_exprToNatStructId_906_);
lean_inc_ref(v_natTypeIdOf_905_);
lean_inc_ref(v_natStructs_904_);
lean_inc_ref(v_forbiddenNatModules_903_);
lean_inc_ref(v_exprToStructIdEntries_902_);
lean_inc_ref(v_exprToStructId_901_);
lean_inc_ref(v_typeIdOf_900_);
lean_inc_ref(v_structs_899_);
v_isSharedCheck_945_ = !lean_is_exclusive(v_s_898_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; lean_object* v_unused_947_; lean_object* v_unused_948_; lean_object* v_unused_949_; lean_object* v_unused_950_; lean_object* v_unused_951_; lean_object* v_unused_952_; lean_object* v_unused_953_; 
v_unused_946_ = lean_ctor_get(v_s_898_, 7);
lean_dec(v_unused_946_);
v_unused_947_ = lean_ctor_get(v_s_898_, 6);
lean_dec(v_unused_947_);
v_unused_948_ = lean_ctor_get(v_s_898_, 5);
lean_dec(v_unused_948_);
v_unused_949_ = lean_ctor_get(v_s_898_, 4);
lean_dec(v_unused_949_);
v_unused_950_ = lean_ctor_get(v_s_898_, 3);
lean_dec(v_unused_950_);
v_unused_951_ = lean_ctor_get(v_s_898_, 2);
lean_dec(v_unused_951_);
v_unused_952_ = lean_ctor_get(v_s_898_, 1);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_s_898_, 0);
lean_dec(v_unused_953_);
v___x_910_ = v_s_898_;
v_isShared_911_ = v_isSharedCheck_945_;
goto v_resetjp_909_;
}
else
{
lean_dec(v_s_898_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_945_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v_v_912_; lean_object* v_id_913_; lean_object* v_structId_914_; lean_object* v_type_915_; lean_object* v_u_916_; lean_object* v_natModuleInst_917_; lean_object* v_leInst_x3f_918_; lean_object* v_ltInst_x3f_919_; lean_object* v_lawfulOrderLTInst_x3f_920_; lean_object* v_isPreorderInst_x3f_921_; lean_object* v_orderedAddInst_x3f_922_; lean_object* v_isLinearInst_x3f_923_; lean_object* v_addRightCancelInst_x3f_924_; lean_object* v_rfl__q_925_; lean_object* v_zero_926_; lean_object* v_toQFn_927_; lean_object* v_addFn_928_; lean_object* v_smulFn_929_; lean_object* v_termMap_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_944_; 
v_v_912_ = lean_array_fget(v_natStructs_904_, v_a_895_);
v_id_913_ = lean_ctor_get(v_v_912_, 0);
v_structId_914_ = lean_ctor_get(v_v_912_, 1);
v_type_915_ = lean_ctor_get(v_v_912_, 2);
v_u_916_ = lean_ctor_get(v_v_912_, 3);
v_natModuleInst_917_ = lean_ctor_get(v_v_912_, 4);
v_leInst_x3f_918_ = lean_ctor_get(v_v_912_, 5);
v_ltInst_x3f_919_ = lean_ctor_get(v_v_912_, 6);
v_lawfulOrderLTInst_x3f_920_ = lean_ctor_get(v_v_912_, 7);
v_isPreorderInst_x3f_921_ = lean_ctor_get(v_v_912_, 8);
v_orderedAddInst_x3f_922_ = lean_ctor_get(v_v_912_, 9);
v_isLinearInst_x3f_923_ = lean_ctor_get(v_v_912_, 10);
v_addRightCancelInst_x3f_924_ = lean_ctor_get(v_v_912_, 11);
v_rfl__q_925_ = lean_ctor_get(v_v_912_, 12);
v_zero_926_ = lean_ctor_get(v_v_912_, 13);
v_toQFn_927_ = lean_ctor_get(v_v_912_, 14);
v_addFn_928_ = lean_ctor_get(v_v_912_, 15);
v_smulFn_929_ = lean_ctor_get(v_v_912_, 16);
v_termMap_930_ = lean_ctor_get(v_v_912_, 17);
v_isSharedCheck_944_ = !lean_is_exclusive(v_v_912_);
if (v_isSharedCheck_944_ == 0)
{
v___x_932_ = v_v_912_;
v_isShared_933_ = v_isSharedCheck_944_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_termMap_930_);
lean_inc(v_smulFn_929_);
lean_inc(v_addFn_928_);
lean_inc(v_toQFn_927_);
lean_inc(v_zero_926_);
lean_inc(v_rfl__q_925_);
lean_inc(v_addRightCancelInst_x3f_924_);
lean_inc(v_isLinearInst_x3f_923_);
lean_inc(v_orderedAddInst_x3f_922_);
lean_inc(v_isPreorderInst_x3f_921_);
lean_inc(v_lawfulOrderLTInst_x3f_920_);
lean_inc(v_ltInst_x3f_919_);
lean_inc(v_leInst_x3f_918_);
lean_inc(v_natModuleInst_917_);
lean_inc(v_u_916_);
lean_inc(v_type_915_);
lean_inc(v_structId_914_);
lean_inc(v_id_913_);
lean_dec(v_v_912_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_944_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v_xs_x27_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_934_ = lean_box(0);
v_xs_x27_935_ = lean_array_fset(v_natStructs_904_, v_a_895_, v___x_934_);
v___x_936_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_termMap_930_, v_e_896_, v___x_897_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 17, v___x_936_);
v___x_938_ = v___x_932_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_id_913_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_structId_914_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v_type_915_);
lean_ctor_set(v_reuseFailAlloc_943_, 3, v_u_916_);
lean_ctor_set(v_reuseFailAlloc_943_, 4, v_natModuleInst_917_);
lean_ctor_set(v_reuseFailAlloc_943_, 5, v_leInst_x3f_918_);
lean_ctor_set(v_reuseFailAlloc_943_, 6, v_ltInst_x3f_919_);
lean_ctor_set(v_reuseFailAlloc_943_, 7, v_lawfulOrderLTInst_x3f_920_);
lean_ctor_set(v_reuseFailAlloc_943_, 8, v_isPreorderInst_x3f_921_);
lean_ctor_set(v_reuseFailAlloc_943_, 9, v_orderedAddInst_x3f_922_);
lean_ctor_set(v_reuseFailAlloc_943_, 10, v_isLinearInst_x3f_923_);
lean_ctor_set(v_reuseFailAlloc_943_, 11, v_addRightCancelInst_x3f_924_);
lean_ctor_set(v_reuseFailAlloc_943_, 12, v_rfl__q_925_);
lean_ctor_set(v_reuseFailAlloc_943_, 13, v_zero_926_);
lean_ctor_set(v_reuseFailAlloc_943_, 14, v_toQFn_927_);
lean_ctor_set(v_reuseFailAlloc_943_, 15, v_addFn_928_);
lean_ctor_set(v_reuseFailAlloc_943_, 16, v_smulFn_929_);
lean_ctor_set(v_reuseFailAlloc_943_, 17, v___x_936_);
v___x_938_ = v_reuseFailAlloc_943_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_939_ = lean_array_fset(v_xs_x27_935_, v_a_895_, v___x_938_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 5, v___x_939_);
v___x_941_ = v___x_910_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_structs_899_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_typeIdOf_900_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_exprToStructId_901_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v_exprToStructIdEntries_902_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v_forbiddenNatModules_903_);
lean_ctor_set(v_reuseFailAlloc_942_, 5, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_942_, 6, v_natTypeIdOf_905_);
lean_ctor_set(v_reuseFailAlloc_942_, 7, v_exprToNatStructId_906_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0___boxed(lean_object* v_a_954_, lean_object* v_e_955_, lean_object* v___x_956_, lean_object* v_s_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0(v_a_954_, v_e_955_, v___x_956_, v_s_957_);
lean_dec(v_a_954_);
return v_res_958_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(lean_object* v_e_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1065_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_1065_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1065_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_termMap_977_; lean_object* v___x_978_; 
v_termMap_977_ = lean_ctor_get(v_a_973_, 17);
lean_inc_ref(v_termMap_977_);
lean_dec(v_a_973_);
v___x_978_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_termMap_977_, v_e_959_);
lean_dec_ref(v_termMap_977_);
if (lean_obj_tag(v___x_978_) == 1)
{
lean_object* v_val_979_; lean_object* v___x_981_; 
lean_dec_ref(v_e_959_);
v_val_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_val_979_);
lean_dec_ref_known(v___x_978_, 1);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v_val_979_);
v___x_981_ = v___x_975_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_val_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
else
{
lean_object* v___x_983_; 
lean_dec(v___x_978_);
lean_del_object(v___x_975_);
v___x_983_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v_rfl__q_985_; lean_object* v_toQFn_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v_rfl__q_985_ = lean_ctor_get(v_a_984_, 12);
lean_inc_ref(v_rfl__q_985_);
v_toQFn_986_ = lean_ctor_get(v_a_984_, 14);
lean_inc_ref(v_toQFn_986_);
lean_dec(v_a_984_);
lean_inc_ref(v_e_959_);
v___x_987_ = l_Lean_Expr_app___override(v_toQFn_986_, v_e_959_);
v___x_988_ = l_Lean_Meta_Sym_shareCommon(v___x_987_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_990_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
v___x_990_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_959_, v_a_961_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
v___x_992_ = lean_box(0);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v_a_966_);
lean_inc_ref(v_a_965_);
lean_inc(v_a_964_);
lean_inc_ref(v_a_963_);
lean_inc(v_a_962_);
lean_inc(v_a_961_);
lean_inc(v_a_989_);
v___x_993_ = lean_grind_internalize(v_a_989_, v_a_991_, v___x_992_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___f_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec_ref_known(v___x_993_, 1);
lean_inc(v_a_989_);
v___x_994_ = l_Lean_Expr_app___override(v_rfl__q_985_, v_a_989_);
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v_a_989_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
lean_inc_ref(v___x_995_);
lean_inc_ref(v_e_959_);
lean_inc(v_a_960_);
v___f_996_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0___boxed), 4, 3);
lean_closure_set(v___f_996_, 0, v_a_960_);
lean_closure_set(v___f_996_, 1, v_e_959_);
lean_closure_set(v___f_996_, 2, v___x_995_);
v___x_997_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_998_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_997_, v___f_996_, v_a_961_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v___x_999_; 
lean_dec_ref_known(v___x_998_, 1);
lean_inc_ref(v_e_959_);
v___x_999_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(v_e_959_, v_a_960_, v_a_961_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v___x_1000_; 
lean_dec_ref_known(v___x_999_, 1);
v___x_1000_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_997_, v_e_959_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1007_ == 0)
{
lean_object* v_unused_1008_; 
v_unused_1008_ = lean_ctor_get(v___x_1000_, 0);
lean_dec(v_unused_1008_);
v___x_1002_ = v___x_1000_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_dec(v___x_1000_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_995_);
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_995_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec_ref_known(v___x_995_, 2);
v_a_1009_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_1000_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1000_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref_known(v___x_995_, 2);
lean_dec_ref(v_e_959_);
v_a_1017_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_999_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_999_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec_ref_known(v___x_995_, 2);
lean_dec_ref(v_e_959_);
v_a_1025_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_998_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_998_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec(v_a_989_);
lean_dec_ref(v_rfl__q_985_);
lean_dec_ref(v_e_959_);
v_a_1033_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_993_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_993_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v_a_989_);
lean_dec_ref(v_rfl__q_985_);
lean_dec_ref(v_e_959_);
v_a_1041_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_990_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_990_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec_ref(v_rfl__q_985_);
lean_dec_ref(v_e_959_);
v_a_1049_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_988_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_988_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec_ref(v_e_959_);
v_a_1057_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_983_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_983_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec_ref(v_e_959_);
v_a_1066_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_972_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_972_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_959_ = stack[0].m_obj;
lean_object* v_a_960_ = stack[1].m_obj;
lean_object* v_a_961_ = stack[2].m_obj;
lean_object* v_a_962_ = stack[3].m_obj;
lean_object* v_a_963_ = stack[4].m_obj;
lean_object* v_a_964_ = stack[5].m_obj;
lean_object* v_a_965_ = stack[6].m_obj;
lean_object* v_a_966_ = stack[7].m_obj;
lean_object* v_a_967_ = stack[8].m_obj;
lean_object* v_a_968_ = stack[9].m_obj;
lean_object* v_a_969_ = stack[10].m_obj;
lean_object* v_a_970_ = stack[11].m_obj;
lean_object* v_res_1074_;
v_res_1074_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
stack->m_obj
 = v_res_1074_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___boxed(lean_object* v_e_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec(v_a_1076_);
return v_res_1088_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(lean_object* v_natStruct_1089_, lean_object* v_inst_1090_){
_start:
{
lean_object* v_addFn_1091_; lean_object* v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; uint8_t v___x_1095_; 
v_addFn_1091_ = lean_ctor_get(v_natStruct_1089_, 15);
v___x_1092_ = l_Lean_Expr_appArg_x21(v_addFn_1091_);
v___x_1093_ = lean_ptr_addr(v___x_1092_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = lean_ptr_addr(v_inst_1090_);
v___x_1095_ = lean_usize_dec_eq(v___x_1093_, v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_natStruct_1089_ = stack[0].m_obj;
lean_object* v_inst_1090_ = stack[1].m_obj;
uint8_t v_res_1096_;
v_res_1096_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_natStruct_1089_, v_inst_1090_);
stack->m_num = v_res_1096_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst___boxed(lean_object* v_natStruct_1097_, lean_object* v_inst_1098_){
_start:
{
uint8_t v_res_1099_; lean_object* v_r_1100_; 
v_res_1099_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_natStruct_1097_, v_inst_1098_);
lean_dec_ref(v_inst_1098_);
lean_dec_ref(v_natStruct_1097_);
v_r_1100_ = lean_box(v_res_1099_);
return v_r_1100_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(lean_object* v_natStruct_1101_, lean_object* v_inst_1102_){
_start:
{
lean_object* v_zero_1103_; lean_object* v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; uint8_t v___x_1107_; 
v_zero_1103_ = lean_ctor_get(v_natStruct_1101_, 13);
v___x_1104_ = l_Lean_Expr_appArg_x21(v_zero_1103_);
v___x_1105_ = lean_ptr_addr(v___x_1104_);
lean_dec_ref(v___x_1104_);
v___x_1106_ = lean_ptr_addr(v_inst_1102_);
v___x_1107_ = lean_usize_dec_eq(v___x_1105_, v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_natStruct_1101_ = stack[0].m_obj;
lean_object* v_inst_1102_ = stack[1].m_obj;
uint8_t v_res_1108_;
v_res_1108_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_natStruct_1101_, v_inst_1102_);
stack->m_num = v_res_1108_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst___boxed(lean_object* v_natStruct_1109_, lean_object* v_inst_1110_){
_start:
{
uint8_t v_res_1111_; lean_object* v_r_1112_; 
v_res_1111_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_natStruct_1109_, v_inst_1110_);
lean_dec_ref(v_inst_1110_);
lean_dec_ref(v_natStruct_1109_);
v_r_1112_ = lean_box(v_res_1111_);
return v_r_1112_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(lean_object* v_natStruct_1113_, lean_object* v_inst_1114_){
_start:
{
lean_object* v_smulFn_1115_; lean_object* v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; uint8_t v___x_1119_; 
v_smulFn_1115_ = lean_ctor_get(v_natStruct_1113_, 16);
v___x_1116_ = l_Lean_Expr_appArg_x21(v_smulFn_1115_);
v___x_1117_ = lean_ptr_addr(v___x_1116_);
lean_dec_ref(v___x_1116_);
v___x_1118_ = lean_ptr_addr(v_inst_1114_);
v___x_1119_ = lean_usize_dec_eq(v___x_1117_, v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_natStruct_1113_ = stack[0].m_obj;
lean_object* v_inst_1114_ = stack[1].m_obj;
uint8_t v_res_1120_;
v_res_1120_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_natStruct_1113_, v_inst_1114_);
stack->m_num = v_res_1120_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst___boxed(lean_object* v_natStruct_1121_, lean_object* v_inst_1122_){
_start:
{
uint8_t v_res_1123_; lean_object* v_r_1124_; 
v_res_1123_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_natStruct_1121_, v_inst_1122_);
lean_dec_ref(v_inst_1122_);
lean_dec_ref(v_natStruct_1121_);
v_r_1124_ = lean_box(v_res_1123_);
return v_r_1124_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(lean_object* v_e_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1185_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1187_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v___x_1185_, 1);
lean_inc_ref(v_e_1170_);
v___x_1187_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1170_, v_a_1179_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1338_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1338_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1338_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = l_Lean_Expr_cleanupAnnotations(v_a_1188_);
v___x_1193_ = l_Lean_Expr_isApp(v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_dec_ref(v___x_1192_);
lean_del_object(v___x_1190_);
lean_dec(v_a_1186_);
lean_dec(v_a_1184_);
v___x_1194_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
return v___x_1194_;
}
else
{
lean_object* v_arg_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v_arg_1195_ = lean_ctor_get(v___x_1192_, 1);
lean_inc_ref(v_arg_1195_);
v___x_1196_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1192_);
v___x_1197_ = l_Lean_Expr_isApp(v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; 
lean_dec_ref(v___x_1196_);
lean_dec_ref(v_arg_1195_);
lean_del_object(v___x_1190_);
lean_dec(v_a_1186_);
lean_dec(v_a_1184_);
v___x_1198_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
return v___x_1198_;
}
else
{
lean_object* v_arg_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_arg_1199_ = lean_ctor_get(v___x_1196_, 1);
lean_inc_ref(v_arg_1199_);
v___x_1200_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1196_);
v___x_1201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2));
v___x_1202_ = l_Lean_Expr_isConstOf(v___x_1200_, v___x_1201_);
if (v___x_1202_ == 0)
{
uint8_t v___x_1203_; 
lean_del_object(v___x_1190_);
v___x_1203_ = l_Lean_Expr_isApp(v___x_1200_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; 
lean_dec_ref(v___x_1200_);
lean_dec_ref(v_arg_1199_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_a_1186_);
lean_dec(v_a_1184_);
v___x_1204_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
return v___x_1204_;
}
else
{
lean_object* v_arg_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v_arg_1205_ = lean_ctor_get(v___x_1200_, 1);
lean_inc_ref(v_arg_1205_);
v___x_1206_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1200_);
v___x_1207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5));
v___x_1208_ = l_Lean_Expr_isConstOf(v___x_1206_, v___x_1207_);
if (v___x_1208_ == 0)
{
uint8_t v___x_1209_; 
v___x_1209_ = l_Lean_Expr_isApp(v___x_1206_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; 
lean_dec_ref(v___x_1206_);
lean_dec_ref(v_arg_1205_);
lean_dec_ref(v_arg_1199_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_a_1186_);
lean_dec(v_a_1184_);
v___x_1210_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
return v___x_1210_;
}
else
{
lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1206_);
v___x_1212_ = l_Lean_Expr_isApp(v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_dec_ref(v___x_1211_);
lean_dec_ref(v_arg_1205_);
lean_dec_ref(v_arg_1199_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_a_1186_);
lean_dec(v_a_1184_);
v___x_1213_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1211_);
v___x_1215_ = l_Lean_Expr_isApp(v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
lean_dec_ref(v___x_1214_);
lean_dec_ref(v_arg_1205_);
lean_dec_ref(v_arg_1199_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_a_1186_);
lean_dec(v_a_1184_);
v___x_1216_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
return v___x_1216_;
}
else
{
lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1217_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1214_);
v___x_1218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8));
v___x_1219_ = l_Lean_Expr_isConstOf(v___x_1217_, v___x_1218_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11));
v___x_1221_ = l_Lean_Expr_isConstOf(v___x_1217_, v___x_1220_);
lean_dec_ref(v___x_1217_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; 
lean_dec_ref(v_arg_1205_);
lean_dec_ref(v_arg_1199_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_a_1186_);
lean_dec(v_a_1184_);
v___x_1222_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
return v___x_1222_;
}
else
{
uint8_t v___x_1223_; 
v___x_1223_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_1186_, v_arg_1205_);
lean_dec_ref(v_arg_1205_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; 
lean_dec_ref(v_arg_1199_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_a_1186_);
lean_dec(v_a_1184_);
v___x_1224_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
return v___x_1224_;
}
else
{
lean_object* v___x_1225_; 
lean_dec_ref(v_e_1170_);
lean_inc_ref(v_arg_1199_);
v___x_1225_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_1199_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v_fst_1227_; lean_object* v_snd_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1262_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v_fst_1227_ = lean_ctor_get(v_a_1226_, 0);
v_snd_1228_ = lean_ctor_get(v_a_1226_, 1);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_a_1226_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1230_ = v_a_1226_;
v_isShared_1231_ = v_isSharedCheck_1262_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_snd_1228_);
lean_inc(v_fst_1227_);
lean_dec(v_a_1226_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1262_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; 
lean_inc_ref(v_arg_1195_);
v___x_1232_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_1195_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1261_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1261_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1261_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v_fst_1237_; lean_object* v_snd_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1260_; 
v_fst_1237_ = lean_ctor_get(v_a_1233_, 0);
v_snd_1238_ = lean_ctor_get(v_a_1233_, 1);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_a_1233_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1240_ = v_a_1233_;
v_isShared_1241_ = v_isSharedCheck_1260_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_snd_1238_);
lean_inc(v_fst_1237_);
lean_dec(v_a_1233_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1260_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v_addFn_1242_; lean_object* v_type_1243_; lean_object* v_u_1244_; lean_object* v_natModuleInst_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v_addFn_1242_ = lean_ctor_get(v_a_1184_, 22);
lean_inc_ref(v_addFn_1242_);
lean_dec(v_a_1184_);
v_type_1243_ = lean_ctor_get(v_a_1186_, 2);
lean_inc_ref(v_type_1243_);
v_u_1244_ = lean_ctor_get(v_a_1186_, 3);
lean_inc(v_u_1244_);
v_natModuleInst_1245_ = lean_ctor_get(v_a_1186_, 4);
lean_inc_ref(v_natModuleInst_1245_);
lean_dec(v_a_1186_);
lean_inc(v_fst_1237_);
lean_inc(v_fst_1227_);
v___x_1246_ = l_Lean_mkAppB(v_addFn_1242_, v_fst_1227_, v_fst_1237_);
v___x_1247_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17));
v___x_1248_ = lean_box(0);
if (v_isShared_1231_ == 0)
{
lean_ctor_set_tag(v___x_1230_, 1);
lean_ctor_set(v___x_1230_, 1, v___x_1248_);
lean_ctor_set(v___x_1230_, 0, v_u_1244_);
v___x_1250_ = v___x_1230_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_u_1244_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1251_ = l_Lean_mkConst(v___x_1247_, v___x_1250_);
v___x_1252_ = l_Lean_mkApp8(v___x_1251_, v_type_1243_, v_natModuleInst_1245_, v_arg_1199_, v_arg_1195_, v_fst_1227_, v_fst_1237_, v_snd_1228_, v_snd_1238_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 1, v___x_1252_);
lean_ctor_set(v___x_1240_, 0, v___x_1246_);
v___x_1254_ = v___x_1240_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1256_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1254_);
v___x_1256_ = v___x_1235_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
lean_dec(v_fst_1227_);
lean_dec_ref(v_arg_1199_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_a_1186_);
lean_dec(v_a_1184_);
return v___x_1232_;
}
}
}
else
{
lean_dec_ref(v_arg_1199_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_a_1186_);
lean_dec(v_a_1184_);
return v___x_1225_;
}
}
}
}
else
{
uint8_t v___x_1263_; 
lean_dec_ref(v___x_1217_);
v___x_1263_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_a_1186_, v_arg_1205_);
lean_dec_ref(v_arg_1205_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
lean_dec_ref(v_arg_1199_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_a_1186_);
lean_dec(v_a_1184_);
v___x_1264_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; 
lean_dec_ref(v_e_1170_);
lean_inc_ref(v_arg_1195_);
v___x_1265_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_1195_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1292_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1292_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1292_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v_fst_1270_; lean_object* v_snd_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1291_; 
v_fst_1270_ = lean_ctor_get(v_a_1266_, 0);
v_snd_1271_ = lean_ctor_get(v_a_1266_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_a_1266_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1273_ = v_a_1266_;
v_isShared_1274_ = v_isSharedCheck_1291_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_snd_1271_);
lean_inc(v_fst_1270_);
lean_dec(v_a_1266_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1291_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v_nsmulFn_1275_; lean_object* v_type_1276_; lean_object* v_u_1277_; lean_object* v_natModuleInst_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
v_nsmulFn_1275_ = lean_ctor_get(v_a_1184_, 24);
lean_inc_ref(v_nsmulFn_1275_);
lean_dec(v_a_1184_);
v_type_1276_ = lean_ctor_get(v_a_1186_, 2);
lean_inc_ref(v_type_1276_);
v_u_1277_ = lean_ctor_get(v_a_1186_, 3);
lean_inc(v_u_1277_);
v_natModuleInst_1278_ = lean_ctor_get(v_a_1186_, 4);
lean_inc_ref(v_natModuleInst_1278_);
lean_dec(v_a_1186_);
lean_inc(v_fst_1270_);
lean_inc_ref(v_arg_1199_);
v___x_1279_ = l_Lean_mkAppB(v_nsmulFn_1275_, v_arg_1199_, v_fst_1270_);
v___x_1280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19));
v___x_1281_ = lean_box(0);
v___x_1282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1282_, 0, v_u_1277_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = l_Lean_mkConst(v___x_1280_, v___x_1282_);
v___x_1284_ = l_Lean_mkApp6(v___x_1283_, v_type_1276_, v_natModuleInst_1278_, v_arg_1199_, v_arg_1195_, v_fst_1270_, v_snd_1271_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v___x_1284_);
lean_ctor_set(v___x_1273_, 0, v___x_1279_);
v___x_1286_ = v___x_1273_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1288_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1286_);
v___x_1288_ = v___x_1268_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_1199_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_a_1186_);
lean_dec(v_a_1184_);
return v___x_1265_;
}
}
}
}
}
}
}
else
{
lean_object* v_type_1293_; lean_object* v_u_1294_; lean_object* v_natModuleInst_1295_; lean_object* v_zero_1296_; lean_object* v___x_1297_; 
lean_dec_ref(v___x_1206_);
lean_dec_ref(v_arg_1205_);
lean_dec_ref(v_arg_1199_);
lean_dec_ref(v_arg_1195_);
v_type_1293_ = lean_ctor_get(v_a_1186_, 2);
lean_inc_ref(v_type_1293_);
v_u_1294_ = lean_ctor_get(v_a_1186_, 3);
lean_inc(v_u_1294_);
v_natModuleInst_1295_ = lean_ctor_get(v_a_1186_, 4);
lean_inc_ref(v_natModuleInst_1295_);
v_zero_1296_ = lean_ctor_get(v_a_1186_, 13);
lean_inc_ref(v_zero_1296_);
lean_dec(v_a_1186_);
lean_inc_ref(v_e_1170_);
v___x_1297_ = l_Lean_Meta_isDefEqD(v_e_1170_, v_zero_1296_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1314_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1314_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1314_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_unbox(v_a_1298_);
lean_dec(v_a_1298_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
lean_del_object(v___x_1300_);
lean_dec_ref(v_natModuleInst_1295_);
lean_dec(v_u_1294_);
lean_dec_ref(v_type_1293_);
lean_dec(v_a_1184_);
v___x_1303_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
return v___x_1303_;
}
else
{
lean_object* v_zero_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1312_; 
lean_dec_ref(v_e_1170_);
v_zero_1304_ = lean_ctor_get(v_a_1184_, 17);
lean_inc_ref(v_zero_1304_);
lean_dec(v_a_1184_);
v___x_1305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21));
v___x_1306_ = lean_box(0);
v___x_1307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1307_, 0, v_u_1294_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = l_Lean_mkConst(v___x_1305_, v___x_1307_);
v___x_1309_ = l_Lean_mkAppB(v___x_1308_, v_type_1293_, v_natModuleInst_1295_);
v___x_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1310_, 0, v_zero_1304_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1310_);
v___x_1312_ = v___x_1300_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref(v_natModuleInst_1295_);
lean_dec(v_u_1294_);
lean_dec_ref(v_type_1293_);
lean_dec(v_a_1184_);
lean_dec_ref(v_e_1170_);
v_a_1315_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1297_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1297_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
}
else
{
uint8_t v___x_1323_; 
lean_dec_ref(v___x_1200_);
lean_dec_ref(v_arg_1199_);
v___x_1323_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_1186_, v_arg_1195_);
lean_dec_ref(v_arg_1195_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_del_object(v___x_1190_);
lean_dec(v_a_1186_);
lean_dec(v_a_1184_);
v___x_1324_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
return v___x_1324_;
}
else
{
lean_object* v_zero_1325_; lean_object* v_type_1326_; lean_object* v_u_1327_; lean_object* v_natModuleInst_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
lean_dec_ref(v_e_1170_);
v_zero_1325_ = lean_ctor_get(v_a_1184_, 17);
lean_inc_ref(v_zero_1325_);
lean_dec(v_a_1184_);
v_type_1326_ = lean_ctor_get(v_a_1186_, 2);
lean_inc_ref(v_type_1326_);
v_u_1327_ = lean_ctor_get(v_a_1186_, 3);
lean_inc(v_u_1327_);
v_natModuleInst_1328_ = lean_ctor_get(v_a_1186_, 4);
lean_inc_ref(v_natModuleInst_1328_);
lean_dec(v_a_1186_);
v___x_1329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21));
v___x_1330_ = lean_box(0);
v___x_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_u_1327_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = l_Lean_mkConst(v___x_1329_, v___x_1331_);
v___x_1333_ = l_Lean_mkAppB(v___x_1332_, v_type_1326_, v_natModuleInst_1328_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_zero_1325_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1334_);
v___x_1336_ = v___x_1190_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v_a_1186_);
lean_dec(v_a_1184_);
lean_dec_ref(v_e_1170_);
v_a_1339_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1187_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1187_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_dec(v_a_1184_);
lean_dec_ref(v_e_1170_);
v_a_1347_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1185_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1185_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec_ref(v_e_1170_);
v_a_1355_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1183_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1183_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1170_ = stack[0].m_obj;
lean_object* v_a_1171_ = stack[1].m_obj;
lean_object* v_a_1172_ = stack[2].m_obj;
lean_object* v_a_1173_ = stack[3].m_obj;
lean_object* v_a_1174_ = stack[4].m_obj;
lean_object* v_a_1175_ = stack[5].m_obj;
lean_object* v_a_1176_ = stack[6].m_obj;
lean_object* v_a_1177_ = stack[7].m_obj;
lean_object* v_a_1178_ = stack[8].m_obj;
lean_object* v_a_1179_ = stack[9].m_obj;
lean_object* v_a_1180_ = stack[10].m_obj;
lean_object* v_a_1181_ = stack[11].m_obj;
lean_object* v_res_1363_;
v_res_1363_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_e_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
stack->m_obj
 = v_res_1363_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___boxed(lean_object* v_e_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_e_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec(v_a_1365_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0(lean_object* v___y_1378_, lean_object* v_e_1379_, lean_object* v_____x_1380_, lean_object* v_s_1381_){
_start:
{
lean_object* v_structs_1382_; lean_object* v_typeIdOf_1383_; lean_object* v_exprToStructId_1384_; lean_object* v_exprToStructIdEntries_1385_; lean_object* v_forbiddenNatModules_1386_; lean_object* v_natStructs_1387_; lean_object* v_natTypeIdOf_1388_; lean_object* v_exprToNatStructId_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v_structs_1382_ = lean_ctor_get(v_s_1381_, 0);
v_typeIdOf_1383_ = lean_ctor_get(v_s_1381_, 1);
v_exprToStructId_1384_ = lean_ctor_get(v_s_1381_, 2);
v_exprToStructIdEntries_1385_ = lean_ctor_get(v_s_1381_, 3);
v_forbiddenNatModules_1386_ = lean_ctor_get(v_s_1381_, 4);
v_natStructs_1387_ = lean_ctor_get(v_s_1381_, 5);
v_natTypeIdOf_1388_ = lean_ctor_get(v_s_1381_, 6);
v_exprToNatStructId_1389_ = lean_ctor_get(v_s_1381_, 7);
v___x_1390_ = lean_array_get_size(v_natStructs_1387_);
v___x_1391_ = lean_nat_dec_lt(v___y_1378_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_dec_ref(v_____x_1380_);
lean_dec_ref(v_e_1379_);
return v_s_1381_;
}
else
{
lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1428_; 
lean_inc_ref(v_exprToNatStructId_1389_);
lean_inc_ref(v_natTypeIdOf_1388_);
lean_inc_ref(v_natStructs_1387_);
lean_inc_ref(v_forbiddenNatModules_1386_);
lean_inc_ref(v_exprToStructIdEntries_1385_);
lean_inc_ref(v_exprToStructId_1384_);
lean_inc_ref(v_typeIdOf_1383_);
lean_inc_ref(v_structs_1382_);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_s_1381_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; lean_object* v_unused_1430_; lean_object* v_unused_1431_; lean_object* v_unused_1432_; lean_object* v_unused_1433_; lean_object* v_unused_1434_; lean_object* v_unused_1435_; lean_object* v_unused_1436_; 
v_unused_1429_ = lean_ctor_get(v_s_1381_, 7);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v_s_1381_, 6);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_s_1381_, 5);
lean_dec(v_unused_1431_);
v_unused_1432_ = lean_ctor_get(v_s_1381_, 4);
lean_dec(v_unused_1432_);
v_unused_1433_ = lean_ctor_get(v_s_1381_, 3);
lean_dec(v_unused_1433_);
v_unused_1434_ = lean_ctor_get(v_s_1381_, 2);
lean_dec(v_unused_1434_);
v_unused_1435_ = lean_ctor_get(v_s_1381_, 1);
lean_dec(v_unused_1435_);
v_unused_1436_ = lean_ctor_get(v_s_1381_, 0);
lean_dec(v_unused_1436_);
v___x_1393_ = v_s_1381_;
v_isShared_1394_ = v_isSharedCheck_1428_;
goto v_resetjp_1392_;
}
else
{
lean_dec(v_s_1381_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1428_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v_v_1395_; lean_object* v_id_1396_; lean_object* v_structId_1397_; lean_object* v_type_1398_; lean_object* v_u_1399_; lean_object* v_natModuleInst_1400_; lean_object* v_leInst_x3f_1401_; lean_object* v_ltInst_x3f_1402_; lean_object* v_lawfulOrderLTInst_x3f_1403_; lean_object* v_isPreorderInst_x3f_1404_; lean_object* v_orderedAddInst_x3f_1405_; lean_object* v_isLinearInst_x3f_1406_; lean_object* v_addRightCancelInst_x3f_1407_; lean_object* v_rfl__q_1408_; lean_object* v_zero_1409_; lean_object* v_toQFn_1410_; lean_object* v_addFn_1411_; lean_object* v_smulFn_1412_; lean_object* v_termMap_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1427_; 
v_v_1395_ = lean_array_fget(v_natStructs_1387_, v___y_1378_);
v_id_1396_ = lean_ctor_get(v_v_1395_, 0);
v_structId_1397_ = lean_ctor_get(v_v_1395_, 1);
v_type_1398_ = lean_ctor_get(v_v_1395_, 2);
v_u_1399_ = lean_ctor_get(v_v_1395_, 3);
v_natModuleInst_1400_ = lean_ctor_get(v_v_1395_, 4);
v_leInst_x3f_1401_ = lean_ctor_get(v_v_1395_, 5);
v_ltInst_x3f_1402_ = lean_ctor_get(v_v_1395_, 6);
v_lawfulOrderLTInst_x3f_1403_ = lean_ctor_get(v_v_1395_, 7);
v_isPreorderInst_x3f_1404_ = lean_ctor_get(v_v_1395_, 8);
v_orderedAddInst_x3f_1405_ = lean_ctor_get(v_v_1395_, 9);
v_isLinearInst_x3f_1406_ = lean_ctor_get(v_v_1395_, 10);
v_addRightCancelInst_x3f_1407_ = lean_ctor_get(v_v_1395_, 11);
v_rfl__q_1408_ = lean_ctor_get(v_v_1395_, 12);
v_zero_1409_ = lean_ctor_get(v_v_1395_, 13);
v_toQFn_1410_ = lean_ctor_get(v_v_1395_, 14);
v_addFn_1411_ = lean_ctor_get(v_v_1395_, 15);
v_smulFn_1412_ = lean_ctor_get(v_v_1395_, 16);
v_termMap_1413_ = lean_ctor_get(v_v_1395_, 17);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_v_1395_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1415_ = v_v_1395_;
v_isShared_1416_ = v_isSharedCheck_1427_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_termMap_1413_);
lean_inc(v_smulFn_1412_);
lean_inc(v_addFn_1411_);
lean_inc(v_toQFn_1410_);
lean_inc(v_zero_1409_);
lean_inc(v_rfl__q_1408_);
lean_inc(v_addRightCancelInst_x3f_1407_);
lean_inc(v_isLinearInst_x3f_1406_);
lean_inc(v_orderedAddInst_x3f_1405_);
lean_inc(v_isPreorderInst_x3f_1404_);
lean_inc(v_lawfulOrderLTInst_x3f_1403_);
lean_inc(v_ltInst_x3f_1402_);
lean_inc(v_leInst_x3f_1401_);
lean_inc(v_natModuleInst_1400_);
lean_inc(v_u_1399_);
lean_inc(v_type_1398_);
lean_inc(v_structId_1397_);
lean_inc(v_id_1396_);
lean_dec(v_v_1395_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1427_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v_xs_x27_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1417_ = lean_box(0);
v_xs_x27_1418_ = lean_array_fset(v_natStructs_1387_, v___y_1378_, v___x_1417_);
v___x_1419_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_termMap_1413_, v_e_1379_, v_____x_1380_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 17, v___x_1419_);
v___x_1421_ = v___x_1415_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_id_1396_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_structId_1397_);
lean_ctor_set(v_reuseFailAlloc_1426_, 2, v_type_1398_);
lean_ctor_set(v_reuseFailAlloc_1426_, 3, v_u_1399_);
lean_ctor_set(v_reuseFailAlloc_1426_, 4, v_natModuleInst_1400_);
lean_ctor_set(v_reuseFailAlloc_1426_, 5, v_leInst_x3f_1401_);
lean_ctor_set(v_reuseFailAlloc_1426_, 6, v_ltInst_x3f_1402_);
lean_ctor_set(v_reuseFailAlloc_1426_, 7, v_lawfulOrderLTInst_x3f_1403_);
lean_ctor_set(v_reuseFailAlloc_1426_, 8, v_isPreorderInst_x3f_1404_);
lean_ctor_set(v_reuseFailAlloc_1426_, 9, v_orderedAddInst_x3f_1405_);
lean_ctor_set(v_reuseFailAlloc_1426_, 10, v_isLinearInst_x3f_1406_);
lean_ctor_set(v_reuseFailAlloc_1426_, 11, v_addRightCancelInst_x3f_1407_);
lean_ctor_set(v_reuseFailAlloc_1426_, 12, v_rfl__q_1408_);
lean_ctor_set(v_reuseFailAlloc_1426_, 13, v_zero_1409_);
lean_ctor_set(v_reuseFailAlloc_1426_, 14, v_toQFn_1410_);
lean_ctor_set(v_reuseFailAlloc_1426_, 15, v_addFn_1411_);
lean_ctor_set(v_reuseFailAlloc_1426_, 16, v_smulFn_1412_);
lean_ctor_set(v_reuseFailAlloc_1426_, 17, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = lean_array_fset(v_xs_x27_1418_, v___y_1378_, v___x_1421_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 5, v___x_1422_);
v___x_1424_ = v___x_1393_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_structs_1382_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_typeIdOf_1383_);
lean_ctor_set(v_reuseFailAlloc_1425_, 2, v_exprToStructId_1384_);
lean_ctor_set(v_reuseFailAlloc_1425_, 3, v_exprToStructIdEntries_1385_);
lean_ctor_set(v_reuseFailAlloc_1425_, 4, v_forbiddenNatModules_1386_);
lean_ctor_set(v_reuseFailAlloc_1425_, 5, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1425_, 6, v_natTypeIdOf_1388_);
lean_ctor_set(v_reuseFailAlloc_1425_, 7, v_exprToNatStructId_1389_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0___boxed(lean_object* v___y_1437_, lean_object* v_e_1438_, lean_object* v_____x_1439_, lean_object* v_s_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0(v___y_1437_, v_e_1438_, v_____x_1439_, v_s_1440_);
lean_dec(v___y_1437_);
return v_res_1441_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofNatModule___closed__0(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
v___x_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
return v___x_1443_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule(lean_object* v_e_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v_____x_1458_; lean_object* v_fst_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1568_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1522_ = v___x_1519_;
v_isShared_1523_ = v_isSharedCheck_1568_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1568_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v_termMap_1524_; lean_object* v___x_1525_; 
v_termMap_1524_ = lean_ctor_get(v_a_1520_, 17);
lean_inc_ref(v_termMap_1524_);
lean_dec(v_a_1520_);
v___x_1525_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_termMap_1524_, v_e_1444_);
lean_dec_ref(v_termMap_1524_);
if (lean_obj_tag(v___x_1525_) == 1)
{
lean_object* v_val_1526_; lean_object* v___x_1528_; 
lean_dec_ref(v_e_1444_);
v_val_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_val_1526_);
lean_dec_ref_known(v___x_1525_, 1);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v_val_1526_);
v___x_1528_ = v___x_1522_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_val_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
else
{
lean_object* v___x_1530_; 
lean_dec(v___x_1525_);
lean_del_object(v___x_1522_);
lean_inc_ref(v_e_1444_);
v___x_1530_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_e_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v_fst_1532_; lean_object* v_snd_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1567_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v_fst_1532_ = lean_ctor_get(v_a_1531_, 0);
v_snd_1533_ = lean_ctor_get(v_a_1531_, 1);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_a_1531_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1535_ = v_a_1531_;
v_isShared_1536_ = v_isSharedCheck_1567_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_snd_1533_);
lean_inc(v_fst_1532_);
lean_dec(v_a_1531_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1567_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; 
lean_inc(v_a_1455_);
lean_inc_ref(v_a_1454_);
lean_inc(v_a_1453_);
lean_inc_ref(v_a_1452_);
lean_inc(v_a_1451_);
lean_inc_ref(v_a_1450_);
lean_inc(v_a_1449_);
lean_inc_ref(v_a_1448_);
lean_inc(v_a_1447_);
lean_inc(v_a_1446_);
v___x_1537_ = lean_grind_preprocess(v_fst_1532_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v_proof_x3f_1539_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
v_proof_x3f_1539_ = lean_ctor_get(v_a_1538_, 1);
if (lean_obj_tag(v_proof_x3f_1539_) == 1)
{
lean_object* v_expr_1540_; lean_object* v_val_1541_; lean_object* v___x_1542_; 
lean_inc_ref(v_proof_x3f_1539_);
v_expr_1540_ = lean_ctor_get(v_a_1538_, 0);
lean_inc_ref(v_expr_1540_);
lean_dec(v_a_1538_);
v_val_1541_ = lean_ctor_get(v_proof_x3f_1539_, 0);
lean_inc(v_val_1541_);
lean_dec_ref_known(v_proof_x3f_1539_, 1);
v___x_1542_ = l_Lean_Meta_mkEqTrans(v_snd_1533_, v_val_1541_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
lean_inc_ref(v_expr_1540_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 1, v_a_1543_);
lean_ctor_set(v___x_1535_, 0, v_expr_1540_);
v___x_1545_ = v___x_1535_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_expr_1540_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_a_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
v_____x_1458_ = v___x_1545_;
v_fst_1459_ = v_expr_1540_;
v___y_1460_ = v_a_1445_;
v___y_1461_ = v_a_1446_;
v___y_1462_ = v_a_1447_;
v___y_1463_ = v_a_1448_;
v___y_1464_ = v_a_1449_;
v___y_1465_ = v_a_1450_;
v___y_1466_ = v_a_1451_;
v___y_1467_ = v_a_1452_;
v___y_1468_ = v_a_1453_;
v___y_1469_ = v_a_1454_;
v___y_1470_ = v_a_1455_;
goto v___jp_1457_;
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec_ref(v_expr_1540_);
lean_del_object(v___x_1535_);
lean_dec_ref(v_e_1444_);
v_a_1547_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1542_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1542_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v_expr_1555_; lean_object* v___x_1557_; 
v_expr_1555_ = lean_ctor_get(v_a_1538_, 0);
lean_inc_ref_n(v_expr_1555_, 2);
lean_dec(v_a_1538_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v_expr_1555_);
v___x_1557_ = v___x_1535_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_expr_1555_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_snd_1533_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
v_____x_1458_ = v___x_1557_;
v_fst_1459_ = v_expr_1555_;
v___y_1460_ = v_a_1445_;
v___y_1461_ = v_a_1446_;
v___y_1462_ = v_a_1447_;
v___y_1463_ = v_a_1448_;
v___y_1464_ = v_a_1449_;
v___y_1465_ = v_a_1450_;
v___y_1466_ = v_a_1451_;
v___y_1467_ = v_a_1452_;
v___y_1468_ = v_a_1453_;
v___y_1469_ = v_a_1454_;
v___y_1470_ = v_a_1455_;
goto v___jp_1457_;
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_del_object(v___x_1535_);
lean_dec(v_snd_1533_);
lean_dec_ref(v_e_1444_);
v_a_1559_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1537_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1537_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1444_);
return v___x_1530_;
}
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec_ref(v_e_1444_);
v_a_1569_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1519_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1519_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
v___jp_1457_:
{
lean_object* v___f_1471_; lean_object* v___x_1472_; 
lean_inc_ref(v_____x_1458_);
lean_inc_ref(v_e_1444_);
lean_inc(v___y_1460_);
v___f_1471_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1471_, 0, v___y_1460_);
lean_closure_set(v___f_1471_, 1, v_e_1444_);
lean_closure_set(v___f_1471_, 2, v_____x_1458_);
v___x_1472_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1444_, v___y_1461_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v___x_1474_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofNatModule___closed__0, &l_Lean_Meta_Grind_Arith_Linear_ofNatModule___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofNatModule___closed__0);
lean_inc(v___y_1470_);
lean_inc_ref(v___y_1469_);
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
lean_inc(v___y_1464_);
lean_inc_ref(v___y_1463_);
lean_inc(v___y_1462_);
lean_inc(v___y_1461_);
v___x_1475_ = lean_grind_internalize(v_fst_1459_, v_a_1473_, v___x_1474_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v___x_1476_; 
lean_dec_ref_known(v___x_1475_, 1);
v___x_1476_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(v_e_1444_, v___y_1460_, v___y_1461_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec_ref_known(v___x_1476_, 1);
v___x_1477_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1478_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1477_, v___f_1471_, v___y_1461_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1485_ == 0)
{
lean_object* v_unused_1486_; 
v_unused_1486_ = lean_ctor_get(v___x_1478_, 0);
lean_dec(v_unused_1486_);
v___x_1480_ = v___x_1478_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_dec(v___x_1478_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v_____x_1458_);
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_____x_1458_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref(v_____x_1458_);
v_a_1487_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1478_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1478_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec_ref(v___f_1471_);
lean_dec_ref(v_____x_1458_);
v_a_1495_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1476_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1476_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec_ref(v___f_1471_);
lean_dec_ref(v_____x_1458_);
lean_dec_ref(v_e_1444_);
v_a_1503_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1475_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1475_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec_ref(v___f_1471_);
lean_dec_ref(v_fst_1459_);
lean_dec_ref(v_____x_1458_);
lean_dec_ref(v_e_1444_);
v_a_1511_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1472_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1472_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_ofNatModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1444_ = stack[0].m_obj;
lean_object* v_a_1445_ = stack[1].m_obj;
lean_object* v_a_1446_ = stack[2].m_obj;
lean_object* v_a_1447_ = stack[3].m_obj;
lean_object* v_a_1448_ = stack[4].m_obj;
lean_object* v_a_1449_ = stack[5].m_obj;
lean_object* v_a_1450_ = stack[6].m_obj;
lean_object* v_a_1451_ = stack[7].m_obj;
lean_object* v_a_1452_ = stack[8].m_obj;
lean_object* v_a_1453_ = stack[9].m_obj;
lean_object* v_a_1454_ = stack[10].m_obj;
lean_object* v_a_1455_ = stack[11].m_obj;
lean_object* v_res_1577_;
v_res_1577_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_e_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
stack->m_obj
 = v_res_1577_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___boxed(lean_object* v_e_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_e_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec(v_a_1580_);
lean_dec(v_a_1579_);
return v_res_1591_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = lean_box(0);
v___x_1593_ = lean_unsigned_to_nat(16u);
v___x_1594_ = lean_mk_array(v___x_1593_, v___x_1592_);
return v___x_1594_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1595_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0);
v___x_1596_ = lean_unsigned_to_nat(0u);
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
lean_ctor_set(v___x_1597_, 1, v___x_1595_);
return v___x_1597_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1600_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2));
v___x_1601_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1);
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
lean_ctor_set(v___x_1602_, 1, v___x_1600_);
return v___x_1602_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(lean_object* v_x_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
v___x_1617_ = lean_st_mk_ref(v___x_1616_);
lean_inc(v_a_1614_);
lean_inc_ref(v_a_1613_);
lean_inc(v_a_1612_);
lean_inc_ref(v_a_1611_);
lean_inc(v_a_1610_);
lean_inc_ref(v_a_1609_);
lean_inc(v_a_1608_);
lean_inc_ref(v_a_1607_);
lean_inc(v_a_1606_);
lean_inc(v_a_1605_);
lean_inc(v_a_1604_);
lean_inc(v___x_1617_);
v___x_1618_ = lean_apply_13(v_x_1603_, v___x_1617_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, lean_box(0));
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1627_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1623_ = lean_st_ref_get(v___x_1617_);
lean_dec(v___x_1617_);
lean_dec(v___x_1623_);
if (v_isShared_1622_ == 0)
{
v___x_1625_ = v___x_1621_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1619_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
else
{
lean_dec(v___x_1617_);
return v___x_1618_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1603_ = stack[0].m_obj;
lean_object* v_a_1604_ = stack[1].m_obj;
lean_object* v_a_1605_ = stack[2].m_obj;
lean_object* v_a_1606_ = stack[3].m_obj;
lean_object* v_a_1607_ = stack[4].m_obj;
lean_object* v_a_1608_ = stack[5].m_obj;
lean_object* v_a_1609_ = stack[6].m_obj;
lean_object* v_a_1610_ = stack[7].m_obj;
lean_object* v_a_1611_ = stack[8].m_obj;
lean_object* v_a_1612_ = stack[9].m_obj;
lean_object* v_a_1613_ = stack[10].m_obj;
lean_object* v_a_1614_ = stack[11].m_obj;
lean_object* v_res_1628_;
v_res_1628_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(v_x_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
stack->m_obj
 = v_res_1628_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___boxed(lean_object* v_x_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(v_x_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec(v_a_1630_);
return v_res_1642_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(lean_object* v_00_u03b1_1643_, lean_object* v_x_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1657_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
v___x_1658_ = lean_st_mk_ref(v___x_1657_);
lean_inc(v_a_1655_);
lean_inc_ref(v_a_1654_);
lean_inc(v_a_1653_);
lean_inc_ref(v_a_1652_);
lean_inc(v_a_1651_);
lean_inc_ref(v_a_1650_);
lean_inc(v_a_1649_);
lean_inc_ref(v_a_1648_);
lean_inc(v_a_1647_);
lean_inc(v_a_1646_);
lean_inc(v_a_1645_);
lean_inc(v___x_1658_);
v___x_1659_ = lean_apply_13(v_x_1644_, v___x_1658_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, lean_box(0));
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1668_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1664_ = lean_st_ref_get(v___x_1658_);
lean_dec(v___x_1658_);
lean_dec(v___x_1664_);
if (v_isShared_1663_ == 0)
{
v___x_1666_ = v___x_1662_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1660_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
else
{
lean_dec(v___x_1658_);
return v___x_1659_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1644_ = stack[1].m_obj;
lean_object* v_a_1645_ = stack[2].m_obj;
lean_object* v_a_1646_ = stack[3].m_obj;
lean_object* v_a_1647_ = stack[4].m_obj;
lean_object* v_a_1648_ = stack[5].m_obj;
lean_object* v_a_1649_ = stack[6].m_obj;
lean_object* v_a_1650_ = stack[7].m_obj;
lean_object* v_a_1651_ = stack[8].m_obj;
lean_object* v_a_1652_ = stack[9].m_obj;
lean_object* v_a_1653_ = stack[10].m_obj;
lean_object* v_a_1654_ = stack[11].m_obj;
lean_object* v_a_1655_ = stack[12].m_obj;
lean_object* v_res_1669_;
v_res_1669_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(lean_box(0), v_x_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
stack->m_obj
 = v_res_1669_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___boxed(lean_object* v_00_u03b1_1670_, lean_object* v_x_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(v_00_u03b1_1670_, v_x_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec(v_a_1672_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(lean_object* v_a_1685_, lean_object* v_b_1686_, lean_object* v_x_1687_){
_start:
{
if (lean_obj_tag(v_x_1687_) == 0)
{
lean_dec(v_b_1686_);
lean_dec_ref(v_a_1685_);
return v_x_1687_;
}
else
{
lean_object* v_key_1688_; lean_object* v_value_1689_; lean_object* v_tail_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1704_; 
v_key_1688_ = lean_ctor_get(v_x_1687_, 0);
v_value_1689_ = lean_ctor_get(v_x_1687_, 1);
v_tail_1690_ = lean_ctor_get(v_x_1687_, 2);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1692_ = v_x_1687_;
v_isShared_1693_ = v_isSharedCheck_1704_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_tail_1690_);
lean_inc(v_value_1689_);
lean_inc(v_key_1688_);
lean_dec(v_x_1687_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1704_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
size_t v___x_1694_; size_t v___x_1695_; uint8_t v___x_1696_; 
v___x_1694_ = lean_ptr_addr(v_key_1688_);
v___x_1695_ = lean_ptr_addr(v_a_1685_);
v___x_1696_ = lean_usize_dec_eq(v___x_1694_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1697_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_1685_, v_b_1686_, v_tail_1690_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 2, v___x_1697_);
v___x_1699_ = v___x_1692_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_key_1688_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_value_1689_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
else
{
lean_object* v___x_1702_; 
lean_dec(v_value_1689_);
lean_dec(v_key_1688_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 1, v_b_1686_);
lean_ctor_set(v___x_1692_, 0, v_a_1685_);
v___x_1702_ = v___x_1692_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1685_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_b_1686_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v_tail_1690_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1705_, lean_object* v_x_1706_){
_start:
{
if (lean_obj_tag(v_x_1706_) == 0)
{
return v_x_1705_;
}
else
{
lean_object* v_key_1707_; lean_object* v_value_1708_; lean_object* v_tail_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1735_; 
v_key_1707_ = lean_ctor_get(v_x_1706_, 0);
v_value_1708_ = lean_ctor_get(v_x_1706_, 1);
v_tail_1709_ = lean_ctor_get(v_x_1706_, 2);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_x_1706_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1711_ = v_x_1706_;
v_isShared_1712_ = v_isSharedCheck_1735_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_tail_1709_);
lean_inc(v_value_1708_);
lean_inc(v_key_1707_);
lean_dec(v_x_1706_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1735_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; size_t v___x_1714_; size_t v___x_1715_; size_t v___x_1716_; uint64_t v___x_1717_; uint64_t v___x_1718_; uint64_t v___x_1719_; uint64_t v_fold_1720_; uint64_t v___x_1721_; uint64_t v___x_1722_; uint64_t v___x_1723_; size_t v___x_1724_; size_t v___x_1725_; size_t v___x_1726_; size_t v___x_1727_; size_t v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1713_ = lean_array_get_size(v_x_1705_);
v___x_1714_ = lean_ptr_addr(v_key_1707_);
v___x_1715_ = ((size_t)3ULL);
v___x_1716_ = lean_usize_shift_right(v___x_1714_, v___x_1715_);
v___x_1717_ = lean_usize_to_uint64(v___x_1716_);
v___x_1718_ = 32ULL;
v___x_1719_ = lean_uint64_shift_right(v___x_1717_, v___x_1718_);
v_fold_1720_ = lean_uint64_xor(v___x_1717_, v___x_1719_);
v___x_1721_ = 16ULL;
v___x_1722_ = lean_uint64_shift_right(v_fold_1720_, v___x_1721_);
v___x_1723_ = lean_uint64_xor(v_fold_1720_, v___x_1722_);
v___x_1724_ = lean_uint64_to_usize(v___x_1723_);
v___x_1725_ = lean_usize_of_nat(v___x_1713_);
v___x_1726_ = ((size_t)1ULL);
v___x_1727_ = lean_usize_sub(v___x_1725_, v___x_1726_);
v___x_1728_ = lean_usize_land(v___x_1724_, v___x_1727_);
v___x_1729_ = lean_array_uget_borrowed(v_x_1705_, v___x_1728_);
lean_inc(v___x_1729_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 2, v___x_1729_);
v___x_1731_ = v___x_1711_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_key_1707_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_value_1708_);
lean_ctor_set(v_reuseFailAlloc_1734_, 2, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_array_uset(v_x_1705_, v___x_1728_, v___x_1731_);
v_x_1705_ = v___x_1732_;
v_x_1706_ = v_tail_1709_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1736_, lean_object* v_source_1737_, lean_object* v_target_1738_){
_start:
{
lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = lean_array_get_size(v_source_1737_);
v___x_1740_ = lean_nat_dec_lt(v_i_1736_, v___x_1739_);
if (v___x_1740_ == 0)
{
lean_dec_ref(v_source_1737_);
lean_dec(v_i_1736_);
return v_target_1738_;
}
else
{
lean_object* v_es_1741_; lean_object* v___x_1742_; lean_object* v_source_1743_; lean_object* v_target_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v_es_1741_ = lean_array_fget(v_source_1737_, v_i_1736_);
v___x_1742_ = lean_box(0);
v_source_1743_ = lean_array_fset(v_source_1737_, v_i_1736_, v___x_1742_);
v_target_1744_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1738_, v_es_1741_);
v___x_1745_ = lean_unsigned_to_nat(1u);
v___x_1746_ = lean_nat_add(v_i_1736_, v___x_1745_);
lean_dec(v_i_1736_);
v_i_1736_ = v___x_1746_;
v_source_1737_ = v_source_1743_;
v_target_1738_ = v_target_1744_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(lean_object* v_data_1748_){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v_nbuckets_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1749_ = lean_array_get_size(v_data_1748_);
v___x_1750_ = lean_unsigned_to_nat(2u);
v_nbuckets_1751_ = lean_nat_mul(v___x_1749_, v___x_1750_);
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1753_ = lean_box(0);
v___x_1754_ = lean_mk_array(v_nbuckets_1751_, v___x_1753_);
v___x_1755_ = lean_array_propagate_mark(v_data_1748_, v___x_1754_);
v___x_1756_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(v___x_1752_, v_data_1748_, v___x_1755_);
return v___x_1756_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(lean_object* v_a_1757_, lean_object* v_x_1758_){
_start:
{
if (lean_obj_tag(v_x_1758_) == 0)
{
uint8_t v___x_1759_; 
v___x_1759_ = 0;
return v___x_1759_;
}
else
{
lean_object* v_key_1760_; lean_object* v_tail_1761_; size_t v___x_1762_; size_t v___x_1763_; uint8_t v___x_1764_; 
v_key_1760_ = lean_ctor_get(v_x_1758_, 0);
v_tail_1761_ = lean_ctor_get(v_x_1758_, 2);
v___x_1762_ = lean_ptr_addr(v_key_1760_);
v___x_1763_ = lean_ptr_addr(v_a_1757_);
v___x_1764_ = lean_usize_dec_eq(v___x_1762_, v___x_1763_);
if (v___x_1764_ == 0)
{
v_x_1758_ = v_tail_1761_;
goto _start;
}
else
{
return v___x_1764_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1757_ = stack[0].m_obj;
lean_object* v_x_1758_ = stack[1].m_obj;
uint8_t v_res_1766_;
v_res_1766_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_1757_, v_x_1758_);
stack->m_num = v_res_1766_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg___boxed(lean_object* v_a_1767_, lean_object* v_x_1768_){
_start:
{
uint8_t v_res_1769_; lean_object* v_r_1770_; 
v_res_1769_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_1767_, v_x_1768_);
lean_dec(v_x_1768_);
lean_dec_ref(v_a_1767_);
v_r_1770_ = lean_box(v_res_1769_);
return v_r_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(lean_object* v_m_1771_, lean_object* v_a_1772_, lean_object* v_b_1773_){
_start:
{
lean_object* v_size_1774_; lean_object* v_buckets_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1821_; 
v_size_1774_ = lean_ctor_get(v_m_1771_, 0);
v_buckets_1775_ = lean_ctor_get(v_m_1771_, 1);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_m_1771_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1777_ = v_m_1771_;
v_isShared_1778_ = v_isSharedCheck_1821_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_buckets_1775_);
lean_inc(v_size_1774_);
lean_dec(v_m_1771_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1821_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; size_t v___x_1780_; size_t v___x_1781_; size_t v___x_1782_; uint64_t v___x_1783_; uint64_t v___x_1784_; uint64_t v___x_1785_; uint64_t v_fold_1786_; uint64_t v___x_1787_; uint64_t v___x_1788_; uint64_t v___x_1789_; size_t v___x_1790_; size_t v___x_1791_; size_t v___x_1792_; size_t v___x_1793_; size_t v___x_1794_; lean_object* v_bkt_1795_; uint8_t v___x_1796_; 
v___x_1779_ = lean_array_get_size(v_buckets_1775_);
v___x_1780_ = lean_ptr_addr(v_a_1772_);
v___x_1781_ = ((size_t)3ULL);
v___x_1782_ = lean_usize_shift_right(v___x_1780_, v___x_1781_);
v___x_1783_ = lean_usize_to_uint64(v___x_1782_);
v___x_1784_ = 32ULL;
v___x_1785_ = lean_uint64_shift_right(v___x_1783_, v___x_1784_);
v_fold_1786_ = lean_uint64_xor(v___x_1783_, v___x_1785_);
v___x_1787_ = 16ULL;
v___x_1788_ = lean_uint64_shift_right(v_fold_1786_, v___x_1787_);
v___x_1789_ = lean_uint64_xor(v_fold_1786_, v___x_1788_);
v___x_1790_ = lean_uint64_to_usize(v___x_1789_);
v___x_1791_ = lean_usize_of_nat(v___x_1779_);
v___x_1792_ = ((size_t)1ULL);
v___x_1793_ = lean_usize_sub(v___x_1791_, v___x_1792_);
v___x_1794_ = lean_usize_land(v___x_1790_, v___x_1793_);
v_bkt_1795_ = lean_array_uget_borrowed(v_buckets_1775_, v___x_1794_);
v___x_1796_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_1772_, v_bkt_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v_size_x27_1798_; lean_object* v___x_1799_; lean_object* v_buckets_x27_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1797_ = lean_unsigned_to_nat(1u);
v_size_x27_1798_ = lean_nat_add(v_size_1774_, v___x_1797_);
lean_dec(v_size_1774_);
lean_inc(v_bkt_1795_);
v___x_1799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1799_, 0, v_a_1772_);
lean_ctor_set(v___x_1799_, 1, v_b_1773_);
lean_ctor_set(v___x_1799_, 2, v_bkt_1795_);
v_buckets_x27_1800_ = lean_array_uset(v_buckets_1775_, v___x_1794_, v___x_1799_);
v___x_1801_ = lean_unsigned_to_nat(4u);
v___x_1802_ = lean_nat_mul(v_size_x27_1798_, v___x_1801_);
v___x_1803_ = lean_unsigned_to_nat(3u);
v___x_1804_ = lean_nat_div(v___x_1802_, v___x_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_array_get_size(v_buckets_x27_1800_);
v___x_1806_ = lean_nat_dec_le(v___x_1804_, v___x_1805_);
lean_dec(v___x_1804_);
if (v___x_1806_ == 0)
{
lean_object* v_val_1807_; lean_object* v___x_1809_; 
v_val_1807_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(v_buckets_x27_1800_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 1, v_val_1807_);
lean_ctor_set(v___x_1777_, 0, v_size_x27_1798_);
v___x_1809_ = v___x_1777_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_size_x27_1798_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_val_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
else
{
lean_object* v___x_1812_; 
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 1, v_buckets_x27_1800_);
lean_ctor_set(v___x_1777_, 0, v_size_x27_1798_);
v___x_1812_ = v___x_1777_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_size_x27_1798_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_buckets_x27_1800_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
else
{
lean_object* v___x_1814_; lean_object* v_buckets_x27_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
lean_inc(v_bkt_1795_);
v___x_1814_ = lean_box(0);
v_buckets_x27_1815_ = lean_array_uset(v_buckets_1775_, v___x_1794_, v___x_1814_);
v___x_1816_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_1772_, v_b_1773_, v_bkt_1795_);
v___x_1817_ = lean_array_uset(v_buckets_x27_1815_, v___x_1794_, v___x_1816_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 1, v___x_1817_);
v___x_1819_ = v___x_1777_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_size_1774_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(lean_object* v_a_1822_, lean_object* v_x_1823_){
_start:
{
if (lean_obj_tag(v_x_1823_) == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_box(0);
return v___x_1824_;
}
else
{
lean_object* v_key_1825_; lean_object* v_value_1826_; lean_object* v_tail_1827_; size_t v___x_1828_; size_t v___x_1829_; uint8_t v___x_1830_; 
v_key_1825_ = lean_ctor_get(v_x_1823_, 0);
v_value_1826_ = lean_ctor_get(v_x_1823_, 1);
v_tail_1827_ = lean_ctor_get(v_x_1823_, 2);
v___x_1828_ = lean_ptr_addr(v_key_1825_);
v___x_1829_ = lean_ptr_addr(v_a_1822_);
v___x_1830_ = lean_usize_dec_eq(v___x_1828_, v___x_1829_);
if (v___x_1830_ == 0)
{
v_x_1823_ = v_tail_1827_;
goto _start;
}
else
{
lean_object* v___x_1832_; 
lean_inc(v_value_1826_);
v___x_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1832_, 0, v_value_1826_);
return v___x_1832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_1833_, lean_object* v_x_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_1833_, v_x_1834_);
lean_dec(v_x_1834_);
lean_dec_ref(v_a_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(lean_object* v_m_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v_buckets_1838_; lean_object* v___x_1839_; size_t v___x_1840_; size_t v___x_1841_; size_t v___x_1842_; uint64_t v___x_1843_; uint64_t v___x_1844_; uint64_t v___x_1845_; uint64_t v_fold_1846_; uint64_t v___x_1847_; uint64_t v___x_1848_; uint64_t v___x_1849_; size_t v___x_1850_; size_t v___x_1851_; size_t v___x_1852_; size_t v___x_1853_; size_t v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_buckets_1838_ = lean_ctor_get(v_m_1836_, 1);
v___x_1839_ = lean_array_get_size(v_buckets_1838_);
v___x_1840_ = lean_ptr_addr(v_a_1837_);
v___x_1841_ = ((size_t)3ULL);
v___x_1842_ = lean_usize_shift_right(v___x_1840_, v___x_1841_);
v___x_1843_ = lean_usize_to_uint64(v___x_1842_);
v___x_1844_ = 32ULL;
v___x_1845_ = lean_uint64_shift_right(v___x_1843_, v___x_1844_);
v_fold_1846_ = lean_uint64_xor(v___x_1843_, v___x_1845_);
v___x_1847_ = 16ULL;
v___x_1848_ = lean_uint64_shift_right(v_fold_1846_, v___x_1847_);
v___x_1849_ = lean_uint64_xor(v_fold_1846_, v___x_1848_);
v___x_1850_ = lean_uint64_to_usize(v___x_1849_);
v___x_1851_ = lean_usize_of_nat(v___x_1839_);
v___x_1852_ = ((size_t)1ULL);
v___x_1853_ = lean_usize_sub(v___x_1851_, v___x_1852_);
v___x_1854_ = lean_usize_land(v___x_1850_, v___x_1853_);
v___x_1855_ = lean_array_uget_borrowed(v_buckets_1838_, v___x_1854_);
v___x_1856_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_1837_, v___x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg___boxed(lean_object* v_m_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_m_1857_, v_a_1858_);
lean_dec_ref(v_a_1858_);
lean_dec_ref(v_m_1857_);
return v_res_1859_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(lean_object* v_e_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v___x_1863_; lean_object* v_varMap_1864_; lean_object* v___x_1865_; 
v___x_1863_ = lean_st_ref_get(v_a_1861_);
v_varMap_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc_ref(v_varMap_1864_);
lean_dec(v___x_1863_);
v___x_1865_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_varMap_1864_, v_e_1860_);
lean_dec_ref(v_varMap_1864_);
if (lean_obj_tag(v___x_1865_) == 1)
{
lean_object* v_val_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1874_; 
lean_dec_ref(v_e_1860_);
v_val_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1874_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_val_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1874_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_val_1866_);
v___x_1871_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
return v___x_1872_;
}
}
}
else
{
lean_object* v___x_1875_; lean_object* v_vars_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v_varMap_1879_; lean_object* v_vars_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v___x_1865_);
v___x_1875_ = lean_st_ref_get(v_a_1861_);
v_vars_1876_ = lean_ctor_get(v___x_1875_, 1);
lean_inc_ref(v_vars_1876_);
lean_dec(v___x_1875_);
v___x_1877_ = lean_array_get_size(v_vars_1876_);
lean_dec_ref(v_vars_1876_);
v___x_1878_ = lean_st_ref_take(v_a_1861_);
v_varMap_1879_ = lean_ctor_get(v___x_1878_, 0);
v_vars_1880_ = lean_ctor_get(v___x_1878_, 1);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1882_ = v___x_1878_;
v_isShared_1883_ = v_isSharedCheck_1892_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_vars_1880_);
lean_inc(v_varMap_1879_);
lean_dec(v___x_1878_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1892_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1887_; 
lean_inc_ref(v_e_1860_);
v___x_1884_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(v_varMap_1879_, v_e_1860_, v___x_1877_);
v___x_1885_ = lean_array_push(v_vars_1880_, v_e_1860_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 1, v___x_1885_);
lean_ctor_set(v___x_1882_, 0, v___x_1884_);
v___x_1887_ = v___x_1882_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1888_ = lean_st_ref_put(v_a_1861_, v___x_1887_);
v___x_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1877_);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1860_ = stack[0].m_obj;
lean_object* v_a_1861_ = stack[1].m_obj;
lean_object* v_res_1893_;
v_res_1893_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1860_, v_a_1861_);
stack->m_obj
 = v_res_1893_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg___boxed(lean_object* v_e_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1894_, v_a_1895_);
lean_dec(v_a_1895_);
return v_res_1897_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(lean_object* v_e_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1898_, v_a_1899_);
return v___x_1912_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1898_ = stack[0].m_obj;
lean_object* v_a_1899_ = stack[1].m_obj;
lean_object* v_a_1900_ = stack[2].m_obj;
lean_object* v_a_1901_ = stack[3].m_obj;
lean_object* v_a_1902_ = stack[4].m_obj;
lean_object* v_a_1903_ = stack[5].m_obj;
lean_object* v_a_1904_ = stack[6].m_obj;
lean_object* v_a_1905_ = stack[7].m_obj;
lean_object* v_a_1906_ = stack[8].m_obj;
lean_object* v_a_1907_ = stack[9].m_obj;
lean_object* v_a_1908_ = stack[10].m_obj;
lean_object* v_a_1909_ = stack[11].m_obj;
lean_object* v_a_1910_ = stack[12].m_obj;
lean_object* v_res_1913_;
v_res_1913_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(v_e_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
stack->m_obj
 = v_res_1913_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___boxed(lean_object* v_e_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(v_e_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec(v_a_1916_);
lean_dec(v_a_1915_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0(lean_object* v_00_u03b2_1929_, lean_object* v_m_1930_, lean_object* v_a_1931_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_m_1930_, v_a_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___boxed(lean_object* v_00_u03b2_1933_, lean_object* v_m_1934_, lean_object* v_a_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0(v_00_u03b2_1933_, v_m_1934_, v_a_1935_);
lean_dec_ref(v_a_1935_);
lean_dec_ref(v_m_1934_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1(lean_object* v_00_u03b2_1937_, lean_object* v_m_1938_, lean_object* v_a_1939_, lean_object* v_b_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(v_m_1938_, v_a_1939_, v_b_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0(lean_object* v_00_u03b2_1942_, lean_object* v_a_1943_, lean_object* v_x_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_1943_, v_x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1946_, lean_object* v_a_1947_, lean_object* v_x_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0(v_00_u03b2_1946_, v_a_1947_, v_x_1948_);
lean_dec(v_x_1948_);
lean_dec_ref(v_a_1947_);
return v_res_1949_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(lean_object* v_00_u03b2_1950_, lean_object* v_a_1951_, lean_object* v_x_1952_){
_start:
{
uint8_t v___x_1953_; 
v___x_1953_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_1951_, v_x_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1951_ = stack[1].m_obj;
lean_object* v_x_1952_ = stack[2].m_obj;
uint8_t v_res_1954_;
v_res_1954_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(lean_box(0), v_a_1951_, v_x_1952_);
stack->m_num = v_res_1954_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1955_, lean_object* v_a_1956_, lean_object* v_x_1957_){
_start:
{
uint8_t v_res_1958_; lean_object* v_r_1959_; 
v_res_1958_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(v_00_u03b2_1955_, v_a_1956_, v_x_1957_);
lean_dec(v_x_1957_);
lean_dec_ref(v_a_1956_);
v_r_1959_ = lean_box(v_res_1958_);
return v_r_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3(lean_object* v_00_u03b2_1960_, lean_object* v_data_1961_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(v_data_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4(lean_object* v_00_u03b2_1963_, lean_object* v_a_1964_, lean_object* v_b_1965_, lean_object* v_x_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_1964_, v_b_1965_, v_x_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1968_, lean_object* v_i_1969_, lean_object* v_source_1970_, lean_object* v_target_1971_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(v_i_1969_, v_source_1970_, v_target_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1973_, lean_object* v_x_1974_, lean_object* v_x_1975_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1974_, v_x_1975_);
return v___x_1976_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(lean_object* v_e_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1993_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
lean_inc_ref(v_e_1977_);
v___x_1993_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1977_, v_a_1987_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2094_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2094_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2094_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1998_ = l_Lean_Expr_cleanupAnnotations(v_a_1994_);
v___x_1999_ = l_Lean_Expr_isApp(v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; 
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1996_);
lean_dec(v_a_1992_);
v___x_2000_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1977_, v_a_1978_);
return v___x_2000_;
}
else
{
lean_object* v_arg_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v_arg_2001_ = lean_ctor_get(v___x_1998_, 1);
lean_inc_ref(v_arg_2001_);
v___x_2002_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1998_);
v___x_2003_ = l_Lean_Expr_isApp(v___x_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; 
lean_dec_ref(v___x_2002_);
lean_dec_ref(v_arg_2001_);
lean_del_object(v___x_1996_);
lean_dec(v_a_1992_);
v___x_2004_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1977_, v_a_1978_);
return v___x_2004_;
}
else
{
lean_object* v_arg_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v_arg_2005_ = lean_ctor_get(v___x_2002_, 1);
lean_inc_ref(v_arg_2005_);
v___x_2006_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2002_);
v___x_2007_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2));
v___x_2008_ = l_Lean_Expr_isConstOf(v___x_2006_, v___x_2007_);
if (v___x_2008_ == 0)
{
uint8_t v___x_2009_; 
lean_del_object(v___x_1996_);
v___x_2009_ = l_Lean_Expr_isApp(v___x_2006_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; 
lean_dec_ref(v___x_2006_);
lean_dec_ref(v_arg_2005_);
lean_dec_ref(v_arg_2001_);
lean_dec(v_a_1992_);
v___x_2010_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1977_, v_a_1978_);
return v___x_2010_;
}
else
{
lean_object* v_arg_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v_arg_2011_ = lean_ctor_get(v___x_2006_, 1);
lean_inc_ref(v_arg_2011_);
v___x_2012_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2006_);
v___x_2013_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5));
v___x_2014_ = l_Lean_Expr_isConstOf(v___x_2012_, v___x_2013_);
if (v___x_2014_ == 0)
{
uint8_t v___x_2015_; 
v___x_2015_ = l_Lean_Expr_isApp(v___x_2012_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; 
lean_dec_ref(v___x_2012_);
lean_dec_ref(v_arg_2011_);
lean_dec_ref(v_arg_2005_);
lean_dec_ref(v_arg_2001_);
lean_dec(v_a_1992_);
v___x_2016_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1977_, v_a_1978_);
return v___x_2016_;
}
else
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2012_);
v___x_2018_ = l_Lean_Expr_isApp(v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; 
lean_dec_ref(v___x_2017_);
lean_dec_ref(v_arg_2011_);
lean_dec_ref(v_arg_2005_);
lean_dec_ref(v_arg_2001_);
lean_dec(v_a_1992_);
v___x_2019_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1977_, v_a_1978_);
return v___x_2019_;
}
else
{
lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2020_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2017_);
v___x_2021_ = l_Lean_Expr_isApp(v___x_2020_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; 
lean_dec_ref(v___x_2020_);
lean_dec_ref(v_arg_2011_);
lean_dec_ref(v_arg_2005_);
lean_dec_ref(v_arg_2001_);
lean_dec(v_a_1992_);
v___x_2022_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1977_, v_a_1978_);
return v___x_2022_;
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2023_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2020_);
v___x_2024_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8));
v___x_2025_ = l_Lean_Expr_isConstOf(v___x_2023_, v___x_2024_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11));
v___x_2027_ = l_Lean_Expr_isConstOf(v___x_2023_, v___x_2026_);
lean_dec_ref(v___x_2023_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; 
lean_dec_ref(v_arg_2011_);
lean_dec_ref(v_arg_2005_);
lean_dec_ref(v_arg_2001_);
lean_dec(v_a_1992_);
v___x_2028_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1977_, v_a_1978_);
return v___x_2028_;
}
else
{
uint8_t v___x_2029_; 
v___x_2029_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_1992_, v_arg_2011_);
lean_dec_ref(v_arg_2011_);
lean_dec(v_a_1992_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; 
lean_dec_ref(v_arg_2005_);
lean_dec_ref(v_arg_2001_);
v___x_2030_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1977_, v_a_1978_);
return v___x_2030_;
}
else
{
lean_object* v___x_2031_; 
lean_dec_ref(v_e_1977_);
v___x_2031_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_2005_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2033_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2033_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_2001_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2042_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2036_ = v___x_2033_;
v_isShared_2037_ = v_isSharedCheck_2042_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2042_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2038_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2038_, 0, v_a_2032_);
lean_ctor_set(v___x_2038_, 1, v_a_2034_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2038_);
v___x_2040_ = v___x_2036_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
else
{
lean_dec(v_a_2032_);
return v___x_2033_;
}
}
else
{
lean_dec_ref(v_arg_2001_);
return v___x_2031_;
}
}
}
}
else
{
uint8_t v___x_2043_; 
lean_dec_ref(v___x_2023_);
v___x_2043_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_a_1992_, v_arg_2011_);
lean_dec_ref(v_arg_2011_);
lean_dec(v_a_1992_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; 
lean_dec_ref(v_arg_2005_);
lean_dec_ref(v_arg_2001_);
v___x_2044_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1977_, v_a_1978_);
return v___x_2044_;
}
else
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_Meta_getNatValue_x3f(v_arg_2005_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
lean_dec_ref(v_arg_2005_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
if (lean_obj_tag(v_a_2046_) == 1)
{
lean_object* v_val_2047_; lean_object* v___x_2048_; 
lean_dec_ref(v_e_1977_);
v_val_2047_ = lean_ctor_get(v_a_2046_, 0);
lean_inc(v_val_2047_);
lean_dec_ref_known(v_a_2046_, 1);
v___x_2048_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_2001_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2057_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2057_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2057_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2053_, 0, v_val_2047_);
lean_ctor_set(v___x_2053_, 1, v_a_2049_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2053_);
v___x_2055_ = v___x_2051_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
else
{
lean_dec(v_val_2047_);
return v___x_2048_;
}
}
else
{
lean_object* v___x_2058_; 
lean_dec(v_a_2046_);
lean_dec_ref(v_arg_2001_);
v___x_2058_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1977_, v_a_1978_);
return v___x_2058_;
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v_arg_2001_);
lean_dec_ref(v_e_1977_);
v_a_2059_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2045_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2045_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
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
lean_object* v_zero_2067_; lean_object* v___x_2068_; 
lean_dec_ref(v___x_2012_);
lean_dec_ref(v_arg_2011_);
lean_dec_ref(v_arg_2005_);
lean_dec_ref(v_arg_2001_);
v_zero_2067_ = lean_ctor_get(v_a_1992_, 13);
lean_inc_ref(v_zero_2067_);
lean_dec(v_a_1992_);
lean_inc_ref(v_e_1977_);
v___x_2068_ = l_Lean_Meta_isDefEqD(v_e_1977_, v_zero_2067_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2079_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2079_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2079_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
uint8_t v___x_2073_; 
v___x_2073_ = lean_unbox(v_a_2069_);
lean_dec(v_a_2069_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; 
lean_del_object(v___x_2071_);
v___x_2074_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1977_, v_a_1978_);
return v___x_2074_;
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
lean_dec_ref(v_e_1977_);
v___x_2075_ = lean_box(0);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 0, v___x_2075_);
v___x_2077_ = v___x_2071_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec_ref(v_e_1977_);
v_a_2080_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2068_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2068_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
}
else
{
uint8_t v___x_2088_; 
lean_dec_ref(v___x_2006_);
lean_dec_ref(v_arg_2005_);
v___x_2088_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_1992_, v_arg_2001_);
lean_dec_ref(v_arg_2001_);
lean_dec(v_a_1992_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; 
lean_del_object(v___x_1996_);
v___x_2089_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1977_, v_a_1978_);
return v___x_2089_;
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
lean_dec_ref(v_e_1977_);
v___x_2090_ = lean_box(0);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_2090_);
v___x_2092_ = v___x_1996_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec(v_a_1992_);
lean_dec_ref(v_e_1977_);
v_a_2095_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_1993_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_1993_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec_ref(v_e_1977_);
v_a_2103_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_1991_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_1991_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1977_ = stack[0].m_obj;
lean_object* v_a_1978_ = stack[1].m_obj;
lean_object* v_a_1979_ = stack[2].m_obj;
lean_object* v_a_1980_ = stack[3].m_obj;
lean_object* v_a_1981_ = stack[4].m_obj;
lean_object* v_a_1982_ = stack[5].m_obj;
lean_object* v_a_1983_ = stack[6].m_obj;
lean_object* v_a_1984_ = stack[7].m_obj;
lean_object* v_a_1985_ = stack[8].m_obj;
lean_object* v_a_1986_ = stack[9].m_obj;
lean_object* v_a_1987_ = stack[10].m_obj;
lean_object* v_a_1988_ = stack[11].m_obj;
lean_object* v_a_1989_ = stack[12].m_obj;
lean_object* v_res_2111_;
v_res_2111_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_e_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
stack->m_obj
 = v_res_2111_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify___boxed(lean_object* v_e_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_e_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec(v_a_2113_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(lean_object* v___y_2127_){
_start:
{
lean_inc_ref(v___y_2127_);
return v___y_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___boxed(lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(v___y_2128_);
lean_dec_ref(v___y_2128_);
return v_res_2129_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2(lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_b_2141_, lean_object* v_ctx_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_type_2156_; lean_object* v_u_2157_; lean_object* v_natModuleInst_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v_type_2156_ = lean_ctor_get(v_a_2137_, 2);
lean_inc_ref(v_type_2156_);
v_u_2157_ = lean_ctor_get(v_a_2137_, 3);
lean_inc(v_u_2157_);
v_natModuleInst_2158_ = lean_ctor_get(v_a_2137_, 4);
lean_inc_ref(v_natModuleInst_2158_);
lean_dec_ref(v_a_2137_);
v___x_2159_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___closed__2));
v___x_2160_ = lean_box(0);
v___x_2161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2161_, 0, v_u_2157_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = l_Lean_mkConst(v___x_2159_, v___x_2161_);
v___x_2163_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_2138_);
v___x_2164_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_2139_);
v___x_2165_ = l_Lean_eagerReflBoolTrue;
v___x_2166_ = l_Lean_mkApp6(v___x_2162_, v_type_2156_, v_natModuleInst_2158_, v_ctx_2142_, v___x_2163_, v___x_2164_, v___x_2165_);
v___x_2167_ = l_Lean_Meta_Grind_mkDiseqProof(v_a_2140_, v_b_2141_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
v___x_2169_ = l_Lean_Expr_app___override(v_a_2168_, v___x_2166_);
v___x_2170_ = l_Lean_Meta_Grind_closeGoal(v___x_2169_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
return v___x_2170_;
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec_ref(v___x_2166_);
v_a_2171_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2167_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2167_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2137_ = stack[0].m_obj;
lean_object* v_a_2138_ = stack[1].m_obj;
lean_object* v_a_2139_ = stack[2].m_obj;
lean_object* v_a_2140_ = stack[3].m_obj;
lean_object* v_b_2141_ = stack[4].m_obj;
lean_object* v_ctx_2142_ = stack[5].m_obj;
lean_object* v___y_2143_ = stack[6].m_obj;
lean_object* v___y_2144_ = stack[7].m_obj;
lean_object* v___y_2145_ = stack[8].m_obj;
lean_object* v___y_2146_ = stack[9].m_obj;
lean_object* v___y_2147_ = stack[10].m_obj;
lean_object* v___y_2148_ = stack[11].m_obj;
lean_object* v___y_2149_ = stack[12].m_obj;
lean_object* v___y_2150_ = stack[13].m_obj;
lean_object* v___y_2151_ = stack[14].m_obj;
lean_object* v___y_2152_ = stack[15].m_obj;
lean_object* v___y_2153_ = stack[16].m_obj;
lean_object* v___y_2154_ = stack[17].m_obj;
lean_object* v_res_2179_;
v_res_2179_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2(v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_b_2141_, v_ctx_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
stack->m_obj
 = v_res_2179_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2___boxed(lean_object** _args){
lean_object* v_a_2180_ = _args[0];
lean_object* v_a_2181_ = _args[1];
lean_object* v_a_2182_ = _args[2];
lean_object* v_a_2183_ = _args[3];
lean_object* v_b_2184_ = _args[4];
lean_object* v_ctx_2185_ = _args[5];
lean_object* v___y_2186_ = _args[6];
lean_object* v___y_2187_ = _args[7];
lean_object* v___y_2188_ = _args[8];
lean_object* v___y_2189_ = _args[9];
lean_object* v___y_2190_ = _args[10];
lean_object* v___y_2191_ = _args[11];
lean_object* v___y_2192_ = _args[12];
lean_object* v___y_2193_ = _args[13];
lean_object* v___y_2194_ = _args[14];
lean_object* v___y_2195_ = _args[15];
lean_object* v___y_2196_ = _args[16];
lean_object* v___y_2197_ = _args[17];
lean_object* v___y_2198_ = _args[18];
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2(v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_b_2184_, v_ctx_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec(v___y_2186_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(lean_object* v_vars_2200_, lean_object* v_x_2201_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_array_fget_borrowed(v_vars_2200_, v_x_2201_);
lean_inc(v___x_2202_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1___boxed(lean_object* v_vars_2203_, lean_object* v_x_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(v_vars_2203_, v_x_2204_);
lean_dec(v_x_2204_);
lean_dec_ref(v_vars_2203_);
return v_res_2205_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(lean_object* v_a_2207_, lean_object* v_b_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v___f_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v_a_2226_; lean_object* v___y_2230_; lean_object* v___x_2232_; 
v___f_2221_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0));
v___x_2222_ = lean_unsigned_to_nat(0u);
v___x_2223_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
v___x_2224_ = lean_st_mk_ref(v___x_2223_);
lean_inc_ref(v_a_2207_);
v___x_2232_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_a_2207_, v___x_2224_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2234_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
lean_inc_ref(v_b_2208_);
v___x_2234_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_b_2208_, v___x_2224_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; uint8_t v___x_2238_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc_n(v_a_2235_, 2);
lean_dec_ref_known(v___x_2234_, 1);
lean_inc(v_a_2233_);
v___x_2236_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_2233_);
v___x_2237_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_2235_);
v___x_2238_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_2236_, v___x_2237_);
lean_dec(v___x_2237_);
lean_dec(v___x_2236_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; 
lean_dec(v_a_2235_);
lean_dec(v_a_2233_);
lean_dec_ref(v_b_2208_);
lean_dec_ref(v_a_2207_);
v___x_2239_ = lean_box(0);
v_a_2226_ = v___x_2239_;
goto v___jp_2225_;
}
else
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2242_; lean_object* v_vars_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2240_, 1);
v___x_2242_ = lean_st_ref_get(v___x_2224_);
v_vars_2243_ = lean_ctor_get(v___x_2242_, 1);
lean_inc_ref(v_vars_2243_);
lean_dec(v___x_2242_);
v___x_2244_ = lean_array_get_size(v_vars_2243_);
v___x_2245_ = lean_nat_dec_lt(v___x_2222_, v___x_2244_);
if (v___x_2245_ == 0)
{
lean_object* v_type_2246_; lean_object* v_zero_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_dec_ref(v_vars_2243_);
v_type_2246_ = lean_ctor_get(v_a_2241_, 2);
v_zero_2247_ = lean_ctor_get(v_a_2241_, 13);
lean_inc_ref(v_zero_2247_);
v___x_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2248_, 0, v_zero_2247_);
lean_inc_ref(v_type_2246_);
v___x_2249_ = l_Lean_RArray_toExpr___redArg(v_type_2246_, v___f_2221_, v___x_2248_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2251_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2250_);
lean_dec_ref_known(v___x_2249_, 1);
v___x_2251_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2(v_a_2241_, v_a_2233_, v_a_2235_, v_a_2207_, v_b_2208_, v_a_2250_, v___x_2224_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
v___y_2230_ = v___x_2251_;
goto v___jp_2229_;
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_dec(v_a_2241_);
lean_dec(v_a_2235_);
lean_dec(v_a_2233_);
lean_dec(v___x_2224_);
lean_dec_ref(v_b_2208_);
lean_dec_ref(v_a_2207_);
v_a_2252_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2249_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2249_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
else
{
lean_object* v_type_2260_; lean_object* v___f_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v_type_2260_ = lean_ctor_get(v_a_2241_, 2);
v___f_2261_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2261_, 0, v_vars_2243_);
v___x_2262_ = l_Lean_RArray_ofFn___redArg(v___x_2244_, v___f_2261_);
lean_inc_ref(v_type_2260_);
v___x_2263_ = l_Lean_RArray_toExpr___redArg(v_type_2260_, v___f_2221_, v___x_2262_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2265_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2264_);
lean_dec_ref_known(v___x_2263_, 1);
v___x_2265_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__2(v_a_2241_, v_a_2233_, v_a_2235_, v_a_2207_, v_b_2208_, v_a_2264_, v___x_2224_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
v___y_2230_ = v___x_2265_;
goto v___jp_2229_;
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_a_2241_);
lean_dec(v_a_2235_);
lean_dec(v_a_2233_);
lean_dec(v___x_2224_);
lean_dec_ref(v_b_2208_);
lean_dec_ref(v_a_2207_);
v_a_2266_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2263_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2263_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec(v_a_2235_);
lean_dec(v_a_2233_);
lean_dec(v___x_2224_);
lean_dec_ref(v_b_2208_);
lean_dec_ref(v_a_2207_);
v_a_2274_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2240_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2240_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec(v_a_2233_);
lean_dec(v___x_2224_);
lean_dec_ref(v_b_2208_);
lean_dec_ref(v_a_2207_);
v_a_2282_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2234_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2234_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v___x_2224_);
lean_dec_ref(v_b_2208_);
lean_dec_ref(v_a_2207_);
v_a_2290_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2232_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2232_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
v___jp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_st_ref_get(v___x_2224_);
lean_dec(v___x_2224_);
lean_dec(v___x_2227_);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v_a_2226_);
return v___x_2228_;
}
v___jp_2229_:
{
if (lean_obj_tag(v___y_2230_) == 0)
{
lean_object* v_a_2231_; 
v_a_2231_ = lean_ctor_get(v___y_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v___y_2230_, 1);
v_a_2226_ = v_a_2231_;
goto v___jp_2225_;
}
else
{
lean_dec(v___x_2224_);
return v___y_2230_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2207_ = stack[0].m_obj;
lean_object* v_b_2208_ = stack[1].m_obj;
lean_object* v_a_2209_ = stack[2].m_obj;
lean_object* v_a_2210_ = stack[3].m_obj;
lean_object* v_a_2211_ = stack[4].m_obj;
lean_object* v_a_2212_ = stack[5].m_obj;
lean_object* v_a_2213_ = stack[6].m_obj;
lean_object* v_a_2214_ = stack[7].m_obj;
lean_object* v_a_2215_ = stack[8].m_obj;
lean_object* v_a_2216_ = stack[9].m_obj;
lean_object* v_a_2217_ = stack[10].m_obj;
lean_object* v_a_2218_ = stack[11].m_obj;
lean_object* v_a_2219_ = stack[12].m_obj;
lean_object* v_res_2298_;
v_res_2298_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_2207_, v_b_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
stack->m_obj
 = v_res_2298_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___boxed(lean_object* v_a_2299_, lean_object* v_b_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_2299_, v_b_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
lean_dec(v_a_2302_);
lean_dec(v_a_2301_);
return v_res_2313_;
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
