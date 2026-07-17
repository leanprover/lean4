// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.OfNatModule
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM import Init.Grind.Module.OfNatModule import Init.Grind.Module.NatModuleNorm import Lean.Meta.Tactic.Grind.Diseq import Lean.Meta.Tactic.Grind.Arith.Linear.ToExpr import Init.Data.Nat.Order import Init.Data.Order.Lemmas import Lean.Data.RArray
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
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
lean_object* l_Lean_Meta_Grind_mkDiseqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Linarith"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "eq_normN"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 207, 141, 119, 115, 174, 198, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(126, 34, 3, 158, 236, 88, 5, 190)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v___x_97_; lean_object* v_env_98_; lean_object* v___x_99_; lean_object* v_mctx_100_; lean_object* v_lctx_101_; lean_object* v_options_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_97_ = lean_st_ref_get(v___y_95_);
v_env_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref(v_env_98_);
lean_dec(v___x_97_);
v___x_99_ = lean_st_ref_get(v___y_93_);
v_mctx_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc_ref(v_mctx_100_);
lean_dec(v___x_99_);
v_lctx_101_ = lean_ctor_get(v___y_92_, 2);
v_options_102_ = lean_ctor_get(v___y_94_, 2);
lean_inc_ref(v_options_102_);
lean_inc_ref(v_lctx_101_);
v___x_103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_103_, 0, v_env_98_);
lean_ctor_set(v___x_103_, 1, v_mctx_100_);
lean_ctor_set(v___x_103_, 2, v_lctx_101_);
lean_ctor_set(v___x_103_, 3, v_options_102_);
v___x_104_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v_msgData_91_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0___boxed(lean_object* v_msgData_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(v_msgData_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(lean_object* v_msg_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_ref_119_; lean_object* v___x_120_; lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_129_; 
v_ref_119_ = lean_ctor_get(v___y_116_, 5);
v___x_120_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(v_msg_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_129_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
lean_inc(v_ref_119_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v_ref_119_);
lean_ctor_set(v___x_125_, 1, v_a_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 1);
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg___boxed(lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(v_msg_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_136_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0));
v___x_139_ = l_Lean_stringToMessageData(v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct(lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_141_, v_a_149_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_166_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_166_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_166_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_166_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v_natStructs_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_natStructs_157_ = lean_ctor_get(v_a_153_, 5);
lean_inc_ref(v_natStructs_157_);
lean_dec(v_a_153_);
v___x_158_ = lean_array_get_size(v_natStructs_157_);
v___x_159_ = lean_nat_dec_lt(v_a_140_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec_ref(v_natStructs_157_);
lean_del_object(v___x_155_);
v___x_160_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1);
v___x_161_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(v___x_160_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
return v___x_161_;
}
else
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_array_fget(v_natStructs_157_, v_a_140_);
lean_dec_ref(v_natStructs_157_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_162_);
v___x_164_ = v___x_155_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
v_a_167_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_152_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_152_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct___boxed(lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec(v_a_176_);
lean_dec(v_a_175_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0(lean_object* v_00_u03b1_188_, lean_object* v_msg_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(v_msg_189_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___boxed(lean_object* v_00_u03b1_203_, lean_object* v_msg_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0(v_00_u03b1_203_, v_msg_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec(v___y_206_);
lean_dec(v___y_205_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v_structId_232_; lean_object* v___x_233_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_230_, 1);
v_structId_232_ = lean_ctor_get(v_a_231_, 1);
lean_inc(v_structId_232_);
lean_dec(v_a_231_);
v___x_233_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_structId_232_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
lean_dec(v_structId_232_);
return v___x_233_;
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
v_a_234_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_230_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_230_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct___boxed(lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec(v_a_243_);
lean_dec(v_a_242_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0(lean_object* v_a_256_, lean_object* v_f_257_, lean_object* v_s_258_){
_start:
{
lean_object* v_structs_259_; lean_object* v_typeIdOf_260_; lean_object* v_exprToStructId_261_; lean_object* v_exprToStructIdEntries_262_; lean_object* v_forbiddenNatModules_263_; lean_object* v_natStructs_264_; lean_object* v_natTypeIdOf_265_; lean_object* v_exprToNatStructId_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_structs_259_ = lean_ctor_get(v_s_258_, 0);
v_typeIdOf_260_ = lean_ctor_get(v_s_258_, 1);
v_exprToStructId_261_ = lean_ctor_get(v_s_258_, 2);
v_exprToStructIdEntries_262_ = lean_ctor_get(v_s_258_, 3);
v_forbiddenNatModules_263_ = lean_ctor_get(v_s_258_, 4);
v_natStructs_264_ = lean_ctor_get(v_s_258_, 5);
v_natTypeIdOf_265_ = lean_ctor_get(v_s_258_, 6);
v_exprToNatStructId_266_ = lean_ctor_get(v_s_258_, 7);
v___x_267_ = lean_array_get_size(v_natStructs_264_);
v___x_268_ = lean_nat_dec_lt(v_a_256_, v___x_267_);
if (v___x_268_ == 0)
{
lean_dec_ref(v_f_257_);
return v_s_258_;
}
else
{
lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_280_; 
lean_inc_ref(v_exprToNatStructId_266_);
lean_inc_ref(v_natTypeIdOf_265_);
lean_inc_ref(v_natStructs_264_);
lean_inc_ref(v_forbiddenNatModules_263_);
lean_inc_ref(v_exprToStructIdEntries_262_);
lean_inc_ref(v_exprToStructId_261_);
lean_inc_ref(v_typeIdOf_260_);
lean_inc_ref(v_structs_259_);
v_isSharedCheck_280_ = !lean_is_exclusive(v_s_258_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; lean_object* v_unused_284_; lean_object* v_unused_285_; lean_object* v_unused_286_; lean_object* v_unused_287_; lean_object* v_unused_288_; 
v_unused_281_ = lean_ctor_get(v_s_258_, 7);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_s_258_, 6);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_s_258_, 5);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v_s_258_, 4);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_s_258_, 3);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_s_258_, 2);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_s_258_, 1);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v_s_258_, 0);
lean_dec(v_unused_288_);
v___x_270_ = v_s_258_;
v_isShared_271_ = v_isSharedCheck_280_;
goto v_resetjp_269_;
}
else
{
lean_dec(v_s_258_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_280_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v_v_272_; lean_object* v___x_273_; lean_object* v_xs_x27_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v_v_272_ = lean_array_fget(v_natStructs_264_, v_a_256_);
v___x_273_ = lean_box(0);
v_xs_x27_274_ = lean_array_fset(v_natStructs_264_, v_a_256_, v___x_273_);
v___x_275_ = lean_apply_1(v_f_257_, v_v_272_);
v___x_276_ = lean_array_fset(v_xs_x27_274_, v_a_256_, v___x_275_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 5, v___x_276_);
v___x_278_ = v___x_270_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_structs_259_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_typeIdOf_260_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_exprToStructId_261_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_exprToStructIdEntries_262_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_forbiddenNatModules_263_);
lean_ctor_set(v_reuseFailAlloc_279_, 5, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_279_, 6, v_natTypeIdOf_265_);
lean_ctor_set(v_reuseFailAlloc_279_, 7, v_exprToNatStructId_266_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed(lean_object* v_a_289_, lean_object* v_f_290_, lean_object* v_s_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0(v_a_289_, v_f_290_, v_s_291_);
lean_dec(v_a_289_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg(lean_object* v_f_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___f_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_inc(v_a_294_);
v___f_297_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_297_, 0, v_a_294_);
lean_closure_set(v___f_297_, 1, v_f_293_);
v___x_298_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_299_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_298_, v___f_297_, v_a_295_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___boxed(lean_object* v_f_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg(v_f_300_, v_a_301_, v_a_302_);
lean_dec(v_a_302_);
lean_dec(v_a_301_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct(lean_object* v_f_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___f_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
lean_inc(v_a_306_);
v___f_318_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_318_, 0, v_a_306_);
lean_closure_set(v___f_318_, 1, v_f_305_);
v___x_319_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_320_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_319_, v___f_318_, v_a_307_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___boxed(lean_object* v_f_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct(v_f_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_a_323_);
lean_dec(v_a_322_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_335_, lean_object* v_vals_336_, lean_object* v_i_337_, lean_object* v_k_338_){
_start:
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = lean_array_get_size(v_keys_335_);
v___x_340_ = lean_nat_dec_lt(v_i_337_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_dec(v_i_337_);
v___x_341_ = lean_box(0);
return v___x_341_;
}
else
{
lean_object* v_k_x27_342_; size_t v___x_343_; size_t v___x_344_; uint8_t v___x_345_; 
v_k_x27_342_ = lean_array_fget_borrowed(v_keys_335_, v_i_337_);
v___x_343_ = lean_ptr_addr(v_k_338_);
v___x_344_ = lean_ptr_addr(v_k_x27_342_);
v___x_345_ = lean_usize_dec_eq(v___x_343_, v___x_344_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_nat_add(v_i_337_, v___x_346_);
lean_dec(v_i_337_);
v_i_337_ = v___x_347_;
goto _start;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_array_fget_borrowed(v_vals_336_, v_i_337_);
lean_dec(v_i_337_);
lean_inc(v___x_349_);
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_351_, lean_object* v_vals_352_, lean_object* v_i_353_, lean_object* v_k_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_351_, v_vals_352_, v_i_353_, v_k_354_);
lean_dec_ref(v_k_354_);
lean_dec_ref(v_vals_352_);
lean_dec_ref(v_keys_351_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_356_, size_t v_x_357_, lean_object* v_x_358_){
_start:
{
if (lean_obj_tag(v_x_356_) == 0)
{
lean_object* v_es_359_; lean_object* v___x_360_; size_t v___x_361_; size_t v___x_362_; lean_object* v_j_363_; lean_object* v___x_364_; 
v_es_359_ = lean_ctor_get(v_x_356_, 0);
v___x_360_ = lean_box(2);
v___x_361_ = ((size_t)31ULL);
v___x_362_ = lean_usize_land(v_x_357_, v___x_361_);
v_j_363_ = lean_usize_to_nat(v___x_362_);
v___x_364_ = lean_array_get_borrowed(v___x_360_, v_es_359_, v_j_363_);
lean_dec(v_j_363_);
switch(lean_obj_tag(v___x_364_))
{
case 0:
{
lean_object* v_key_365_; lean_object* v_val_366_; size_t v___x_367_; size_t v___x_368_; uint8_t v___x_369_; 
v_key_365_ = lean_ctor_get(v___x_364_, 0);
v_val_366_ = lean_ctor_get(v___x_364_, 1);
v___x_367_ = lean_ptr_addr(v_x_358_);
v___x_368_ = lean_ptr_addr(v_key_365_);
v___x_369_ = lean_usize_dec_eq(v___x_367_, v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
v___x_370_ = lean_box(0);
return v___x_370_;
}
else
{
lean_object* v___x_371_; 
lean_inc(v_val_366_);
v___x_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_371_, 0, v_val_366_);
return v___x_371_;
}
}
case 1:
{
lean_object* v_node_372_; size_t v___x_373_; size_t v___x_374_; 
v_node_372_ = lean_ctor_get(v___x_364_, 0);
v___x_373_ = ((size_t)5ULL);
v___x_374_ = lean_usize_shift_right(v_x_357_, v___x_373_);
v_x_356_ = v_node_372_;
v_x_357_ = v___x_374_;
goto _start;
}
default: 
{
lean_object* v___x_376_; 
v___x_376_ = lean_box(0);
return v___x_376_;
}
}
}
else
{
lean_object* v_ks_377_; lean_object* v_vs_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_ks_377_ = lean_ctor_get(v_x_356_, 0);
v_vs_378_ = lean_ctor_get(v_x_356_, 1);
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_377_, v_vs_378_, v___x_379_, v_x_358_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v_x_383_){
_start:
{
size_t v_x_890__boxed_384_; lean_object* v_res_385_; 
v_x_890__boxed_384_ = lean_unbox_usize(v_x_382_);
lean_dec(v_x_382_);
v_res_385_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_381_, v_x_890__boxed_384_, v_x_383_);
lean_dec_ref(v_x_383_);
lean_dec_ref(v_x_381_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
size_t v___x_388_; size_t v___x_389_; size_t v___x_390_; uint64_t v___x_391_; size_t v___x_392_; lean_object* v___x_393_; 
v___x_388_ = lean_ptr_addr(v_x_387_);
v___x_389_ = ((size_t)3ULL);
v___x_390_ = lean_usize_shift_right(v___x_388_, v___x_389_);
v___x_391_ = lean_usize_to_uint64(v___x_390_);
v___x_392_ = lean_uint64_to_usize(v___x_391_);
v___x_393_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_386_, v___x_392_, v_x_387_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_394_, lean_object* v_x_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_x_394_, v_x_395_);
lean_dec_ref(v_x_395_);
lean_dec_ref(v_x_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(lean_object* v_e_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_411_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_411_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_411_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_411_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v_exprToNatStructId_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v_exprToNatStructId_406_ = lean_ctor_get(v_a_402_, 7);
lean_inc_ref(v_exprToNatStructId_406_);
lean_dec(v_a_402_);
v___x_407_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_exprToNatStructId_406_, v_e_397_);
lean_dec_ref(v_exprToNatStructId_406_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_407_);
v___x_409_ = v___x_404_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_a_412_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_401_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_401_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg___boxed(lean_object* v_e_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_e_420_, v_a_421_, v_a_422_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_e_420_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f(lean_object* v_e_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_e_425_, v_a_426_, v_a_434_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___boxed(lean_object* v_e_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f(v_e_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_e_438_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0(lean_object* v_00_u03b2_451_, lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_x_452_, v_x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_455_, lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0(v_00_u03b2_455_, v_x_456_, v_x_457_);
lean_dec_ref(v_x_457_);
lean_dec_ref(v_x_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_459_, lean_object* v_x_460_, size_t v_x_461_, lean_object* v_x_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_460_, v_x_461_, v_x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_464_, lean_object* v_x_465_, lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
size_t v_x_1011__boxed_468_; lean_object* v_res_469_; 
v_x_1011__boxed_468_ = lean_unbox_usize(v_x_466_);
lean_dec(v_x_466_);
v_res_469_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0(v_00_u03b2_464_, v_x_465_, v_x_1011__boxed_468_, v_x_467_);
lean_dec_ref(v_x_467_);
lean_dec_ref(v_x_465_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_470_, lean_object* v_keys_471_, lean_object* v_vals_472_, lean_object* v_heq_473_, lean_object* v_i_474_, lean_object* v_k_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_471_, v_vals_472_, v_i_474_, v_k_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_477_, lean_object* v_keys_478_, lean_object* v_vals_479_, lean_object* v_heq_480_, lean_object* v_i_481_, lean_object* v_k_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_477_, v_keys_478_, v_vals_479_, v_heq_480_, v_i_481_, v_k_482_);
lean_dec_ref(v_k_482_);
lean_dec_ref(v_vals_479_);
lean_dec_ref(v_keys_478_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(lean_object* v_a_484_, lean_object* v_b_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_a_484_, v_a_486_, v_a_487_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_518_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_518_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_518_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_518_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
if (lean_obj_tag(v_a_490_) == 1)
{
lean_object* v_val_494_; lean_object* v___x_495_; 
lean_del_object(v___x_492_);
v_val_494_ = lean_ctor_get(v_a_490_, 0);
v___x_495_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_b_485_, v_a_486_, v_a_487_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_513_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_513_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_513_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_513_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
if (lean_obj_tag(v_a_496_) == 1)
{
lean_object* v_val_500_; uint8_t v___x_501_; 
v_val_500_ = lean_ctor_get(v_a_496_, 0);
lean_inc(v_val_500_);
lean_dec_ref_known(v_a_496_, 1);
v___x_501_ = lean_nat_dec_eq(v_val_494_, v_val_500_);
lean_dec(v_val_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_504_; 
lean_dec_ref_known(v_a_490_, 1);
v___x_502_ = lean_box(0);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_502_);
v___x_504_ = v___x_498_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
else
{
lean_object* v___x_507_; 
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v_a_490_);
v___x_507_ = v___x_498_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_490_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
else
{
lean_object* v___x_509_; lean_object* v___x_511_; 
lean_dec(v_a_496_);
lean_dec_ref_known(v_a_490_, 1);
v___x_509_ = lean_box(0);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_509_);
v___x_511_ = v___x_498_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_490_, 1);
return v___x_495_;
}
}
else
{
lean_object* v___x_514_; lean_object* v___x_516_; 
lean_dec(v_a_490_);
v___x_514_ = lean_box(0);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_514_);
v___x_516_ = v___x_492_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
else
{
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg___boxed(lean_object* v_a_519_, lean_object* v_b_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_519_, v_b_520_, v_a_521_, v_a_522_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec_ref(v_b_520_);
lean_dec_ref(v_a_519_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f(lean_object* v_a_525_, lean_object* v_b_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_525_, v_b_526_, v_a_527_, v_a_535_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___boxed(lean_object* v_a_539_, lean_object* v_b_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f(v_a_539_, v_b_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_b_540_);
lean_dec_ref(v_a_539_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
lean_object* v_ks_557_; lean_object* v_vs_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_584_; 
v_ks_557_ = lean_ctor_get(v_x_553_, 0);
v_vs_558_ = lean_ctor_get(v_x_553_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_x_553_);
if (v_isSharedCheck_584_ == 0)
{
v___x_560_ = v_x_553_;
v_isShared_561_ = v_isSharedCheck_584_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_vs_558_);
lean_inc(v_ks_557_);
lean_dec(v_x_553_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_584_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = lean_array_get_size(v_ks_557_);
v___x_563_ = lean_nat_dec_lt(v_x_554_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
lean_dec(v_x_554_);
v___x_564_ = lean_array_push(v_ks_557_, v_x_555_);
v___x_565_ = lean_array_push(v_vs_558_, v_x_556_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v___x_565_);
lean_ctor_set(v___x_560_, 0, v___x_564_);
v___x_567_ = v___x_560_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
else
{
lean_object* v_k_x27_569_; size_t v___x_570_; size_t v___x_571_; uint8_t v___x_572_; 
v_k_x27_569_ = lean_array_fget_borrowed(v_ks_557_, v_x_554_);
v___x_570_ = lean_ptr_addr(v_x_555_);
v___x_571_ = lean_ptr_addr(v_k_x27_569_);
v___x_572_ = lean_usize_dec_eq(v___x_570_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_574_; 
if (v_isShared_561_ == 0)
{
v___x_574_ = v___x_560_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_ks_557_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_vs_558_);
v___x_574_ = v_reuseFailAlloc_578_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = lean_nat_add(v_x_554_, v___x_575_);
lean_dec(v_x_554_);
v_x_553_ = v___x_574_;
v_x_554_ = v___x_576_;
goto _start;
}
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_579_ = lean_array_fset(v_ks_557_, v_x_554_, v_x_555_);
v___x_580_ = lean_array_fset(v_vs_558_, v_x_554_, v_x_556_);
lean_dec(v_x_554_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v___x_580_);
lean_ctor_set(v___x_560_, 0, v___x_579_);
v___x_582_ = v___x_560_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_585_, lean_object* v_k_586_, lean_object* v_v_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_585_, v___x_588_, v_k_586_, v_v_587_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(lean_object* v_x_591_, size_t v_x_592_, size_t v_x_593_, lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
if (lean_obj_tag(v_x_591_) == 0)
{
lean_object* v_es_596_; size_t v___x_597_; size_t v___x_598_; lean_object* v_j_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_es_596_ = lean_ctor_get(v_x_591_, 0);
v___x_597_ = ((size_t)31ULL);
v___x_598_ = lean_usize_land(v_x_592_, v___x_597_);
v_j_599_ = lean_usize_to_nat(v___x_598_);
v___x_600_ = lean_array_get_size(v_es_596_);
v___x_601_ = lean_nat_dec_lt(v_j_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_dec(v_j_599_);
lean_dec(v_x_595_);
lean_dec_ref(v_x_594_);
return v_x_591_;
}
else
{
lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_642_; 
lean_inc_ref(v_es_596_);
v_isSharedCheck_642_ = !lean_is_exclusive(v_x_591_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; 
v_unused_643_ = lean_ctor_get(v_x_591_, 0);
lean_dec(v_unused_643_);
v___x_603_ = v_x_591_;
v_isShared_604_ = v_isSharedCheck_642_;
goto v_resetjp_602_;
}
else
{
lean_dec(v_x_591_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_642_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v_v_605_; lean_object* v___x_606_; lean_object* v_xs_x27_607_; lean_object* v___y_609_; 
v_v_605_ = lean_array_fget(v_es_596_, v_j_599_);
v___x_606_ = lean_box(0);
v_xs_x27_607_ = lean_array_fset(v_es_596_, v_j_599_, v___x_606_);
switch(lean_obj_tag(v_v_605_))
{
case 0:
{
lean_object* v_key_614_; lean_object* v_val_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_627_; 
v_key_614_ = lean_ctor_get(v_v_605_, 0);
v_val_615_ = lean_ctor_get(v_v_605_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v_v_605_);
if (v_isSharedCheck_627_ == 0)
{
v___x_617_ = v_v_605_;
v_isShared_618_ = v_isSharedCheck_627_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_val_615_);
lean_inc(v_key_614_);
lean_dec(v_v_605_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_627_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
size_t v___x_619_; size_t v___x_620_; uint8_t v___x_621_; 
v___x_619_ = lean_ptr_addr(v_x_594_);
v___x_620_ = lean_ptr_addr(v_key_614_);
v___x_621_ = lean_usize_dec_eq(v___x_619_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; 
lean_del_object(v___x_617_);
v___x_622_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_614_, v_val_615_, v_x_594_, v_x_595_);
v___x_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
v___y_609_ = v___x_623_;
goto v___jp_608_;
}
else
{
lean_object* v___x_625_; 
lean_dec(v_val_615_);
lean_dec(v_key_614_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v_x_595_);
lean_ctor_set(v___x_617_, 0, v_x_594_);
v___x_625_ = v___x_617_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_x_594_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_x_595_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
v___y_609_ = v___x_625_;
goto v___jp_608_;
}
}
}
}
case 1:
{
lean_object* v_node_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_640_; 
v_node_628_ = lean_ctor_get(v_v_605_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v_v_605_);
if (v_isSharedCheck_640_ == 0)
{
v___x_630_ = v_v_605_;
v_isShared_631_ = v_isSharedCheck_640_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_node_628_);
lean_dec(v_v_605_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_640_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
size_t v___x_632_; size_t v___x_633_; size_t v___x_634_; size_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_632_ = ((size_t)5ULL);
v___x_633_ = lean_usize_shift_right(v_x_592_, v___x_632_);
v___x_634_ = ((size_t)1ULL);
v___x_635_ = lean_usize_add(v_x_593_, v___x_634_);
v___x_636_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_node_628_, v___x_633_, v___x_635_, v_x_594_, v_x_595_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_636_);
v___x_638_ = v___x_630_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
v___y_609_ = v___x_638_;
goto v___jp_608_;
}
}
}
default: 
{
lean_object* v___x_641_; 
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v_x_594_);
lean_ctor_set(v___x_641_, 1, v_x_595_);
v___y_609_ = v___x_641_;
goto v___jp_608_;
}
}
v___jp_608_:
{
lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_610_ = lean_array_fset(v_xs_x27_607_, v_j_599_, v___y_609_);
lean_dec(v_j_599_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_610_);
v___x_612_ = v___x_603_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
else
{
lean_object* v_ks_644_; lean_object* v_vs_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_665_; 
v_ks_644_ = lean_ctor_get(v_x_591_, 0);
v_vs_645_ = lean_ctor_get(v_x_591_, 1);
v_isSharedCheck_665_ = !lean_is_exclusive(v_x_591_);
if (v_isSharedCheck_665_ == 0)
{
v___x_647_ = v_x_591_;
v_isShared_648_ = v_isSharedCheck_665_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_vs_645_);
lean_inc(v_ks_644_);
lean_dec(v_x_591_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_665_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_ks_644_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_vs_645_);
v___x_650_ = v_reuseFailAlloc_664_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v_newNode_651_; uint8_t v___y_653_; size_t v___x_659_; uint8_t v___x_660_; 
v_newNode_651_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(v___x_650_, v_x_594_, v_x_595_);
v___x_659_ = ((size_t)7ULL);
v___x_660_ = lean_usize_dec_le(v___x_659_, v_x_593_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_661_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_651_);
v___x_662_ = lean_unsigned_to_nat(4u);
v___x_663_ = lean_nat_dec_lt(v___x_661_, v___x_662_);
lean_dec(v___x_661_);
v___y_653_ = v___x_663_;
goto v___jp_652_;
}
else
{
v___y_653_ = v___x_660_;
goto v___jp_652_;
}
v___jp_652_:
{
if (v___y_653_ == 0)
{
lean_object* v_ks_654_; lean_object* v_vs_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_ks_654_ = lean_ctor_get(v_newNode_651_, 0);
lean_inc_ref(v_ks_654_);
v_vs_655_ = lean_ctor_get(v_newNode_651_, 1);
lean_inc_ref(v_vs_655_);
lean_dec_ref(v_newNode_651_);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0);
v___x_658_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_x_593_, v_ks_654_, v_vs_655_, v___x_656_, v___x_657_);
lean_dec_ref(v_vs_655_);
lean_dec_ref(v_ks_654_);
return v___x_658_;
}
else
{
return v_newNode_651_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(size_t v_depth_666_, lean_object* v_keys_667_, lean_object* v_vals_668_, lean_object* v_i_669_, lean_object* v_entries_670_){
_start:
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = lean_array_get_size(v_keys_667_);
v___x_672_ = lean_nat_dec_lt(v_i_669_, v___x_671_);
if (v___x_672_ == 0)
{
lean_dec(v_i_669_);
return v_entries_670_;
}
else
{
lean_object* v_k_673_; lean_object* v_v_674_; size_t v___x_675_; size_t v___x_676_; size_t v___x_677_; uint64_t v___x_678_; size_t v_h_679_; size_t v___x_680_; lean_object* v___x_681_; size_t v___x_682_; size_t v___x_683_; size_t v___x_684_; size_t v_h_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_k_673_ = lean_array_fget_borrowed(v_keys_667_, v_i_669_);
v_v_674_ = lean_array_fget_borrowed(v_vals_668_, v_i_669_);
v___x_675_ = lean_ptr_addr(v_k_673_);
v___x_676_ = ((size_t)3ULL);
v___x_677_ = lean_usize_shift_right(v___x_675_, v___x_676_);
v___x_678_ = lean_usize_to_uint64(v___x_677_);
v_h_679_ = lean_uint64_to_usize(v___x_678_);
v___x_680_ = ((size_t)5ULL);
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = ((size_t)1ULL);
v___x_683_ = lean_usize_sub(v_depth_666_, v___x_682_);
v___x_684_ = lean_usize_mul(v___x_680_, v___x_683_);
v_h_685_ = lean_usize_shift_right(v_h_679_, v___x_684_);
v___x_686_ = lean_nat_add(v_i_669_, v___x_681_);
lean_dec(v_i_669_);
lean_inc(v_v_674_);
lean_inc(v_k_673_);
v___x_687_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_entries_670_, v_h_685_, v_depth_666_, v_k_673_, v_v_674_);
v_i_669_ = v___x_686_;
v_entries_670_ = v___x_687_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_689_, lean_object* v_keys_690_, lean_object* v_vals_691_, lean_object* v_i_692_, lean_object* v_entries_693_){
_start:
{
size_t v_depth_boxed_694_; lean_object* v_res_695_; 
v_depth_boxed_694_ = lean_unbox_usize(v_depth_689_);
lean_dec(v_depth_689_);
v_res_695_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_694_, v_keys_690_, v_vals_691_, v_i_692_, v_entries_693_);
lean_dec_ref(v_vals_691_);
lean_dec_ref(v_keys_690_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___boxed(lean_object* v_x_696_, lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v_x_699_, lean_object* v_x_700_){
_start:
{
size_t v_x_6947__boxed_701_; size_t v_x_6948__boxed_702_; lean_object* v_res_703_; 
v_x_6947__boxed_701_ = lean_unbox_usize(v_x_697_);
lean_dec(v_x_697_);
v_x_6948__boxed_702_ = lean_unbox_usize(v_x_698_);
lean_dec(v_x_698_);
v_res_703_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_696_, v_x_6947__boxed_701_, v_x_6948__boxed_702_, v_x_699_, v_x_700_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
size_t v___x_707_; size_t v___x_708_; size_t v___x_709_; uint64_t v___x_710_; size_t v___x_711_; size_t v___x_712_; lean_object* v___x_713_; 
v___x_707_ = lean_ptr_addr(v_x_705_);
v___x_708_ = ((size_t)3ULL);
v___x_709_ = lean_usize_shift_right(v___x_707_, v___x_708_);
v___x_710_ = lean_usize_to_uint64(v___x_709_);
v___x_711_ = lean_uint64_to_usize(v___x_710_);
v___x_712_ = ((size_t)1ULL);
v___x_713_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_704_, v___x_711_, v___x_712_, v_x_705_, v_x_706_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0(lean_object* v_e_714_, lean_object* v_a_715_, lean_object* v_s_716_){
_start:
{
lean_object* v_structs_717_; lean_object* v_typeIdOf_718_; lean_object* v_exprToStructId_719_; lean_object* v_exprToStructIdEntries_720_; lean_object* v_forbiddenNatModules_721_; lean_object* v_natStructs_722_; lean_object* v_natTypeIdOf_723_; lean_object* v_exprToNatStructId_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_732_; 
v_structs_717_ = lean_ctor_get(v_s_716_, 0);
v_typeIdOf_718_ = lean_ctor_get(v_s_716_, 1);
v_exprToStructId_719_ = lean_ctor_get(v_s_716_, 2);
v_exprToStructIdEntries_720_ = lean_ctor_get(v_s_716_, 3);
v_forbiddenNatModules_721_ = lean_ctor_get(v_s_716_, 4);
v_natStructs_722_ = lean_ctor_get(v_s_716_, 5);
v_natTypeIdOf_723_ = lean_ctor_get(v_s_716_, 6);
v_exprToNatStructId_724_ = lean_ctor_get(v_s_716_, 7);
v_isSharedCheck_732_ = !lean_is_exclusive(v_s_716_);
if (v_isSharedCheck_732_ == 0)
{
v___x_726_ = v_s_716_;
v_isShared_727_ = v_isSharedCheck_732_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_exprToNatStructId_724_);
lean_inc(v_natTypeIdOf_723_);
lean_inc(v_natStructs_722_);
lean_inc(v_forbiddenNatModules_721_);
lean_inc(v_exprToStructIdEntries_720_);
lean_inc(v_exprToStructId_719_);
lean_inc(v_typeIdOf_718_);
lean_inc(v_structs_717_);
lean_dec(v_s_716_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_732_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_730_; 
lean_inc(v_a_715_);
v___x_728_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_exprToNatStructId_724_, v_e_714_, v_a_715_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 7, v___x_728_);
v___x_730_ = v___x_726_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_structs_717_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_typeIdOf_718_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v_exprToStructId_719_);
lean_ctor_set(v_reuseFailAlloc_731_, 3, v_exprToStructIdEntries_720_);
lean_ctor_set(v_reuseFailAlloc_731_, 4, v_forbiddenNatModules_721_);
lean_ctor_set(v_reuseFailAlloc_731_, 5, v_natStructs_722_);
lean_ctor_set(v_reuseFailAlloc_731_, 6, v_natTypeIdOf_723_);
lean_ctor_set(v_reuseFailAlloc_731_, 7, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0___boxed(lean_object* v_e_733_, lean_object* v_a_734_, lean_object* v_s_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0(v_e_733_, v_a_734_, v_s_735_);
lean_dec(v_a_734_);
return v_res_736_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__0));
v___x_739_ = l_Lean_stringToMessageData(v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(lean_object* v_e_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_e_740_, v_a_742_, v_a_747_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 1);
if (lean_obj_tag(v_a_754_) == 1)
{
lean_object* v_val_755_; uint8_t v___x_756_; 
v_val_755_ = lean_ctor_get(v_a_754_, 0);
lean_inc(v_val_755_);
lean_dec_ref_known(v_a_754_, 1);
v___x_756_ = lean_nat_dec_eq(v_val_755_, v_a_741_);
lean_dec(v_val_755_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_743_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; uint8_t v_verbose_759_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
v_verbose_759_ = lean_ctor_get_uint8(v_a_758_, 0);
lean_dec(v_a_758_);
if (v_verbose_759_ == 0)
{
lean_dec_ref(v_e_740_);
goto v___jp_750_;
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_760_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1);
v___x_761_ = l_Lean_indentExpr(v_e_740_);
v___x_762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = l_Lean_Meta_Sym_reportIssue(v___x_762_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_dec_ref_known(v___x_763_, 1);
goto v___jp_750_;
}
else
{
return v___x_763_;
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec_ref(v_e_740_);
v_a_764_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_757_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_757_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
else
{
lean_dec_ref(v_e_740_);
goto v___jp_750_;
}
}
else
{
lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
lean_dec(v_a_754_);
lean_inc(v_a_741_);
v___f_772_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_772_, 0, v_e_740_);
lean_closure_set(v___f_772_, 1, v_a_741_);
v___x_773_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_774_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_773_, v___f_772_, v_a_742_);
return v___x_774_;
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec_ref(v_e_740_);
v_a_775_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_753_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_753_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
v___jp_750_:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_box(0);
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___boxed(lean_object* v_e_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(v_e_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec(v_a_784_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(lean_object* v_e_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(v_e_794_, v_a_795_, v_a_796_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___boxed(lean_object* v_e_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(v_e_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec(v_a_810_);
lean_dec(v_a_809_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0(lean_object* v_00_u03b2_822_, lean_object* v_x_823_, lean_object* v_x_824_, lean_object* v_x_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_x_823_, v_x_824_, v_x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(lean_object* v_00_u03b2_827_, lean_object* v_x_828_, size_t v_x_829_, size_t v_x_830_, lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_828_, v_x_829_, v_x_830_, v_x_831_, v_x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_834_, lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
size_t v_x_7237__boxed_840_; size_t v_x_7238__boxed_841_; lean_object* v_res_842_; 
v_x_7237__boxed_840_ = lean_unbox_usize(v_x_836_);
lean_dec(v_x_836_);
v_x_7238__boxed_841_ = lean_unbox_usize(v_x_837_);
lean_dec(v_x_837_);
v_res_842_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(v_00_u03b2_834_, v_x_835_, v_x_7237__boxed_840_, v_x_7238__boxed_841_, v_x_838_, v_x_839_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_843_, lean_object* v_n_844_, lean_object* v_k_845_, lean_object* v_v_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(v_n_844_, v_k_845_, v_v_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_848_, size_t v_depth_849_, lean_object* v_keys_850_, lean_object* v_vals_851_, lean_object* v_heq_852_, lean_object* v_i_853_, lean_object* v_entries_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_depth_849_, v_keys_850_, v_vals_851_, v_i_853_, v_entries_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_856_, lean_object* v_depth_857_, lean_object* v_keys_858_, lean_object* v_vals_859_, lean_object* v_heq_860_, lean_object* v_i_861_, lean_object* v_entries_862_){
_start:
{
size_t v_depth_boxed_863_; lean_object* v_res_864_; 
v_depth_boxed_863_ = lean_unbox_usize(v_depth_857_);
lean_dec(v_depth_857_);
v_res_864_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(v_00_u03b2_856_, v_depth_boxed_863_, v_keys_858_, v_vals_859_, v_heq_860_, v_i_861_, v_entries_862_);
lean_dec_ref(v_vals_859_);
lean_dec_ref(v_keys_858_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_866_, v_x_867_, v_x_868_, v_x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0(lean_object* v_a_871_, lean_object* v_e_872_, lean_object* v___x_873_, lean_object* v_s_874_){
_start:
{
lean_object* v_structs_875_; lean_object* v_typeIdOf_876_; lean_object* v_exprToStructId_877_; lean_object* v_exprToStructIdEntries_878_; lean_object* v_forbiddenNatModules_879_; lean_object* v_natStructs_880_; lean_object* v_natTypeIdOf_881_; lean_object* v_exprToNatStructId_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v_structs_875_ = lean_ctor_get(v_s_874_, 0);
v_typeIdOf_876_ = lean_ctor_get(v_s_874_, 1);
v_exprToStructId_877_ = lean_ctor_get(v_s_874_, 2);
v_exprToStructIdEntries_878_ = lean_ctor_get(v_s_874_, 3);
v_forbiddenNatModules_879_ = lean_ctor_get(v_s_874_, 4);
v_natStructs_880_ = lean_ctor_get(v_s_874_, 5);
v_natTypeIdOf_881_ = lean_ctor_get(v_s_874_, 6);
v_exprToNatStructId_882_ = lean_ctor_get(v_s_874_, 7);
v___x_883_ = lean_array_get_size(v_natStructs_880_);
v___x_884_ = lean_nat_dec_lt(v_a_871_, v___x_883_);
if (v___x_884_ == 0)
{
lean_dec_ref(v___x_873_);
lean_dec_ref(v_e_872_);
return v_s_874_;
}
else
{
lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_921_; 
lean_inc_ref(v_exprToNatStructId_882_);
lean_inc_ref(v_natTypeIdOf_881_);
lean_inc_ref(v_natStructs_880_);
lean_inc_ref(v_forbiddenNatModules_879_);
lean_inc_ref(v_exprToStructIdEntries_878_);
lean_inc_ref(v_exprToStructId_877_);
lean_inc_ref(v_typeIdOf_876_);
lean_inc_ref(v_structs_875_);
v_isSharedCheck_921_ = !lean_is_exclusive(v_s_874_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; lean_object* v_unused_923_; lean_object* v_unused_924_; lean_object* v_unused_925_; lean_object* v_unused_926_; lean_object* v_unused_927_; lean_object* v_unused_928_; lean_object* v_unused_929_; 
v_unused_922_ = lean_ctor_get(v_s_874_, 7);
lean_dec(v_unused_922_);
v_unused_923_ = lean_ctor_get(v_s_874_, 6);
lean_dec(v_unused_923_);
v_unused_924_ = lean_ctor_get(v_s_874_, 5);
lean_dec(v_unused_924_);
v_unused_925_ = lean_ctor_get(v_s_874_, 4);
lean_dec(v_unused_925_);
v_unused_926_ = lean_ctor_get(v_s_874_, 3);
lean_dec(v_unused_926_);
v_unused_927_ = lean_ctor_get(v_s_874_, 2);
lean_dec(v_unused_927_);
v_unused_928_ = lean_ctor_get(v_s_874_, 1);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_s_874_, 0);
lean_dec(v_unused_929_);
v___x_886_ = v_s_874_;
v_isShared_887_ = v_isSharedCheck_921_;
goto v_resetjp_885_;
}
else
{
lean_dec(v_s_874_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_921_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v_v_888_; lean_object* v_id_889_; lean_object* v_structId_890_; lean_object* v_type_891_; lean_object* v_u_892_; lean_object* v_natModuleInst_893_; lean_object* v_leInst_x3f_894_; lean_object* v_ltInst_x3f_895_; lean_object* v_lawfulOrderLTInst_x3f_896_; lean_object* v_isPreorderInst_x3f_897_; lean_object* v_orderedAddInst_x3f_898_; lean_object* v_isLinearInst_x3f_899_; lean_object* v_addRightCancelInst_x3f_900_; lean_object* v_rfl__q_901_; lean_object* v_zero_902_; lean_object* v_toQFn_903_; lean_object* v_addFn_904_; lean_object* v_smulFn_905_; lean_object* v_termMap_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_920_; 
v_v_888_ = lean_array_fget(v_natStructs_880_, v_a_871_);
v_id_889_ = lean_ctor_get(v_v_888_, 0);
v_structId_890_ = lean_ctor_get(v_v_888_, 1);
v_type_891_ = lean_ctor_get(v_v_888_, 2);
v_u_892_ = lean_ctor_get(v_v_888_, 3);
v_natModuleInst_893_ = lean_ctor_get(v_v_888_, 4);
v_leInst_x3f_894_ = lean_ctor_get(v_v_888_, 5);
v_ltInst_x3f_895_ = lean_ctor_get(v_v_888_, 6);
v_lawfulOrderLTInst_x3f_896_ = lean_ctor_get(v_v_888_, 7);
v_isPreorderInst_x3f_897_ = lean_ctor_get(v_v_888_, 8);
v_orderedAddInst_x3f_898_ = lean_ctor_get(v_v_888_, 9);
v_isLinearInst_x3f_899_ = lean_ctor_get(v_v_888_, 10);
v_addRightCancelInst_x3f_900_ = lean_ctor_get(v_v_888_, 11);
v_rfl__q_901_ = lean_ctor_get(v_v_888_, 12);
v_zero_902_ = lean_ctor_get(v_v_888_, 13);
v_toQFn_903_ = lean_ctor_get(v_v_888_, 14);
v_addFn_904_ = lean_ctor_get(v_v_888_, 15);
v_smulFn_905_ = lean_ctor_get(v_v_888_, 16);
v_termMap_906_ = lean_ctor_get(v_v_888_, 17);
v_isSharedCheck_920_ = !lean_is_exclusive(v_v_888_);
if (v_isSharedCheck_920_ == 0)
{
v___x_908_ = v_v_888_;
v_isShared_909_ = v_isSharedCheck_920_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_termMap_906_);
lean_inc(v_smulFn_905_);
lean_inc(v_addFn_904_);
lean_inc(v_toQFn_903_);
lean_inc(v_zero_902_);
lean_inc(v_rfl__q_901_);
lean_inc(v_addRightCancelInst_x3f_900_);
lean_inc(v_isLinearInst_x3f_899_);
lean_inc(v_orderedAddInst_x3f_898_);
lean_inc(v_isPreorderInst_x3f_897_);
lean_inc(v_lawfulOrderLTInst_x3f_896_);
lean_inc(v_ltInst_x3f_895_);
lean_inc(v_leInst_x3f_894_);
lean_inc(v_natModuleInst_893_);
lean_inc(v_u_892_);
lean_inc(v_type_891_);
lean_inc(v_structId_890_);
lean_inc(v_id_889_);
lean_dec(v_v_888_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_920_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v_xs_x27_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_910_ = lean_box(0);
v_xs_x27_911_ = lean_array_fset(v_natStructs_880_, v_a_871_, v___x_910_);
v___x_912_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_termMap_906_, v_e_872_, v___x_873_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 17, v___x_912_);
v___x_914_ = v___x_908_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_id_889_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_structId_890_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_type_891_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_u_892_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v_natModuleInst_893_);
lean_ctor_set(v_reuseFailAlloc_919_, 5, v_leInst_x3f_894_);
lean_ctor_set(v_reuseFailAlloc_919_, 6, v_ltInst_x3f_895_);
lean_ctor_set(v_reuseFailAlloc_919_, 7, v_lawfulOrderLTInst_x3f_896_);
lean_ctor_set(v_reuseFailAlloc_919_, 8, v_isPreorderInst_x3f_897_);
lean_ctor_set(v_reuseFailAlloc_919_, 9, v_orderedAddInst_x3f_898_);
lean_ctor_set(v_reuseFailAlloc_919_, 10, v_isLinearInst_x3f_899_);
lean_ctor_set(v_reuseFailAlloc_919_, 11, v_addRightCancelInst_x3f_900_);
lean_ctor_set(v_reuseFailAlloc_919_, 12, v_rfl__q_901_);
lean_ctor_set(v_reuseFailAlloc_919_, 13, v_zero_902_);
lean_ctor_set(v_reuseFailAlloc_919_, 14, v_toQFn_903_);
lean_ctor_set(v_reuseFailAlloc_919_, 15, v_addFn_904_);
lean_ctor_set(v_reuseFailAlloc_919_, 16, v_smulFn_905_);
lean_ctor_set(v_reuseFailAlloc_919_, 17, v___x_912_);
v___x_914_ = v_reuseFailAlloc_919_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_915_ = lean_array_fset(v_xs_x27_911_, v_a_871_, v___x_914_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 5, v___x_915_);
v___x_917_ = v___x_886_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_structs_875_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_typeIdOf_876_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_exprToStructId_877_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v_exprToStructIdEntries_878_);
lean_ctor_set(v_reuseFailAlloc_918_, 4, v_forbiddenNatModules_879_);
lean_ctor_set(v_reuseFailAlloc_918_, 5, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_918_, 6, v_natTypeIdOf_881_);
lean_ctor_set(v_reuseFailAlloc_918_, 7, v_exprToNatStructId_882_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0___boxed(lean_object* v_a_930_, lean_object* v_e_931_, lean_object* v___x_932_, lean_object* v_s_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0(v_a_930_, v_e_931_, v___x_932_, v_s_933_);
lean_dec(v_a_930_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(lean_object* v_e_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_1021_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_1021_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_1021_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v_termMap_953_; lean_object* v___x_954_; 
v_termMap_953_ = lean_ctor_get(v_a_949_, 17);
lean_inc_ref(v_termMap_953_);
lean_dec(v_a_949_);
v___x_954_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_termMap_953_, v_e_935_);
lean_dec_ref(v_termMap_953_);
if (lean_obj_tag(v___x_954_) == 1)
{
lean_object* v_val_955_; lean_object* v___x_957_; 
lean_dec_ref(v_e_935_);
v_val_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_val_955_);
lean_dec_ref_known(v___x_954_, 1);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v_val_955_);
v___x_957_ = v___x_951_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_val_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
else
{
lean_object* v___x_959_; 
lean_dec(v___x_954_);
lean_del_object(v___x_951_);
v___x_959_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v_rfl__q_961_; lean_object* v_toQFn_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 1);
v_rfl__q_961_ = lean_ctor_get(v_a_960_, 12);
lean_inc_ref(v_rfl__q_961_);
v_toQFn_962_ = lean_ctor_get(v_a_960_, 14);
lean_inc_ref(v_toQFn_962_);
lean_dec(v_a_960_);
lean_inc_ref(v_e_935_);
v___x_963_ = l_Lean_Expr_app___override(v_toQFn_962_, v_e_935_);
v___x_964_ = l_Lean_Meta_Sym_shareCommon(v___x_963_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___f_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc_n(v_a_965_, 2);
lean_dec_ref_known(v___x_964_, 1);
v___x_966_ = l_Lean_Expr_app___override(v_rfl__q_961_, v_a_965_);
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v_a_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
lean_inc_ref(v___x_967_);
lean_inc_ref(v_e_935_);
lean_inc(v_a_936_);
v___f_968_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0___boxed), 4, 3);
lean_closure_set(v___f_968_, 0, v_a_936_);
lean_closure_set(v___f_968_, 1, v_e_935_);
lean_closure_set(v___f_968_, 2, v___x_967_);
v___x_969_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_970_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_969_, v___f_968_, v_a_937_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v___x_971_; 
lean_dec_ref_known(v___x_970_, 1);
lean_inc_ref(v_e_935_);
v___x_971_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(v_e_935_, v_a_936_, v_a_937_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v___x_972_; 
lean_dec_ref_known(v___x_971_, 1);
v___x_972_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_969_, v_e_935_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; 
v_unused_980_ = lean_ctor_get(v___x_972_, 0);
lean_dec(v_unused_980_);
v___x_974_ = v___x_972_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_dec(v___x_972_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_967_);
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_967_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec_ref_known(v___x_967_, 2);
v_a_981_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_972_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_972_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec_ref_known(v___x_967_, 2);
lean_dec_ref(v_e_935_);
v_a_989_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_971_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_971_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec_ref_known(v___x_967_, 2);
lean_dec_ref(v_e_935_);
v_a_997_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_970_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_970_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_dec_ref(v_rfl__q_961_);
lean_dec_ref(v_e_935_);
v_a_1005_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_964_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_964_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec_ref(v_e_935_);
v_a_1013_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_959_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_959_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec_ref(v_e_935_);
v_a_1022_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_948_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_948_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___boxed(lean_object* v_e_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec(v_a_1031_);
return v_res_1043_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(lean_object* v_natStruct_1044_, lean_object* v_inst_1045_){
_start:
{
lean_object* v_addFn_1046_; lean_object* v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; uint8_t v___x_1050_; 
v_addFn_1046_ = lean_ctor_get(v_natStruct_1044_, 15);
v___x_1047_ = l_Lean_Expr_appArg_x21(v_addFn_1046_);
v___x_1048_ = lean_ptr_addr(v___x_1047_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = lean_ptr_addr(v_inst_1045_);
v___x_1050_ = lean_usize_dec_eq(v___x_1048_, v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst___boxed(lean_object* v_natStruct_1051_, lean_object* v_inst_1052_){
_start:
{
uint8_t v_res_1053_; lean_object* v_r_1054_; 
v_res_1053_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_natStruct_1051_, v_inst_1052_);
lean_dec_ref(v_inst_1052_);
lean_dec_ref(v_natStruct_1051_);
v_r_1054_ = lean_box(v_res_1053_);
return v_r_1054_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(lean_object* v_natStruct_1055_, lean_object* v_inst_1056_){
_start:
{
lean_object* v_zero_1057_; lean_object* v___x_1058_; size_t v___x_1059_; size_t v___x_1060_; uint8_t v___x_1061_; 
v_zero_1057_ = lean_ctor_get(v_natStruct_1055_, 13);
v___x_1058_ = l_Lean_Expr_appArg_x21(v_zero_1057_);
v___x_1059_ = lean_ptr_addr(v___x_1058_);
lean_dec_ref(v___x_1058_);
v___x_1060_ = lean_ptr_addr(v_inst_1056_);
v___x_1061_ = lean_usize_dec_eq(v___x_1059_, v___x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst___boxed(lean_object* v_natStruct_1062_, lean_object* v_inst_1063_){
_start:
{
uint8_t v_res_1064_; lean_object* v_r_1065_; 
v_res_1064_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_natStruct_1062_, v_inst_1063_);
lean_dec_ref(v_inst_1063_);
lean_dec_ref(v_natStruct_1062_);
v_r_1065_ = lean_box(v_res_1064_);
return v_r_1065_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(lean_object* v_natStruct_1066_, lean_object* v_inst_1067_){
_start:
{
lean_object* v_smulFn_1068_; lean_object* v___x_1069_; size_t v___x_1070_; size_t v___x_1071_; uint8_t v___x_1072_; 
v_smulFn_1068_ = lean_ctor_get(v_natStruct_1066_, 16);
v___x_1069_ = l_Lean_Expr_appArg_x21(v_smulFn_1068_);
v___x_1070_ = lean_ptr_addr(v___x_1069_);
lean_dec_ref(v___x_1069_);
v___x_1071_ = lean_ptr_addr(v_inst_1067_);
v___x_1072_ = lean_usize_dec_eq(v___x_1070_, v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst___boxed(lean_object* v_natStruct_1073_, lean_object* v_inst_1074_){
_start:
{
uint8_t v_res_1075_; lean_object* v_r_1076_; 
v_res_1075_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_natStruct_1073_, v_inst_1074_);
lean_dec_ref(v_inst_1074_);
lean_dec_ref(v_natStruct_1073_);
v_r_1076_ = lean_box(v_res_1075_);
return v_r_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(lean_object* v_e_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1137_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1135_, 1);
v___x_1137_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1139_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
lean_inc_ref(v_e_1122_);
v___x_1139_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1122_, v_a_1131_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1290_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1290_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1290_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1144_ = l_Lean_Expr_cleanupAnnotations(v_a_1140_);
v___x_1145_ = l_Lean_Expr_isApp(v___x_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; 
lean_dec_ref(v___x_1144_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1138_);
lean_dec(v_a_1136_);
v___x_1146_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1146_;
}
else
{
lean_object* v_arg_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v_arg_1147_ = lean_ctor_get(v___x_1144_, 1);
lean_inc_ref(v_arg_1147_);
v___x_1148_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1144_);
v___x_1149_ = l_Lean_Expr_isApp(v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
lean_dec_ref(v___x_1148_);
lean_dec_ref(v_arg_1147_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1138_);
lean_dec(v_a_1136_);
v___x_1150_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1150_;
}
else
{
lean_object* v_arg_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v_arg_1151_ = lean_ctor_get(v___x_1148_, 1);
lean_inc_ref(v_arg_1151_);
v___x_1152_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1148_);
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2));
v___x_1154_ = l_Lean_Expr_isConstOf(v___x_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
uint8_t v___x_1155_; 
lean_del_object(v___x_1142_);
v___x_1155_ = l_Lean_Expr_isApp(v___x_1152_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
lean_dec_ref(v___x_1152_);
lean_dec_ref(v_arg_1151_);
lean_dec_ref(v_arg_1147_);
lean_dec(v_a_1138_);
lean_dec(v_a_1136_);
v___x_1156_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1156_;
}
else
{
lean_object* v_arg_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_arg_1157_ = lean_ctor_get(v___x_1152_, 1);
lean_inc_ref(v_arg_1157_);
v___x_1158_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1152_);
v___x_1159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5));
v___x_1160_ = l_Lean_Expr_isConstOf(v___x_1158_, v___x_1159_);
if (v___x_1160_ == 0)
{
uint8_t v___x_1161_; 
v___x_1161_ = l_Lean_Expr_isApp(v___x_1158_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; 
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_arg_1157_);
lean_dec_ref(v_arg_1151_);
lean_dec_ref(v_arg_1147_);
lean_dec(v_a_1138_);
lean_dec(v_a_1136_);
v___x_1162_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1162_;
}
else
{
lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1158_);
v___x_1164_ = l_Lean_Expr_isApp(v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; 
lean_dec_ref(v___x_1163_);
lean_dec_ref(v_arg_1157_);
lean_dec_ref(v_arg_1151_);
lean_dec_ref(v_arg_1147_);
lean_dec(v_a_1138_);
lean_dec(v_a_1136_);
v___x_1165_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1165_;
}
else
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1163_);
v___x_1167_ = l_Lean_Expr_isApp(v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; 
lean_dec_ref(v___x_1166_);
lean_dec_ref(v_arg_1157_);
lean_dec_ref(v_arg_1151_);
lean_dec_ref(v_arg_1147_);
lean_dec(v_a_1138_);
lean_dec(v_a_1136_);
v___x_1168_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1168_;
}
else
{
lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1169_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1166_);
v___x_1170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8));
v___x_1171_ = l_Lean_Expr_isConstOf(v___x_1169_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11));
v___x_1173_ = l_Lean_Expr_isConstOf(v___x_1169_, v___x_1172_);
lean_dec_ref(v___x_1169_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; 
lean_dec_ref(v_arg_1157_);
lean_dec_ref(v_arg_1151_);
lean_dec_ref(v_arg_1147_);
lean_dec(v_a_1138_);
lean_dec(v_a_1136_);
v___x_1174_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1174_;
}
else
{
uint8_t v___x_1175_; 
v___x_1175_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_1138_, v_arg_1157_);
lean_dec_ref(v_arg_1157_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; 
lean_dec_ref(v_arg_1151_);
lean_dec_ref(v_arg_1147_);
lean_dec(v_a_1138_);
lean_dec(v_a_1136_);
v___x_1176_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; 
lean_dec_ref(v_e_1122_);
lean_inc_ref(v_arg_1151_);
v___x_1177_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_1151_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v_fst_1179_; lean_object* v_snd_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1214_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1177_, 1);
v_fst_1179_ = lean_ctor_get(v_a_1178_, 0);
v_snd_1180_ = lean_ctor_get(v_a_1178_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_a_1178_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1182_ = v_a_1178_;
v_isShared_1183_ = v_isSharedCheck_1214_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_snd_1180_);
lean_inc(v_fst_1179_);
lean_dec(v_a_1178_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1214_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; 
lean_inc_ref(v_arg_1147_);
v___x_1184_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_1147_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1213_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1213_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1213_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v_fst_1189_; lean_object* v_snd_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1212_; 
v_fst_1189_ = lean_ctor_get(v_a_1185_, 0);
v_snd_1190_ = lean_ctor_get(v_a_1185_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_a_1185_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1192_ = v_a_1185_;
v_isShared_1193_ = v_isSharedCheck_1212_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_snd_1190_);
lean_inc(v_fst_1189_);
lean_dec(v_a_1185_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1212_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_addFn_1194_; lean_object* v_type_1195_; lean_object* v_u_1196_; lean_object* v_natModuleInst_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v_addFn_1194_ = lean_ctor_get(v_a_1136_, 22);
lean_inc_ref(v_addFn_1194_);
lean_dec(v_a_1136_);
v_type_1195_ = lean_ctor_get(v_a_1138_, 2);
lean_inc_ref(v_type_1195_);
v_u_1196_ = lean_ctor_get(v_a_1138_, 3);
lean_inc(v_u_1196_);
v_natModuleInst_1197_ = lean_ctor_get(v_a_1138_, 4);
lean_inc_ref(v_natModuleInst_1197_);
lean_dec(v_a_1138_);
lean_inc(v_fst_1189_);
lean_inc(v_fst_1179_);
v___x_1198_ = l_Lean_mkAppB(v_addFn_1194_, v_fst_1179_, v_fst_1189_);
v___x_1199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17));
v___x_1200_ = lean_box(0);
if (v_isShared_1183_ == 0)
{
lean_ctor_set_tag(v___x_1182_, 1);
lean_ctor_set(v___x_1182_, 1, v___x_1200_);
lean_ctor_set(v___x_1182_, 0, v_u_1196_);
v___x_1202_ = v___x_1182_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_u_1196_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1203_ = l_Lean_mkConst(v___x_1199_, v___x_1202_);
v___x_1204_ = l_Lean_mkApp8(v___x_1203_, v_type_1195_, v_natModuleInst_1197_, v_arg_1151_, v_arg_1147_, v_fst_1179_, v_fst_1189_, v_snd_1180_, v_snd_1190_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v___x_1204_);
lean_ctor_set(v___x_1192_, 0, v___x_1198_);
v___x_1206_ = v___x_1192_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1208_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1206_);
v___x_1208_ = v___x_1187_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1182_);
lean_dec(v_snd_1180_);
lean_dec(v_fst_1179_);
lean_dec_ref(v_arg_1151_);
lean_dec_ref(v_arg_1147_);
lean_dec(v_a_1138_);
lean_dec(v_a_1136_);
return v___x_1184_;
}
}
}
else
{
lean_dec_ref(v_arg_1151_);
lean_dec_ref(v_arg_1147_);
lean_dec(v_a_1138_);
lean_dec(v_a_1136_);
return v___x_1177_;
}
}
}
}
else
{
uint8_t v___x_1215_; 
lean_dec_ref(v___x_1169_);
v___x_1215_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_a_1138_, v_arg_1157_);
lean_dec_ref(v_arg_1157_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
lean_dec_ref(v_arg_1151_);
lean_dec_ref(v_arg_1147_);
lean_dec(v_a_1138_);
lean_dec(v_a_1136_);
v___x_1216_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1216_;
}
else
{
lean_object* v___x_1217_; 
lean_dec_ref(v_e_1122_);
lean_inc_ref(v_arg_1147_);
v___x_1217_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_1147_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1244_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1244_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1244_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_fst_1222_; lean_object* v_snd_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1243_; 
v_fst_1222_ = lean_ctor_get(v_a_1218_, 0);
v_snd_1223_ = lean_ctor_get(v_a_1218_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_a_1218_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1225_ = v_a_1218_;
v_isShared_1226_ = v_isSharedCheck_1243_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_snd_1223_);
lean_inc(v_fst_1222_);
lean_dec(v_a_1218_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1243_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v_nsmulFn_1227_; lean_object* v_type_1228_; lean_object* v_u_1229_; lean_object* v_natModuleInst_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
v_nsmulFn_1227_ = lean_ctor_get(v_a_1136_, 24);
lean_inc_ref(v_nsmulFn_1227_);
lean_dec(v_a_1136_);
v_type_1228_ = lean_ctor_get(v_a_1138_, 2);
lean_inc_ref(v_type_1228_);
v_u_1229_ = lean_ctor_get(v_a_1138_, 3);
lean_inc(v_u_1229_);
v_natModuleInst_1230_ = lean_ctor_get(v_a_1138_, 4);
lean_inc_ref(v_natModuleInst_1230_);
lean_dec(v_a_1138_);
lean_inc(v_fst_1222_);
lean_inc_ref(v_arg_1151_);
v___x_1231_ = l_Lean_mkAppB(v_nsmulFn_1227_, v_arg_1151_, v_fst_1222_);
v___x_1232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19));
v___x_1233_ = lean_box(0);
v___x_1234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1234_, 0, v_u_1229_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = l_Lean_mkConst(v___x_1232_, v___x_1234_);
v___x_1236_ = l_Lean_mkApp6(v___x_1235_, v_type_1228_, v_natModuleInst_1230_, v_arg_1151_, v_arg_1147_, v_fst_1222_, v_snd_1223_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 1, v___x_1236_);
lean_ctor_set(v___x_1225_, 0, v___x_1231_);
v___x_1238_ = v___x_1225_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1240_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1238_);
v___x_1240_ = v___x_1220_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_1151_);
lean_dec_ref(v_arg_1147_);
lean_dec(v_a_1138_);
lean_dec(v_a_1136_);
return v___x_1217_;
}
}
}
}
}
}
}
else
{
lean_object* v_type_1245_; lean_object* v_u_1246_; lean_object* v_natModuleInst_1247_; lean_object* v_zero_1248_; lean_object* v___x_1249_; 
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_arg_1157_);
lean_dec_ref(v_arg_1151_);
lean_dec_ref(v_arg_1147_);
v_type_1245_ = lean_ctor_get(v_a_1138_, 2);
lean_inc_ref(v_type_1245_);
v_u_1246_ = lean_ctor_get(v_a_1138_, 3);
lean_inc(v_u_1246_);
v_natModuleInst_1247_ = lean_ctor_get(v_a_1138_, 4);
lean_inc_ref(v_natModuleInst_1247_);
v_zero_1248_ = lean_ctor_get(v_a_1138_, 13);
lean_inc_ref(v_zero_1248_);
lean_dec(v_a_1138_);
lean_inc_ref(v_e_1122_);
v___x_1249_ = l_Lean_Meta_isDefEqD(v_e_1122_, v_zero_1248_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1266_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1266_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1266_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_unbox(v_a_1250_);
lean_dec(v_a_1250_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; 
lean_del_object(v___x_1252_);
lean_dec_ref(v_natModuleInst_1247_);
lean_dec(v_u_1246_);
lean_dec_ref(v_type_1245_);
lean_dec(v_a_1136_);
v___x_1255_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1255_;
}
else
{
lean_object* v_zero_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
lean_dec_ref(v_e_1122_);
v_zero_1256_ = lean_ctor_get(v_a_1136_, 17);
lean_inc_ref(v_zero_1256_);
lean_dec(v_a_1136_);
v___x_1257_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21));
v___x_1258_ = lean_box(0);
v___x_1259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1259_, 0, v_u_1246_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = l_Lean_mkConst(v___x_1257_, v___x_1259_);
v___x_1261_ = l_Lean_mkAppB(v___x_1260_, v_type_1245_, v_natModuleInst_1247_);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v_zero_1256_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___x_1262_);
v___x_1264_ = v___x_1252_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref(v_natModuleInst_1247_);
lean_dec(v_u_1246_);
lean_dec_ref(v_type_1245_);
lean_dec(v_a_1136_);
lean_dec_ref(v_e_1122_);
v_a_1267_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1249_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1249_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
}
else
{
uint8_t v___x_1275_; 
lean_dec_ref(v___x_1152_);
lean_dec_ref(v_arg_1151_);
v___x_1275_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_1138_, v_arg_1147_);
lean_dec_ref(v_arg_1147_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; 
lean_del_object(v___x_1142_);
lean_dec(v_a_1138_);
lean_dec(v_a_1136_);
v___x_1276_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1276_;
}
else
{
lean_object* v_zero_1277_; lean_object* v_type_1278_; lean_object* v_u_1279_; lean_object* v_natModuleInst_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
lean_dec_ref(v_e_1122_);
v_zero_1277_ = lean_ctor_get(v_a_1136_, 17);
lean_inc_ref(v_zero_1277_);
lean_dec(v_a_1136_);
v_type_1278_ = lean_ctor_get(v_a_1138_, 2);
lean_inc_ref(v_type_1278_);
v_u_1279_ = lean_ctor_get(v_a_1138_, 3);
lean_inc(v_u_1279_);
v_natModuleInst_1280_ = lean_ctor_get(v_a_1138_, 4);
lean_inc_ref(v_natModuleInst_1280_);
lean_dec(v_a_1138_);
v___x_1281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21));
v___x_1282_ = lean_box(0);
v___x_1283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1283_, 0, v_u_1279_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = l_Lean_mkConst(v___x_1281_, v___x_1283_);
v___x_1285_ = l_Lean_mkAppB(v___x_1284_, v_type_1278_, v_natModuleInst_1280_);
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_zero_1277_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1286_);
v___x_1288_ = v___x_1142_;
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
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v_a_1138_);
lean_dec(v_a_1136_);
lean_dec_ref(v_e_1122_);
v_a_1291_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1139_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1139_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec(v_a_1136_);
lean_dec_ref(v_e_1122_);
v_a_1299_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1137_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1137_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec_ref(v_e_1122_);
v_a_1307_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1135_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1135_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___boxed(lean_object* v_e_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_e_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec(v_a_1316_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0(lean_object* v___y_1329_, lean_object* v_e_1330_, lean_object* v_____x_1331_, lean_object* v_s_1332_){
_start:
{
lean_object* v_structs_1333_; lean_object* v_typeIdOf_1334_; lean_object* v_exprToStructId_1335_; lean_object* v_exprToStructIdEntries_1336_; lean_object* v_forbiddenNatModules_1337_; lean_object* v_natStructs_1338_; lean_object* v_natTypeIdOf_1339_; lean_object* v_exprToNatStructId_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v_structs_1333_ = lean_ctor_get(v_s_1332_, 0);
v_typeIdOf_1334_ = lean_ctor_get(v_s_1332_, 1);
v_exprToStructId_1335_ = lean_ctor_get(v_s_1332_, 2);
v_exprToStructIdEntries_1336_ = lean_ctor_get(v_s_1332_, 3);
v_forbiddenNatModules_1337_ = lean_ctor_get(v_s_1332_, 4);
v_natStructs_1338_ = lean_ctor_get(v_s_1332_, 5);
v_natTypeIdOf_1339_ = lean_ctor_get(v_s_1332_, 6);
v_exprToNatStructId_1340_ = lean_ctor_get(v_s_1332_, 7);
v___x_1341_ = lean_array_get_size(v_natStructs_1338_);
v___x_1342_ = lean_nat_dec_lt(v___y_1329_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_dec_ref(v_____x_1331_);
lean_dec_ref(v_e_1330_);
return v_s_1332_;
}
else
{
lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1379_; 
lean_inc_ref(v_exprToNatStructId_1340_);
lean_inc_ref(v_natTypeIdOf_1339_);
lean_inc_ref(v_natStructs_1338_);
lean_inc_ref(v_forbiddenNatModules_1337_);
lean_inc_ref(v_exprToStructIdEntries_1336_);
lean_inc_ref(v_exprToStructId_1335_);
lean_inc_ref(v_typeIdOf_1334_);
lean_inc_ref(v_structs_1333_);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_s_1332_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; lean_object* v_unused_1381_; lean_object* v_unused_1382_; lean_object* v_unused_1383_; lean_object* v_unused_1384_; lean_object* v_unused_1385_; lean_object* v_unused_1386_; lean_object* v_unused_1387_; 
v_unused_1380_ = lean_ctor_get(v_s_1332_, 7);
lean_dec(v_unused_1380_);
v_unused_1381_ = lean_ctor_get(v_s_1332_, 6);
lean_dec(v_unused_1381_);
v_unused_1382_ = lean_ctor_get(v_s_1332_, 5);
lean_dec(v_unused_1382_);
v_unused_1383_ = lean_ctor_get(v_s_1332_, 4);
lean_dec(v_unused_1383_);
v_unused_1384_ = lean_ctor_get(v_s_1332_, 3);
lean_dec(v_unused_1384_);
v_unused_1385_ = lean_ctor_get(v_s_1332_, 2);
lean_dec(v_unused_1385_);
v_unused_1386_ = lean_ctor_get(v_s_1332_, 1);
lean_dec(v_unused_1386_);
v_unused_1387_ = lean_ctor_get(v_s_1332_, 0);
lean_dec(v_unused_1387_);
v___x_1344_ = v_s_1332_;
v_isShared_1345_ = v_isSharedCheck_1379_;
goto v_resetjp_1343_;
}
else
{
lean_dec(v_s_1332_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1379_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v_v_1346_; lean_object* v_id_1347_; lean_object* v_structId_1348_; lean_object* v_type_1349_; lean_object* v_u_1350_; lean_object* v_natModuleInst_1351_; lean_object* v_leInst_x3f_1352_; lean_object* v_ltInst_x3f_1353_; lean_object* v_lawfulOrderLTInst_x3f_1354_; lean_object* v_isPreorderInst_x3f_1355_; lean_object* v_orderedAddInst_x3f_1356_; lean_object* v_isLinearInst_x3f_1357_; lean_object* v_addRightCancelInst_x3f_1358_; lean_object* v_rfl__q_1359_; lean_object* v_zero_1360_; lean_object* v_toQFn_1361_; lean_object* v_addFn_1362_; lean_object* v_smulFn_1363_; lean_object* v_termMap_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1378_; 
v_v_1346_ = lean_array_fget(v_natStructs_1338_, v___y_1329_);
v_id_1347_ = lean_ctor_get(v_v_1346_, 0);
v_structId_1348_ = lean_ctor_get(v_v_1346_, 1);
v_type_1349_ = lean_ctor_get(v_v_1346_, 2);
v_u_1350_ = lean_ctor_get(v_v_1346_, 3);
v_natModuleInst_1351_ = lean_ctor_get(v_v_1346_, 4);
v_leInst_x3f_1352_ = lean_ctor_get(v_v_1346_, 5);
v_ltInst_x3f_1353_ = lean_ctor_get(v_v_1346_, 6);
v_lawfulOrderLTInst_x3f_1354_ = lean_ctor_get(v_v_1346_, 7);
v_isPreorderInst_x3f_1355_ = lean_ctor_get(v_v_1346_, 8);
v_orderedAddInst_x3f_1356_ = lean_ctor_get(v_v_1346_, 9);
v_isLinearInst_x3f_1357_ = lean_ctor_get(v_v_1346_, 10);
v_addRightCancelInst_x3f_1358_ = lean_ctor_get(v_v_1346_, 11);
v_rfl__q_1359_ = lean_ctor_get(v_v_1346_, 12);
v_zero_1360_ = lean_ctor_get(v_v_1346_, 13);
v_toQFn_1361_ = lean_ctor_get(v_v_1346_, 14);
v_addFn_1362_ = lean_ctor_get(v_v_1346_, 15);
v_smulFn_1363_ = lean_ctor_get(v_v_1346_, 16);
v_termMap_1364_ = lean_ctor_get(v_v_1346_, 17);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_v_1346_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1366_ = v_v_1346_;
v_isShared_1367_ = v_isSharedCheck_1378_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_termMap_1364_);
lean_inc(v_smulFn_1363_);
lean_inc(v_addFn_1362_);
lean_inc(v_toQFn_1361_);
lean_inc(v_zero_1360_);
lean_inc(v_rfl__q_1359_);
lean_inc(v_addRightCancelInst_x3f_1358_);
lean_inc(v_isLinearInst_x3f_1357_);
lean_inc(v_orderedAddInst_x3f_1356_);
lean_inc(v_isPreorderInst_x3f_1355_);
lean_inc(v_lawfulOrderLTInst_x3f_1354_);
lean_inc(v_ltInst_x3f_1353_);
lean_inc(v_leInst_x3f_1352_);
lean_inc(v_natModuleInst_1351_);
lean_inc(v_u_1350_);
lean_inc(v_type_1349_);
lean_inc(v_structId_1348_);
lean_inc(v_id_1347_);
lean_dec(v_v_1346_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1378_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v_xs_x27_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1368_ = lean_box(0);
v_xs_x27_1369_ = lean_array_fset(v_natStructs_1338_, v___y_1329_, v___x_1368_);
v___x_1370_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_termMap_1364_, v_e_1330_, v_____x_1331_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 17, v___x_1370_);
v___x_1372_ = v___x_1366_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_id_1347_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_structId_1348_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_type_1349_);
lean_ctor_set(v_reuseFailAlloc_1377_, 3, v_u_1350_);
lean_ctor_set(v_reuseFailAlloc_1377_, 4, v_natModuleInst_1351_);
lean_ctor_set(v_reuseFailAlloc_1377_, 5, v_leInst_x3f_1352_);
lean_ctor_set(v_reuseFailAlloc_1377_, 6, v_ltInst_x3f_1353_);
lean_ctor_set(v_reuseFailAlloc_1377_, 7, v_lawfulOrderLTInst_x3f_1354_);
lean_ctor_set(v_reuseFailAlloc_1377_, 8, v_isPreorderInst_x3f_1355_);
lean_ctor_set(v_reuseFailAlloc_1377_, 9, v_orderedAddInst_x3f_1356_);
lean_ctor_set(v_reuseFailAlloc_1377_, 10, v_isLinearInst_x3f_1357_);
lean_ctor_set(v_reuseFailAlloc_1377_, 11, v_addRightCancelInst_x3f_1358_);
lean_ctor_set(v_reuseFailAlloc_1377_, 12, v_rfl__q_1359_);
lean_ctor_set(v_reuseFailAlloc_1377_, 13, v_zero_1360_);
lean_ctor_set(v_reuseFailAlloc_1377_, 14, v_toQFn_1361_);
lean_ctor_set(v_reuseFailAlloc_1377_, 15, v_addFn_1362_);
lean_ctor_set(v_reuseFailAlloc_1377_, 16, v_smulFn_1363_);
lean_ctor_set(v_reuseFailAlloc_1377_, 17, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1373_ = lean_array_fset(v_xs_x27_1369_, v___y_1329_, v___x_1372_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 5, v___x_1373_);
v___x_1375_ = v___x_1344_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_structs_1333_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_typeIdOf_1334_);
lean_ctor_set(v_reuseFailAlloc_1376_, 2, v_exprToStructId_1335_);
lean_ctor_set(v_reuseFailAlloc_1376_, 3, v_exprToStructIdEntries_1336_);
lean_ctor_set(v_reuseFailAlloc_1376_, 4, v_forbiddenNatModules_1337_);
lean_ctor_set(v_reuseFailAlloc_1376_, 5, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1376_, 6, v_natTypeIdOf_1339_);
lean_ctor_set(v_reuseFailAlloc_1376_, 7, v_exprToNatStructId_1340_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0___boxed(lean_object* v___y_1388_, lean_object* v_e_1389_, lean_object* v_____x_1390_, lean_object* v_s_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0(v___y_1388_, v_e_1389_, v_____x_1390_, v_s_1391_);
lean_dec(v___y_1388_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule(lean_object* v_e_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_____x_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1493_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1447_ = v___x_1444_;
v_isShared_1448_ = v_isSharedCheck_1493_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1444_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1493_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v_termMap_1449_; lean_object* v___x_1450_; 
v_termMap_1449_ = lean_ctor_get(v_a_1445_, 17);
lean_inc_ref(v_termMap_1449_);
lean_dec(v_a_1445_);
v___x_1450_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_termMap_1449_, v_e_1393_);
lean_dec_ref(v_termMap_1449_);
if (lean_obj_tag(v___x_1450_) == 1)
{
lean_object* v_val_1451_; lean_object* v___x_1453_; 
lean_dec_ref(v_e_1393_);
v_val_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_val_1451_);
lean_dec_ref_known(v___x_1450_, 1);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v_val_1451_);
v___x_1453_ = v___x_1447_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_val_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
else
{
lean_object* v___x_1455_; 
lean_dec(v___x_1450_);
lean_del_object(v___x_1447_);
lean_inc_ref(v_e_1393_);
v___x_1455_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_e_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v_fst_1457_; lean_object* v_snd_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1492_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
v_fst_1457_ = lean_ctor_get(v_a_1456_, 0);
v_snd_1458_ = lean_ctor_get(v_a_1456_, 1);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_a_1456_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1460_ = v_a_1456_;
v_isShared_1461_ = v_isSharedCheck_1492_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_snd_1458_);
lean_inc(v_fst_1457_);
lean_dec(v_a_1456_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1492_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; 
lean_inc(v_a_1404_);
lean_inc_ref(v_a_1403_);
lean_inc(v_a_1402_);
lean_inc_ref(v_a_1401_);
lean_inc(v_a_1400_);
lean_inc_ref(v_a_1399_);
lean_inc(v_a_1398_);
lean_inc_ref(v_a_1397_);
lean_inc(v_a_1396_);
lean_inc(v_a_1395_);
v___x_1462_ = lean_grind_preprocess(v_fst_1457_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v_proof_x3f_1464_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
v_proof_x3f_1464_ = lean_ctor_get(v_a_1463_, 1);
if (lean_obj_tag(v_proof_x3f_1464_) == 1)
{
lean_object* v_expr_1465_; lean_object* v_val_1466_; lean_object* v___x_1467_; 
lean_inc_ref(v_proof_x3f_1464_);
v_expr_1465_ = lean_ctor_get(v_a_1463_, 0);
lean_inc_ref(v_expr_1465_);
lean_dec(v_a_1463_);
v_val_1466_ = lean_ctor_get(v_proof_x3f_1464_, 0);
lean_inc(v_val_1466_);
lean_dec_ref_known(v_proof_x3f_1464_, 1);
v___x_1467_ = l_Lean_Meta_mkEqTrans(v_snd_1458_, v_val_1466_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1470_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref_known(v___x_1467_, 1);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 1, v_a_1468_);
lean_ctor_set(v___x_1460_, 0, v_expr_1465_);
v___x_1470_ = v___x_1460_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_expr_1465_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_a_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
v_____x_1407_ = v___x_1470_;
v___y_1408_ = v_a_1394_;
v___y_1409_ = v_a_1395_;
v___y_1410_ = v_a_1399_;
v___y_1411_ = v_a_1400_;
v___y_1412_ = v_a_1401_;
v___y_1413_ = v_a_1402_;
v___y_1414_ = v_a_1403_;
v___y_1415_ = v_a_1404_;
goto v___jp_1406_;
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec_ref(v_expr_1465_);
lean_del_object(v___x_1460_);
lean_dec_ref(v_e_1393_);
v_a_1472_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1467_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1467_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_expr_1480_; lean_object* v___x_1482_; 
v_expr_1480_ = lean_ctor_get(v_a_1463_, 0);
lean_inc_ref(v_expr_1480_);
lean_dec(v_a_1463_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v_expr_1480_);
v___x_1482_ = v___x_1460_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_expr_1480_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_snd_1458_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
v_____x_1407_ = v___x_1482_;
v___y_1408_ = v_a_1394_;
v___y_1409_ = v_a_1395_;
v___y_1410_ = v_a_1399_;
v___y_1411_ = v_a_1400_;
v___y_1412_ = v_a_1401_;
v___y_1413_ = v_a_1402_;
v___y_1414_ = v_a_1403_;
v___y_1415_ = v_a_1404_;
goto v___jp_1406_;
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_del_object(v___x_1460_);
lean_dec(v_snd_1458_);
lean_dec_ref(v_e_1393_);
v_a_1484_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1462_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1462_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1393_);
return v___x_1455_;
}
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref(v_e_1393_);
v_a_1494_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1444_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1444_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
v___jp_1406_:
{
lean_object* v___x_1416_; 
lean_inc_ref(v_e_1393_);
v___x_1416_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(v_e_1393_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v___f_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_dec_ref_known(v___x_1416_, 1);
lean_inc_ref(v_____x_1407_);
lean_inc(v___y_1408_);
v___f_1417_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1417_, 0, v___y_1408_);
lean_closure_set(v___f_1417_, 1, v_e_1393_);
lean_closure_set(v___f_1417_, 2, v_____x_1407_);
v___x_1418_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1419_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1418_, v___f_1417_, v___y_1409_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; 
v_unused_1427_ = lean_ctor_get(v___x_1419_, 0);
lean_dec(v_unused_1427_);
v___x_1421_ = v___x_1419_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_dec(v___x_1419_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v_____x_1407_);
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_____x_1407_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec_ref(v_____x_1407_);
v_a_1428_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1419_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1419_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec_ref(v_____x_1407_);
lean_dec_ref(v_e_1393_);
v_a_1436_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1416_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1416_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___boxed(lean_object* v_e_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_e_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1512_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec(v_a_1504_);
lean_dec(v_a_1503_);
return v_res_1515_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = lean_box(0);
v___x_1517_ = lean_unsigned_to_nat(16u);
v___x_1518_ = lean_mk_array(v___x_1517_, v___x_1516_);
return v___x_1518_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0);
v___x_1520_ = lean_unsigned_to_nat(0u);
v___x_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
lean_ctor_set(v___x_1521_, 1, v___x_1519_);
return v___x_1521_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2));
v___x_1525_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1);
v___x_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___x_1524_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(lean_object* v_x_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
v___x_1541_ = lean_st_mk_ref(v___x_1540_);
lean_inc(v_a_1538_);
lean_inc_ref(v_a_1537_);
lean_inc(v_a_1536_);
lean_inc_ref(v_a_1535_);
lean_inc(v_a_1534_);
lean_inc_ref(v_a_1533_);
lean_inc(v_a_1532_);
lean_inc_ref(v_a_1531_);
lean_inc(v_a_1530_);
lean_inc(v_a_1529_);
lean_inc(v_a_1528_);
lean_inc(v___x_1541_);
v___x_1542_ = lean_apply_13(v_x_1527_, v___x_1541_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, lean_box(0));
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1551_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1551_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1551_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1547_ = lean_st_ref_get(v___x_1541_);
lean_dec(v___x_1541_);
lean_dec(v___x_1547_);
if (v_isShared_1546_ == 0)
{
v___x_1549_ = v___x_1545_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1543_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
else
{
lean_dec(v___x_1541_);
return v___x_1542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___boxed(lean_object* v_x_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(v_x_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec(v_a_1553_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(lean_object* v_00_u03b1_1566_, lean_object* v_x_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
v___x_1581_ = lean_st_mk_ref(v___x_1580_);
lean_inc(v_a_1578_);
lean_inc_ref(v_a_1577_);
lean_inc(v_a_1576_);
lean_inc_ref(v_a_1575_);
lean_inc(v_a_1574_);
lean_inc_ref(v_a_1573_);
lean_inc(v_a_1572_);
lean_inc_ref(v_a_1571_);
lean_inc(v_a_1570_);
lean_inc(v_a_1569_);
lean_inc(v_a_1568_);
lean_inc(v___x_1581_);
v___x_1582_ = lean_apply_13(v_x_1567_, v___x_1581_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, lean_box(0));
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1591_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1591_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1591_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; lean_object* v___x_1589_; 
v___x_1587_ = lean_st_ref_get(v___x_1581_);
lean_dec(v___x_1581_);
lean_dec(v___x_1587_);
if (v_isShared_1586_ == 0)
{
v___x_1589_ = v___x_1585_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1583_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
else
{
lean_dec(v___x_1581_);
return v___x_1582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___boxed(lean_object* v_00_u03b1_1592_, lean_object* v_x_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(v_00_u03b1_1592_, v_x_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_a_1596_);
lean_dec(v_a_1595_);
lean_dec(v_a_1594_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(lean_object* v_a_1607_, lean_object* v_b_1608_, lean_object* v_x_1609_){
_start:
{
if (lean_obj_tag(v_x_1609_) == 0)
{
lean_dec(v_b_1608_);
lean_dec_ref(v_a_1607_);
return v_x_1609_;
}
else
{
lean_object* v_key_1610_; lean_object* v_value_1611_; lean_object* v_tail_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1626_; 
v_key_1610_ = lean_ctor_get(v_x_1609_, 0);
v_value_1611_ = lean_ctor_get(v_x_1609_, 1);
v_tail_1612_ = lean_ctor_get(v_x_1609_, 2);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_x_1609_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1614_ = v_x_1609_;
v_isShared_1615_ = v_isSharedCheck_1626_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_tail_1612_);
lean_inc(v_value_1611_);
lean_inc(v_key_1610_);
lean_dec(v_x_1609_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1626_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
size_t v___x_1616_; size_t v___x_1617_; uint8_t v___x_1618_; 
v___x_1616_ = lean_ptr_addr(v_key_1610_);
v___x_1617_ = lean_ptr_addr(v_a_1607_);
v___x_1618_ = lean_usize_dec_eq(v___x_1616_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1619_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_1607_, v_b_1608_, v_tail_1612_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 2, v___x_1619_);
v___x_1621_ = v___x_1614_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_key_1610_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_value_1611_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
else
{
lean_object* v___x_1624_; 
lean_dec(v_value_1611_);
lean_dec(v_key_1610_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 1, v_b_1608_);
lean_ctor_set(v___x_1614_, 0, v_a_1607_);
v___x_1624_ = v___x_1614_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1607_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_b_1608_);
lean_ctor_set(v_reuseFailAlloc_1625_, 2, v_tail_1612_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1627_, lean_object* v_x_1628_){
_start:
{
if (lean_obj_tag(v_x_1628_) == 0)
{
return v_x_1627_;
}
else
{
lean_object* v_key_1629_; lean_object* v_value_1630_; lean_object* v_tail_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1657_; 
v_key_1629_ = lean_ctor_get(v_x_1628_, 0);
v_value_1630_ = lean_ctor_get(v_x_1628_, 1);
v_tail_1631_ = lean_ctor_get(v_x_1628_, 2);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_x_1628_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1633_ = v_x_1628_;
v_isShared_1634_ = v_isSharedCheck_1657_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_tail_1631_);
lean_inc(v_value_1630_);
lean_inc(v_key_1629_);
lean_dec(v_x_1628_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1657_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; size_t v___x_1636_; size_t v___x_1637_; size_t v___x_1638_; uint64_t v___x_1639_; uint64_t v___x_1640_; uint64_t v___x_1641_; uint64_t v_fold_1642_; uint64_t v___x_1643_; uint64_t v___x_1644_; uint64_t v___x_1645_; size_t v___x_1646_; size_t v___x_1647_; size_t v___x_1648_; size_t v___x_1649_; size_t v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1635_ = lean_array_get_size(v_x_1627_);
v___x_1636_ = lean_ptr_addr(v_key_1629_);
v___x_1637_ = ((size_t)3ULL);
v___x_1638_ = lean_usize_shift_right(v___x_1636_, v___x_1637_);
v___x_1639_ = lean_usize_to_uint64(v___x_1638_);
v___x_1640_ = 32ULL;
v___x_1641_ = lean_uint64_shift_right(v___x_1639_, v___x_1640_);
v_fold_1642_ = lean_uint64_xor(v___x_1639_, v___x_1641_);
v___x_1643_ = 16ULL;
v___x_1644_ = lean_uint64_shift_right(v_fold_1642_, v___x_1643_);
v___x_1645_ = lean_uint64_xor(v_fold_1642_, v___x_1644_);
v___x_1646_ = lean_uint64_to_usize(v___x_1645_);
v___x_1647_ = lean_usize_of_nat(v___x_1635_);
v___x_1648_ = ((size_t)1ULL);
v___x_1649_ = lean_usize_sub(v___x_1647_, v___x_1648_);
v___x_1650_ = lean_usize_land(v___x_1646_, v___x_1649_);
v___x_1651_ = lean_array_uget_borrowed(v_x_1627_, v___x_1650_);
lean_inc(v___x_1651_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 2, v___x_1651_);
v___x_1653_ = v___x_1633_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_key_1629_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_value_1630_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_array_uset(v_x_1627_, v___x_1650_, v___x_1653_);
v_x_1627_ = v___x_1654_;
v_x_1628_ = v_tail_1631_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1658_, lean_object* v_source_1659_, lean_object* v_target_1660_){
_start:
{
lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___x_1661_ = lean_array_get_size(v_source_1659_);
v___x_1662_ = lean_nat_dec_lt(v_i_1658_, v___x_1661_);
if (v___x_1662_ == 0)
{
lean_dec_ref(v_source_1659_);
lean_dec(v_i_1658_);
return v_target_1660_;
}
else
{
lean_object* v_es_1663_; lean_object* v___x_1664_; lean_object* v_source_1665_; lean_object* v_target_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_es_1663_ = lean_array_fget(v_source_1659_, v_i_1658_);
v___x_1664_ = lean_box(0);
v_source_1665_ = lean_array_fset(v_source_1659_, v_i_1658_, v___x_1664_);
v_target_1666_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1660_, v_es_1663_);
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = lean_nat_add(v_i_1658_, v___x_1667_);
lean_dec(v_i_1658_);
v_i_1658_ = v___x_1668_;
v_source_1659_ = v_source_1665_;
v_target_1660_ = v_target_1666_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(lean_object* v_data_1670_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v_nbuckets_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1671_ = lean_array_get_size(v_data_1670_);
v___x_1672_ = lean_unsigned_to_nat(2u);
v_nbuckets_1673_ = lean_nat_mul(v___x_1671_, v___x_1672_);
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = lean_box(0);
v___x_1676_ = lean_mk_array(v_nbuckets_1673_, v___x_1675_);
v___x_1677_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(v___x_1674_, v_data_1670_, v___x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(lean_object* v_a_1678_, lean_object* v_x_1679_){
_start:
{
if (lean_obj_tag(v_x_1679_) == 0)
{
uint8_t v___x_1680_; 
v___x_1680_ = 0;
return v___x_1680_;
}
else
{
lean_object* v_key_1681_; lean_object* v_tail_1682_; size_t v___x_1683_; size_t v___x_1684_; uint8_t v___x_1685_; 
v_key_1681_ = lean_ctor_get(v_x_1679_, 0);
v_tail_1682_ = lean_ctor_get(v_x_1679_, 2);
v___x_1683_ = lean_ptr_addr(v_key_1681_);
v___x_1684_ = lean_ptr_addr(v_a_1678_);
v___x_1685_ = lean_usize_dec_eq(v___x_1683_, v___x_1684_);
if (v___x_1685_ == 0)
{
v_x_1679_ = v_tail_1682_;
goto _start;
}
else
{
return v___x_1685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg___boxed(lean_object* v_a_1687_, lean_object* v_x_1688_){
_start:
{
uint8_t v_res_1689_; lean_object* v_r_1690_; 
v_res_1689_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_1687_, v_x_1688_);
lean_dec(v_x_1688_);
lean_dec_ref(v_a_1687_);
v_r_1690_ = lean_box(v_res_1689_);
return v_r_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(lean_object* v_m_1691_, lean_object* v_a_1692_, lean_object* v_b_1693_){
_start:
{
lean_object* v_size_1694_; lean_object* v_buckets_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1741_; 
v_size_1694_ = lean_ctor_get(v_m_1691_, 0);
v_buckets_1695_ = lean_ctor_get(v_m_1691_, 1);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_m_1691_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1697_ = v_m_1691_;
v_isShared_1698_ = v_isSharedCheck_1741_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_buckets_1695_);
lean_inc(v_size_1694_);
lean_dec(v_m_1691_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1741_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; size_t v___x_1700_; size_t v___x_1701_; size_t v___x_1702_; uint64_t v___x_1703_; uint64_t v___x_1704_; uint64_t v___x_1705_; uint64_t v_fold_1706_; uint64_t v___x_1707_; uint64_t v___x_1708_; uint64_t v___x_1709_; size_t v___x_1710_; size_t v___x_1711_; size_t v___x_1712_; size_t v___x_1713_; size_t v___x_1714_; lean_object* v_bkt_1715_; uint8_t v___x_1716_; 
v___x_1699_ = lean_array_get_size(v_buckets_1695_);
v___x_1700_ = lean_ptr_addr(v_a_1692_);
v___x_1701_ = ((size_t)3ULL);
v___x_1702_ = lean_usize_shift_right(v___x_1700_, v___x_1701_);
v___x_1703_ = lean_usize_to_uint64(v___x_1702_);
v___x_1704_ = 32ULL;
v___x_1705_ = lean_uint64_shift_right(v___x_1703_, v___x_1704_);
v_fold_1706_ = lean_uint64_xor(v___x_1703_, v___x_1705_);
v___x_1707_ = 16ULL;
v___x_1708_ = lean_uint64_shift_right(v_fold_1706_, v___x_1707_);
v___x_1709_ = lean_uint64_xor(v_fold_1706_, v___x_1708_);
v___x_1710_ = lean_uint64_to_usize(v___x_1709_);
v___x_1711_ = lean_usize_of_nat(v___x_1699_);
v___x_1712_ = ((size_t)1ULL);
v___x_1713_ = lean_usize_sub(v___x_1711_, v___x_1712_);
v___x_1714_ = lean_usize_land(v___x_1710_, v___x_1713_);
v_bkt_1715_ = lean_array_uget_borrowed(v_buckets_1695_, v___x_1714_);
v___x_1716_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_1692_, v_bkt_1715_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v_size_x27_1718_; lean_object* v___x_1719_; lean_object* v_buckets_x27_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1717_ = lean_unsigned_to_nat(1u);
v_size_x27_1718_ = lean_nat_add(v_size_1694_, v___x_1717_);
lean_dec(v_size_1694_);
lean_inc(v_bkt_1715_);
v___x_1719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1719_, 0, v_a_1692_);
lean_ctor_set(v___x_1719_, 1, v_b_1693_);
lean_ctor_set(v___x_1719_, 2, v_bkt_1715_);
v_buckets_x27_1720_ = lean_array_uset(v_buckets_1695_, v___x_1714_, v___x_1719_);
v___x_1721_ = lean_unsigned_to_nat(4u);
v___x_1722_ = lean_nat_mul(v_size_x27_1718_, v___x_1721_);
v___x_1723_ = lean_unsigned_to_nat(3u);
v___x_1724_ = lean_nat_div(v___x_1722_, v___x_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_array_get_size(v_buckets_x27_1720_);
v___x_1726_ = lean_nat_dec_le(v___x_1724_, v___x_1725_);
lean_dec(v___x_1724_);
if (v___x_1726_ == 0)
{
lean_object* v_val_1727_; lean_object* v___x_1729_; 
v_val_1727_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(v_buckets_x27_1720_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 1, v_val_1727_);
lean_ctor_set(v___x_1697_, 0, v_size_x27_1718_);
v___x_1729_ = v___x_1697_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_size_x27_1718_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_val_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
else
{
lean_object* v___x_1732_; 
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 1, v_buckets_x27_1720_);
lean_ctor_set(v___x_1697_, 0, v_size_x27_1718_);
v___x_1732_ = v___x_1697_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_size_x27_1718_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_buckets_x27_1720_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
else
{
lean_object* v___x_1734_; lean_object* v_buckets_x27_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
lean_inc(v_bkt_1715_);
v___x_1734_ = lean_box(0);
v_buckets_x27_1735_ = lean_array_uset(v_buckets_1695_, v___x_1714_, v___x_1734_);
v___x_1736_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_1692_, v_b_1693_, v_bkt_1715_);
v___x_1737_ = lean_array_uset(v_buckets_x27_1735_, v___x_1714_, v___x_1736_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 1, v___x_1737_);
v___x_1739_ = v___x_1697_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_size_1694_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(lean_object* v_a_1742_, lean_object* v_x_1743_){
_start:
{
if (lean_obj_tag(v_x_1743_) == 0)
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_box(0);
return v___x_1744_;
}
else
{
lean_object* v_key_1745_; lean_object* v_value_1746_; lean_object* v_tail_1747_; size_t v___x_1748_; size_t v___x_1749_; uint8_t v___x_1750_; 
v_key_1745_ = lean_ctor_get(v_x_1743_, 0);
v_value_1746_ = lean_ctor_get(v_x_1743_, 1);
v_tail_1747_ = lean_ctor_get(v_x_1743_, 2);
v___x_1748_ = lean_ptr_addr(v_key_1745_);
v___x_1749_ = lean_ptr_addr(v_a_1742_);
v___x_1750_ = lean_usize_dec_eq(v___x_1748_, v___x_1749_);
if (v___x_1750_ == 0)
{
v_x_1743_ = v_tail_1747_;
goto _start;
}
else
{
lean_object* v___x_1752_; 
lean_inc(v_value_1746_);
v___x_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_value_1746_);
return v___x_1752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_1753_, lean_object* v_x_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_1753_, v_x_1754_);
lean_dec(v_x_1754_);
lean_dec_ref(v_a_1753_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(lean_object* v_m_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v_buckets_1758_; lean_object* v___x_1759_; size_t v___x_1760_; size_t v___x_1761_; size_t v___x_1762_; uint64_t v___x_1763_; uint64_t v___x_1764_; uint64_t v___x_1765_; uint64_t v_fold_1766_; uint64_t v___x_1767_; uint64_t v___x_1768_; uint64_t v___x_1769_; size_t v___x_1770_; size_t v___x_1771_; size_t v___x_1772_; size_t v___x_1773_; size_t v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_buckets_1758_ = lean_ctor_get(v_m_1756_, 1);
v___x_1759_ = lean_array_get_size(v_buckets_1758_);
v___x_1760_ = lean_ptr_addr(v_a_1757_);
v___x_1761_ = ((size_t)3ULL);
v___x_1762_ = lean_usize_shift_right(v___x_1760_, v___x_1761_);
v___x_1763_ = lean_usize_to_uint64(v___x_1762_);
v___x_1764_ = 32ULL;
v___x_1765_ = lean_uint64_shift_right(v___x_1763_, v___x_1764_);
v_fold_1766_ = lean_uint64_xor(v___x_1763_, v___x_1765_);
v___x_1767_ = 16ULL;
v___x_1768_ = lean_uint64_shift_right(v_fold_1766_, v___x_1767_);
v___x_1769_ = lean_uint64_xor(v_fold_1766_, v___x_1768_);
v___x_1770_ = lean_uint64_to_usize(v___x_1769_);
v___x_1771_ = lean_usize_of_nat(v___x_1759_);
v___x_1772_ = ((size_t)1ULL);
v___x_1773_ = lean_usize_sub(v___x_1771_, v___x_1772_);
v___x_1774_ = lean_usize_land(v___x_1770_, v___x_1773_);
v___x_1775_ = lean_array_uget_borrowed(v_buckets_1758_, v___x_1774_);
v___x_1776_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_1757_, v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg___boxed(lean_object* v_m_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_m_1777_, v_a_1778_);
lean_dec_ref(v_a_1778_);
lean_dec_ref(v_m_1777_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(lean_object* v_e_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v___x_1783_; lean_object* v_varMap_1784_; lean_object* v___x_1785_; 
v___x_1783_ = lean_st_ref_get(v_a_1781_);
v_varMap_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc_ref(v_varMap_1784_);
lean_dec(v___x_1783_);
v___x_1785_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_varMap_1784_, v_e_1780_);
lean_dec_ref(v_varMap_1784_);
if (lean_obj_tag(v___x_1785_) == 1)
{
lean_object* v_val_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v_e_1780_);
v_val_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1794_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_val_1786_);
lean_dec(v___x_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1794_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_val_1786_);
v___x_1791_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
return v___x_1792_;
}
}
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v_vars_1797_; lean_object* v_varMap_1798_; lean_object* v_vars_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v___x_1785_);
v___x_1795_ = lean_st_ref_get(v_a_1781_);
v___x_1796_ = lean_st_ref_take(v_a_1781_);
v_vars_1797_ = lean_ctor_get(v___x_1795_, 1);
lean_inc_ref(v_vars_1797_);
lean_dec(v___x_1795_);
v_varMap_1798_ = lean_ctor_get(v___x_1796_, 0);
v_vars_1799_ = lean_ctor_get(v___x_1796_, 1);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1801_ = v___x_1796_;
v_isShared_1802_ = v_isSharedCheck_1812_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_vars_1799_);
lean_inc(v_varMap_1798_);
lean_dec(v___x_1796_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1812_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1803_ = lean_array_get_size(v_vars_1797_);
lean_dec_ref(v_vars_1797_);
lean_inc_ref(v_e_1780_);
v___x_1804_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(v_varMap_1798_, v_e_1780_, v___x_1803_);
v___x_1805_ = lean_array_push(v_vars_1799_, v_e_1780_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v___x_1805_);
lean_ctor_set(v___x_1801_, 0, v___x_1804_);
v___x_1807_ = v___x_1801_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = lean_st_ref_set(v_a_1781_, v___x_1807_);
v___x_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1803_);
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
return v___x_1810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg___boxed(lean_object* v_e_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1813_, v_a_1814_);
lean_dec(v_a_1814_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(lean_object* v_e_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1817_, v_a_1818_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___boxed(lean_object* v_e_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(v_e_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec(v_a_1833_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0(lean_object* v_00_u03b2_1847_, lean_object* v_m_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_m_1848_, v_a_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___boxed(lean_object* v_00_u03b2_1851_, lean_object* v_m_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0(v_00_u03b2_1851_, v_m_1852_, v_a_1853_);
lean_dec_ref(v_a_1853_);
lean_dec_ref(v_m_1852_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1(lean_object* v_00_u03b2_1855_, lean_object* v_m_1856_, lean_object* v_a_1857_, lean_object* v_b_1858_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(v_m_1856_, v_a_1857_, v_b_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0(lean_object* v_00_u03b2_1860_, lean_object* v_a_1861_, lean_object* v_x_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_1861_, v_x_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1864_, lean_object* v_a_1865_, lean_object* v_x_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0(v_00_u03b2_1864_, v_a_1865_, v_x_1866_);
lean_dec(v_x_1866_);
lean_dec_ref(v_a_1865_);
return v_res_1867_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(lean_object* v_00_u03b2_1868_, lean_object* v_a_1869_, lean_object* v_x_1870_){
_start:
{
uint8_t v___x_1871_; 
v___x_1871_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_1869_, v_x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1872_, lean_object* v_a_1873_, lean_object* v_x_1874_){
_start:
{
uint8_t v_res_1875_; lean_object* v_r_1876_; 
v_res_1875_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(v_00_u03b2_1872_, v_a_1873_, v_x_1874_);
lean_dec(v_x_1874_);
lean_dec_ref(v_a_1873_);
v_r_1876_ = lean_box(v_res_1875_);
return v_r_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3(lean_object* v_00_u03b2_1877_, lean_object* v_data_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(v_data_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4(lean_object* v_00_u03b2_1880_, lean_object* v_a_1881_, lean_object* v_b_1882_, lean_object* v_x_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_1881_, v_b_1882_, v_x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1885_, lean_object* v_i_1886_, lean_object* v_source_1887_, lean_object* v_target_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(v_i_1886_, v_source_1887_, v_target_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1891_, v_x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(lean_object* v_e_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1910_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___x_1908_, 1);
lean_inc_ref(v_e_1894_);
v___x_1910_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1894_, v_a_1904_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_2011_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_2011_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_2011_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1915_; uint8_t v___x_1916_; 
v___x_1915_ = l_Lean_Expr_cleanupAnnotations(v_a_1911_);
v___x_1916_ = l_Lean_Expr_isApp(v___x_1915_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; 
lean_dec_ref(v___x_1915_);
lean_del_object(v___x_1913_);
lean_dec(v_a_1909_);
v___x_1917_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1894_, v_a_1895_);
return v___x_1917_;
}
else
{
lean_object* v_arg_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; 
v_arg_1918_ = lean_ctor_get(v___x_1915_, 1);
lean_inc_ref(v_arg_1918_);
v___x_1919_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1915_);
v___x_1920_ = l_Lean_Expr_isApp(v___x_1919_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; 
lean_dec_ref(v___x_1919_);
lean_dec_ref(v_arg_1918_);
lean_del_object(v___x_1913_);
lean_dec(v_a_1909_);
v___x_1921_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1894_, v_a_1895_);
return v___x_1921_;
}
else
{
lean_object* v_arg_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v_arg_1922_ = lean_ctor_get(v___x_1919_, 1);
lean_inc_ref(v_arg_1922_);
v___x_1923_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1919_);
v___x_1924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2));
v___x_1925_ = l_Lean_Expr_isConstOf(v___x_1923_, v___x_1924_);
if (v___x_1925_ == 0)
{
uint8_t v___x_1926_; 
lean_del_object(v___x_1913_);
v___x_1926_ = l_Lean_Expr_isApp(v___x_1923_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; 
lean_dec_ref(v___x_1923_);
lean_dec_ref(v_arg_1922_);
lean_dec_ref(v_arg_1918_);
lean_dec(v_a_1909_);
v___x_1927_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1894_, v_a_1895_);
return v___x_1927_;
}
else
{
lean_object* v_arg_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
v_arg_1928_ = lean_ctor_get(v___x_1923_, 1);
lean_inc_ref(v_arg_1928_);
v___x_1929_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1923_);
v___x_1930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5));
v___x_1931_ = l_Lean_Expr_isConstOf(v___x_1929_, v___x_1930_);
if (v___x_1931_ == 0)
{
uint8_t v___x_1932_; 
v___x_1932_ = l_Lean_Expr_isApp(v___x_1929_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; 
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_arg_1928_);
lean_dec_ref(v_arg_1922_);
lean_dec_ref(v_arg_1918_);
lean_dec(v_a_1909_);
v___x_1933_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1894_, v_a_1895_);
return v___x_1933_;
}
else
{
lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1934_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1929_);
v___x_1935_ = l_Lean_Expr_isApp(v___x_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; 
lean_dec_ref(v___x_1934_);
lean_dec_ref(v_arg_1928_);
lean_dec_ref(v_arg_1922_);
lean_dec_ref(v_arg_1918_);
lean_dec(v_a_1909_);
v___x_1936_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1894_, v_a_1895_);
return v___x_1936_;
}
else
{
lean_object* v___x_1937_; uint8_t v___x_1938_; 
v___x_1937_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1934_);
v___x_1938_ = l_Lean_Expr_isApp(v___x_1937_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; 
lean_dec_ref(v___x_1937_);
lean_dec_ref(v_arg_1928_);
lean_dec_ref(v_arg_1922_);
lean_dec_ref(v_arg_1918_);
lean_dec(v_a_1909_);
v___x_1939_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1894_, v_a_1895_);
return v___x_1939_;
}
else
{
lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1940_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1937_);
v___x_1941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8));
v___x_1942_ = l_Lean_Expr_isConstOf(v___x_1940_, v___x_1941_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11));
v___x_1944_ = l_Lean_Expr_isConstOf(v___x_1940_, v___x_1943_);
lean_dec_ref(v___x_1940_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; 
lean_dec_ref(v_arg_1928_);
lean_dec_ref(v_arg_1922_);
lean_dec_ref(v_arg_1918_);
lean_dec(v_a_1909_);
v___x_1945_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1894_, v_a_1895_);
return v___x_1945_;
}
else
{
uint8_t v___x_1946_; 
v___x_1946_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_1909_, v_arg_1928_);
lean_dec_ref(v_arg_1928_);
lean_dec(v_a_1909_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; 
lean_dec_ref(v_arg_1922_);
lean_dec_ref(v_arg_1918_);
v___x_1947_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1894_, v_a_1895_);
return v___x_1947_;
}
else
{
lean_object* v___x_1948_; 
lean_dec_ref(v_e_1894_);
v___x_1948_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_1922_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1950_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___x_1948_, 1);
v___x_1950_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_1918_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1959_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_1959_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1959_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1955_, 0, v_a_1949_);
lean_ctor_set(v___x_1955_, 1, v_a_1951_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v___x_1955_);
v___x_1957_ = v___x_1953_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
else
{
lean_dec(v_a_1949_);
return v___x_1950_;
}
}
else
{
lean_dec_ref(v_arg_1918_);
return v___x_1948_;
}
}
}
}
else
{
uint8_t v___x_1960_; 
lean_dec_ref(v___x_1940_);
v___x_1960_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_a_1909_, v_arg_1928_);
lean_dec_ref(v_arg_1928_);
lean_dec(v_a_1909_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; 
lean_dec_ref(v_arg_1922_);
lean_dec_ref(v_arg_1918_);
v___x_1961_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1894_, v_a_1895_);
return v___x_1961_;
}
else
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_Meta_getNatValue_x3f(v_arg_1922_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
lean_dec_ref(v_arg_1922_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
if (lean_obj_tag(v_a_1963_) == 1)
{
lean_object* v_val_1964_; lean_object* v___x_1965_; 
lean_dec_ref(v_e_1894_);
v_val_1964_ = lean_ctor_get(v_a_1963_, 0);
lean_inc(v_val_1964_);
lean_dec_ref_known(v_a_1963_, 1);
v___x_1965_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_1918_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1974_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1970_, 0, v_val_1964_);
lean_ctor_set(v___x_1970_, 1, v_a_1966_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1970_);
v___x_1972_ = v___x_1968_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
else
{
lean_dec(v_val_1964_);
return v___x_1965_;
}
}
else
{
lean_object* v___x_1975_; 
lean_dec(v_a_1963_);
lean_dec_ref(v_arg_1918_);
v___x_1975_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1894_, v_a_1895_);
return v___x_1975_;
}
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
lean_dec_ref(v_arg_1918_);
lean_dec_ref(v_e_1894_);
v_a_1976_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1962_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1962_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
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
lean_object* v_zero_1984_; lean_object* v___x_1985_; 
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_arg_1928_);
lean_dec_ref(v_arg_1922_);
lean_dec_ref(v_arg_1918_);
v_zero_1984_ = lean_ctor_get(v_a_1909_, 13);
lean_inc_ref(v_zero_1984_);
lean_dec(v_a_1909_);
lean_inc_ref(v_e_1894_);
v___x_1985_ = l_Lean_Meta_isDefEqD(v_e_1894_, v_zero_1984_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1996_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_1996_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1996_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
uint8_t v___x_1990_; 
v___x_1990_ = lean_unbox(v_a_1986_);
lean_dec(v_a_1986_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; 
lean_del_object(v___x_1988_);
v___x_1991_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1894_, v_a_1895_);
return v___x_1991_;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1994_; 
lean_dec_ref(v_e_1894_);
v___x_1992_ = lean_box(0);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_1992_);
v___x_1994_ = v___x_1988_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1992_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec_ref(v_e_1894_);
v_a_1997_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1985_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1985_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
}
else
{
uint8_t v___x_2005_; 
lean_dec_ref(v___x_1923_);
lean_dec_ref(v_arg_1922_);
v___x_2005_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_1909_, v_arg_1918_);
lean_dec_ref(v_arg_1918_);
lean_dec(v_a_1909_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
lean_del_object(v___x_1913_);
v___x_2006_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1894_, v_a_1895_);
return v___x_2006_;
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
lean_dec_ref(v_e_1894_);
v___x_2007_ = lean_box(0);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v___x_2007_);
v___x_2009_ = v___x_1913_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec(v_a_1909_);
lean_dec_ref(v_e_1894_);
v_a_2012_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_1910_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_1910_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec_ref(v_e_1894_);
v_a_2020_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_1908_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_1908_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify___boxed(lean_object* v_e_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_e_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2037_);
lean_dec(v_a_2036_);
lean_dec_ref(v_a_2035_);
lean_dec(v_a_2034_);
lean_dec_ref(v_a_2033_);
lean_dec(v_a_2032_);
lean_dec(v_a_2031_);
lean_dec(v_a_2030_);
lean_dec(v_a_2029_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(lean_object* v_a_2050_, lean_object* v_b_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_ctx_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_Meta_Grind_mkDiseqProof(v_a_2050_, v_b_2051_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v_type_2071_; lean_object* v_u_2072_; lean_object* v_natModuleInst_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2069_, 1);
v_type_2071_ = lean_ctor_get(v_a_2052_, 2);
lean_inc_ref(v_type_2071_);
v_u_2072_ = lean_ctor_get(v_a_2052_, 3);
lean_inc(v_u_2072_);
v_natModuleInst_2073_ = lean_ctor_get(v_a_2052_, 4);
lean_inc_ref(v_natModuleInst_2073_);
lean_dec_ref(v_a_2052_);
v___x_2074_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2));
v___x_2075_ = lean_box(0);
v___x_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2076_, 0, v_u_2072_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = l_Lean_mkConst(v___x_2074_, v___x_2076_);
v___x_2078_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_2053_);
v___x_2079_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_2054_);
v___x_2080_ = l_Lean_eagerReflBoolTrue;
v___x_2081_ = l_Lean_mkApp6(v___x_2077_, v_type_2071_, v_natModuleInst_2073_, v_ctx_2055_, v___x_2078_, v___x_2079_, v___x_2080_);
v___x_2082_ = l_Lean_Expr_app___override(v_a_2070_, v___x_2081_);
v___x_2083_ = l_Lean_Meta_Grind_closeGoal(v___x_2082_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
return v___x_2083_;
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec_ref(v_ctx_2055_);
lean_dec(v_a_2054_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
v_a_2084_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2069_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2069_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___boxed(lean_object** _args){
lean_object* v_a_2092_ = _args[0];
lean_object* v_b_2093_ = _args[1];
lean_object* v_a_2094_ = _args[2];
lean_object* v_a_2095_ = _args[3];
lean_object* v_a_2096_ = _args[4];
lean_object* v_ctx_2097_ = _args[5];
lean_object* v___y_2098_ = _args[6];
lean_object* v___y_2099_ = _args[7];
lean_object* v___y_2100_ = _args[8];
lean_object* v___y_2101_ = _args[9];
lean_object* v___y_2102_ = _args[10];
lean_object* v___y_2103_ = _args[11];
lean_object* v___y_2104_ = _args[12];
lean_object* v___y_2105_ = _args[13];
lean_object* v___y_2106_ = _args[14];
lean_object* v___y_2107_ = _args[15];
lean_object* v___y_2108_ = _args[16];
lean_object* v___y_2109_ = _args[17];
lean_object* v___y_2110_ = _args[18];
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(v_a_2092_, v_b_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_ctx_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec(v___y_2098_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(lean_object* v___y_2112_){
_start:
{
lean_inc_ref(v___y_2112_);
return v___y_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1___boxed(lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(v___y_2113_);
lean_dec_ref(v___y_2113_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3(lean_object* v_vars_2115_, lean_object* v_x_2116_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = lean_array_fget_borrowed(v_vars_2115_, v_x_2116_);
lean_inc(v___x_2117_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3___boxed(lean_object* v_vars_2118_, lean_object* v_x_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3(v_vars_2118_, v_x_2119_);
lean_dec(v_x_2119_);
lean_dec_ref(v_vars_2118_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(lean_object* v_a_2122_, lean_object* v_b_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v_a_2140_; lean_object* v___y_2144_; lean_object* v___x_2146_; 
v___x_2136_ = lean_unsigned_to_nat(0u);
v___x_2137_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
v___x_2138_ = lean_st_mk_ref(v___x_2137_);
lean_inc_ref(v_a_2122_);
v___x_2146_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_a_2122_, v___x_2138_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2148_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
lean_inc_ref(v_b_2123_);
v___x_2148_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_b_2123_, v___x_2138_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc_n(v_a_2149_, 2);
lean_dec_ref_known(v___x_2148_, 1);
lean_inc(v_a_2147_);
v___x_2150_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_2147_);
v___x_2151_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_2149_);
v___x_2152_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_2150_, v___x_2151_);
lean_dec(v___x_2151_);
lean_dec(v___x_2150_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; 
lean_dec(v_a_2149_);
lean_dec(v_a_2147_);
lean_dec_ref(v_b_2123_);
lean_dec_ref(v_a_2122_);
v___x_2153_ = lean_box(0);
v_a_2140_ = v___x_2153_;
goto v___jp_2139_;
}
else
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2156_; lean_object* v_vars_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2154_, 1);
v___x_2156_ = lean_st_ref_get(v___x_2138_);
v_vars_2157_ = lean_ctor_get(v___x_2156_, 1);
lean_inc_ref(v_vars_2157_);
lean_dec(v___x_2156_);
v___x_2158_ = lean_array_get_size(v_vars_2157_);
v___x_2159_ = lean_nat_dec_lt(v___x_2136_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v_type_2160_; lean_object* v_zero_2161_; lean_object* v___f_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
lean_dec_ref(v_vars_2157_);
v_type_2160_ = lean_ctor_get(v_a_2155_, 2);
v_zero_2161_ = lean_ctor_get(v_a_2155_, 13);
v___f_2162_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0));
lean_inc_ref(v_zero_2161_);
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v_zero_2161_);
lean_inc_ref(v_type_2160_);
v___x_2164_ = l_Lean_RArray_toExpr___redArg(v_type_2160_, v___f_2162_, v___x_2163_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2166_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2164_, 1);
v___x_2166_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(v_a_2122_, v_b_2123_, v_a_2155_, v_a_2147_, v_a_2149_, v_a_2165_, v___x_2138_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
v___y_2144_ = v___x_2166_;
goto v___jp_2143_;
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v_a_2155_);
lean_dec(v_a_2149_);
lean_dec(v_a_2147_);
lean_dec(v___x_2138_);
lean_dec_ref(v_b_2123_);
lean_dec_ref(v_a_2122_);
v_a_2167_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2164_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2164_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v_type_2175_; lean_object* v___f_2176_; lean_object* v___f_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v_type_2175_ = lean_ctor_get(v_a_2155_, 2);
v___f_2176_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0));
v___f_2177_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3___boxed), 2, 1);
lean_closure_set(v___f_2177_, 0, v_vars_2157_);
v___x_2178_ = l_Lean_RArray_ofFn___redArg(v___x_2158_, v___f_2177_);
lean_inc_ref(v_type_2175_);
v___x_2179_ = l_Lean_RArray_toExpr___redArg(v_type_2175_, v___f_2176_, v___x_2178_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2181_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2179_, 1);
v___x_2181_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(v_a_2122_, v_b_2123_, v_a_2155_, v_a_2147_, v_a_2149_, v_a_2180_, v___x_2138_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
v___y_2144_ = v___x_2181_;
goto v___jp_2143_;
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_a_2155_);
lean_dec(v_a_2149_);
lean_dec(v_a_2147_);
lean_dec(v___x_2138_);
lean_dec_ref(v_b_2123_);
lean_dec_ref(v_a_2122_);
v_a_2182_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2179_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2179_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v_a_2149_);
lean_dec(v_a_2147_);
lean_dec(v___x_2138_);
lean_dec_ref(v_b_2123_);
lean_dec_ref(v_a_2122_);
v_a_2190_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2154_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2154_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v_a_2147_);
lean_dec(v___x_2138_);
lean_dec_ref(v_b_2123_);
lean_dec_ref(v_a_2122_);
v_a_2198_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2148_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2148_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v___x_2138_);
lean_dec_ref(v_b_2123_);
lean_dec_ref(v_a_2122_);
v_a_2206_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2146_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2146_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
v___jp_2139_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_st_ref_get(v___x_2138_);
lean_dec(v___x_2138_);
lean_dec(v___x_2141_);
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v_a_2140_);
return v___x_2142_;
}
v___jp_2143_:
{
if (lean_obj_tag(v___y_2144_) == 0)
{
lean_object* v_a_2145_; 
v_a_2145_ = lean_ctor_get(v___y_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___y_2144_, 1);
v_a_2140_ = v_a_2145_;
goto v___jp_2139_;
}
else
{
lean_dec(v___x_2138_);
return v___y_2144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___boxed(lean_object* v_a_2214_, lean_object* v_b_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_2214_, v_b_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec(v_a_2216_);
return v_res_2228_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_OfNatModule(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_NatModuleNorm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_RArray(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
