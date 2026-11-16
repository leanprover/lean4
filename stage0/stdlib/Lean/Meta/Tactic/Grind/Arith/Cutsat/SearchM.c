// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.SearchM
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_diseq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_diseq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_cooper_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_cooper_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7;
static const lean_array_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "search"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 65, 210, 255, 142, 133, 148, 120)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__7;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "reordering request for "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Cutsat_mkCase___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_d_7_; lean_object* v___x_8_; 
v_d_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_d_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_d_7_);
return v___x_8_;
}
else
{
lean_object* v_s_9_; lean_object* v_hs_10_; lean_object* v_decVars_11_; lean_object* v___x_12_; 
v_s_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_s_9_);
v_hs_10_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_hs_10_);
v_decVars_11_ = lean_ctor_get(v_t_5_, 2);
lean_inc(v_decVars_11_);
lean_dec_ref_known(v_t_5_, 3);
v___x_12_ = lean_apply_3(v_k_6_, v_s_9_, v_hs_10_, v_decVars_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_diseq_elim___redArg(lean_object* v_t_25_, lean_object* v_diseq_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_25_, v_diseq_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_diseq_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_diseq_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_29_, v_diseq_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_cooper_elim___redArg(lean_object* v_t_33_, lean_object* v_cooper_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_33_, v_cooper_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_cooper_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_cooper_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_37_, v_cooper_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = lean_nat_to_int(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0);
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_box(0);
v___x_49_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3));
v___x_50_ = l_Lean_Expr_const___override(v___x_49_, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = lean_box(0);
v___x_54_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5);
v___x_55_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1);
v___x_56_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
lean_ctor_set(v___x_56_, 2, v___x_53_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; lean_object* v___x_60_; 
v___x_57_ = lean_box(0);
v___x_58_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6);
v___x_59_ = 0;
v___x_60_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_58_);
lean_ctor_set(v___x_60_, 2, v___x_57_);
lean_ctor_set_uint8(v___x_60_, sizeof(void*)*3, v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = lean_box(1);
v___x_64_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8));
v___x_65_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7);
v___x_66_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
lean_ctor_set(v___x_66_, 2, v___x_63_);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default(void){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind(void){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default;
return v___x_68_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_69_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
v___x_70_ = lean_box(0);
v___x_71_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default;
v___x_72_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_70_);
lean_ctor_set(v___x_72_, 2, v___x_69_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0);
return v___x_73_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default;
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___impl(uint8_t v_x_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_box(v_x_75_);
v___x_77_ = lean_obj_tag_nat(v___x_76_);
lean_dec(v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___impl___boxed(lean_object* v_x_78_){
_start:
{
uint8_t v_x_4__boxed_79_; lean_object* v_res_80_; 
v_x_4__boxed_79_ = lean_unbox(v_x_78_);
v_res_80_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___impl(v_x_4__boxed_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg(lean_object* v_k_81_){
_start:
{
lean_inc(v_k_81_);
return v_k_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg___boxed(lean_object* v_k_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg(v_k_82_);
lean_dec(v_k_82_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(lean_object* v_motive_84_, lean_object* v_ctorIdx_85_, uint8_t v_t_86_, lean_object* v_h_87_, lean_object* v_k_88_){
_start:
{
lean_inc(v_k_88_);
return v_k_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___boxed(lean_object* v_motive_89_, lean_object* v_ctorIdx_90_, lean_object* v_t_91_, lean_object* v_h_92_, lean_object* v_k_93_){
_start:
{
uint8_t v_t_boxed_94_; lean_object* v_res_95_; 
v_t_boxed_94_ = lean_unbox(v_t_91_);
v_res_95_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(v_motive_89_, v_ctorIdx_90_, v_t_boxed_94_, v_h_92_, v_k_93_);
lean_dec(v_k_93_);
lean_dec(v_ctorIdx_90_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(lean_object* v_rat_96_){
_start:
{
lean_inc(v_rat_96_);
return v_rat_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg___boxed(lean_object* v_rat_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(v_rat_97_);
lean_dec(v_rat_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(lean_object* v_motive_99_, uint8_t v_t_100_, lean_object* v_h_101_, lean_object* v_rat_102_){
_start:
{
lean_inc(v_rat_102_);
return v_rat_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___boxed(lean_object* v_motive_103_, lean_object* v_t_104_, lean_object* v_h_105_, lean_object* v_rat_106_){
_start:
{
uint8_t v_t_boxed_107_; lean_object* v_res_108_; 
v_t_boxed_107_ = lean_unbox(v_t_104_);
v_res_108_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(v_motive_103_, v_t_boxed_107_, v_h_105_, v_rat_106_);
lean_dec(v_rat_106_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(lean_object* v_int_109_){
_start:
{
lean_inc(v_int_109_);
return v_int_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg___boxed(lean_object* v_int_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(v_int_110_);
lean_dec(v_int_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(lean_object* v_motive_112_, uint8_t v_t_113_, lean_object* v_h_114_, lean_object* v_int_115_){
_start:
{
lean_inc(v_int_115_);
return v_int_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___boxed(lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_int_119_){
_start:
{
uint8_t v_t_boxed_120_; lean_object* v_res_121_; 
v_t_boxed_120_ = lean_unbox(v_t_117_);
v_res_121_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(v_motive_116_, v_t_boxed_120_, v_h_118_, v_int_119_);
lean_dec(v_int_119_);
return v_res_121_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default(void){
_start:
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind(void){
_start:
{
uint8_t v___x_123_; 
v___x_123_ = 0;
return v___x_123_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(uint8_t v_x_124_, uint8_t v_y_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_126_ = lean_box(v_x_124_);
v___x_127_ = lean_obj_tag_nat(v___x_126_);
lean_dec(v___x_126_);
v___x_128_ = lean_box(v_y_125_);
v___x_129_ = lean_obj_tag_nat(v___x_128_);
lean_dec(v___x_128_);
v___x_130_ = lean_nat_dec_eq(v___x_127_, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq___boxed(lean_object* v_x_131_, lean_object* v_y_132_){
_start:
{
uint8_t v_x_24__boxed_133_; uint8_t v_y_25__boxed_134_; uint8_t v_res_135_; lean_object* v_r_136_; 
v_x_24__boxed_133_ = lean_unbox(v_x_131_);
v_y_25__boxed_134_ = lean_unbox(v_y_132_);
v_res_135_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(v_x_24__boxed_133_, v_y_25__boxed_134_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(uint8_t v_a_139_){
_start:
{
uint8_t v___x_141_; uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_141_ = 0;
v___x_142_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(v_a_139_, v___x_141_);
v___x_143_ = lean_box(v___x_142_);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg___boxed(lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
uint8_t v_a_boxed_147_; lean_object* v_res_148_; 
v_a_boxed_147_ = lean_unbox(v_a_145_);
v_res_148_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(v_a_boxed_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox(uint8_t v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(v_a_149_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___boxed(lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
uint8_t v_a_boxed_176_; lean_object* v_res_177_; 
v_a_boxed_176_ = lean_unbox(v_a_163_);
v_res_177_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox(v_a_boxed_176_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
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
lean_dec(v_a_164_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(lean_object* v_a_178_){
_start:
{
lean_object* v___x_180_; lean_object* v_cases_181_; lean_object* v_decVars_182_; lean_object* v_steps_183_; lean_object* v_reorderRequest_x3f_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_195_; 
v___x_180_ = lean_st_ref_take(v_a_178_);
v_cases_181_ = lean_ctor_get(v___x_180_, 0);
v_decVars_182_ = lean_ctor_get(v___x_180_, 1);
v_steps_183_ = lean_ctor_get(v___x_180_, 2);
v_reorderRequest_x3f_184_ = lean_ctor_get(v___x_180_, 3);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_195_ == 0)
{
v___x_186_ = v___x_180_;
v_isShared_187_ = v_isSharedCheck_195_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_reorderRequest_x3f_184_);
lean_inc(v_steps_183_);
lean_inc(v_decVars_182_);
lean_inc(v_cases_181_);
lean_dec(v___x_180_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_195_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; uint8_t v___x_189_; lean_object* v___x_191_; 
v___x_188_ = lean_box(0);
v___x_189_ = 0;
if (v_isShared_187_ == 0)
{
v___x_191_ = v___x_186_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_cases_181_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_decVars_182_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_steps_183_);
lean_ctor_set(v_reuseFailAlloc_194_, 3, v_reorderRequest_x3f_184_);
v___x_191_ = v_reuseFailAlloc_194_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*4, v___x_189_);
v___x_192_ = lean_st_ref_put(v_a_178_, v___x_191_);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_188_);
return v___x_193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg___boxed(lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(v_a_196_);
lean_dec(v_a_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(uint8_t v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(v_a_200_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___boxed(lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
uint8_t v_a_boxed_226_; lean_object* v_res_227_; 
v_a_boxed_226_ = lean_unbox(v_a_213_);
v_res_227_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(v_a_boxed_226_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec(v_a_215_);
lean_dec(v_a_214_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_233_; lean_object* v_cases_234_; uint8_t v_precise_235_; lean_object* v_decVars_236_; lean_object* v_steps_237_; lean_object* v_reorderRequest_x3f_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_282_; 
v___x_233_ = lean_st_ref_take(v_a_228_);
v_cases_234_ = lean_ctor_get(v___x_233_, 0);
v_precise_235_ = lean_ctor_get_uint8(v___x_233_, sizeof(void*)*4);
v_decVars_236_ = lean_ctor_get(v___x_233_, 1);
v_steps_237_ = lean_ctor_get(v___x_233_, 2);
v_reorderRequest_x3f_238_ = lean_ctor_get(v___x_233_, 3);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_282_ == 0)
{
v___x_240_ = v___x_233_;
v_isShared_241_ = v_isSharedCheck_282_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_reorderRequest_x3f_238_);
lean_inc(v_steps_237_);
lean_inc(v_decVars_236_);
lean_inc(v_cases_234_);
lean_dec(v___x_233_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_282_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_nat_add(v_steps_237_, v___x_242_);
lean_dec(v_steps_237_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 2, v___x_243_);
v___x_245_ = v___x_240_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_cases_234_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_decVars_236_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_reorderRequest_x3f_238_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, sizeof(void*)*4, v_precise_235_);
v___x_245_ = v_reuseFailAlloc_281_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_st_ref_put(v_a_228_, v___x_245_);
v___x_247_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_229_, v_a_231_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_248_);
lean_dec_ref_known(v___x_247_, 1);
v___x_249_ = lean_st_ref_get(v_a_228_);
v___x_250_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_230_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_264_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_264_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_264_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_264_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v_liaSteps_255_; lean_object* v_steps_256_; lean_object* v_steps_257_; lean_object* v___x_258_; uint8_t v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v_liaSteps_255_ = lean_ctor_get(v_a_251_, 10);
lean_inc(v_liaSteps_255_);
lean_dec(v_a_251_);
v_steps_256_ = lean_ctor_get(v_a_248_, 15);
lean_inc(v_steps_256_);
lean_dec(v_a_248_);
v_steps_257_ = lean_ctor_get(v___x_249_, 2);
lean_inc(v_steps_257_);
lean_dec(v___x_249_);
v___x_258_ = lean_nat_add(v_steps_256_, v_steps_257_);
lean_dec(v_steps_257_);
lean_dec(v_steps_256_);
v___x_259_ = lean_nat_dec_lt(v_liaSteps_255_, v___x_258_);
lean_dec(v___x_258_);
lean_dec(v_liaSteps_255_);
v___x_260_ = lean_box(v___x_259_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v___x_260_);
v___x_262_ = v___x_253_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec(v___x_249_);
lean_dec(v_a_248_);
v_a_265_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_250_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_250_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
v_a_273_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_247_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_247_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg___boxed(lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(v_a_283_, v_a_284_, v_a_285_, v_a_286_);
lean_dec_ref(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec(v_a_283_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps(uint8_t v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(v_a_290_, v_a_291_, v_a_293_, v_a_299_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___boxed(lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
uint8_t v_a_boxed_316_; lean_object* v_res_317_; 
v_a_boxed_316_ = lean_unbox(v_a_303_);
v_res_317_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps(v_a_boxed_316_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec(v_a_305_);
lean_dec(v_a_304_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0(lean_object* v_steps_318_, lean_object* v_s_319_){
_start:
{
lean_object* v_vars_320_; lean_object* v_varMap_321_; lean_object* v_varsHistory_322_; lean_object* v_natToIntMap_323_; lean_object* v_natDef_324_; lean_object* v_dvds_325_; lean_object* v_lowers_326_; lean_object* v_uppers_327_; lean_object* v_diseqs_328_; lean_object* v_elimEqs_329_; lean_object* v_active_330_; lean_object* v_elimStack_331_; lean_object* v_occurs_332_; lean_object* v_assignment_333_; lean_object* v_nextCnstrId_334_; uint8_t v_caseSplits_335_; lean_object* v_steps_336_; lean_object* v_penalties_337_; lean_object* v_numReorderRequests_338_; lean_object* v_conflict_x3f_339_; lean_object* v_diseqSplits_340_; lean_object* v_divMod_341_; uint8_t v_usedCommRing_342_; lean_object* v_nonlinearOccs_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_351_; 
v_vars_320_ = lean_ctor_get(v_s_319_, 0);
v_varMap_321_ = lean_ctor_get(v_s_319_, 1);
v_varsHistory_322_ = lean_ctor_get(v_s_319_, 2);
v_natToIntMap_323_ = lean_ctor_get(v_s_319_, 3);
v_natDef_324_ = lean_ctor_get(v_s_319_, 4);
v_dvds_325_ = lean_ctor_get(v_s_319_, 5);
v_lowers_326_ = lean_ctor_get(v_s_319_, 6);
v_uppers_327_ = lean_ctor_get(v_s_319_, 7);
v_diseqs_328_ = lean_ctor_get(v_s_319_, 8);
v_elimEqs_329_ = lean_ctor_get(v_s_319_, 9);
v_active_330_ = lean_ctor_get(v_s_319_, 10);
v_elimStack_331_ = lean_ctor_get(v_s_319_, 11);
v_occurs_332_ = lean_ctor_get(v_s_319_, 12);
v_assignment_333_ = lean_ctor_get(v_s_319_, 13);
v_nextCnstrId_334_ = lean_ctor_get(v_s_319_, 14);
v_caseSplits_335_ = lean_ctor_get_uint8(v_s_319_, sizeof(void*)*22);
v_steps_336_ = lean_ctor_get(v_s_319_, 15);
v_penalties_337_ = lean_ctor_get(v_s_319_, 16);
v_numReorderRequests_338_ = lean_ctor_get(v_s_319_, 17);
v_conflict_x3f_339_ = lean_ctor_get(v_s_319_, 18);
v_diseqSplits_340_ = lean_ctor_get(v_s_319_, 19);
v_divMod_341_ = lean_ctor_get(v_s_319_, 20);
v_usedCommRing_342_ = lean_ctor_get_uint8(v_s_319_, sizeof(void*)*22 + 1);
v_nonlinearOccs_343_ = lean_ctor_get(v_s_319_, 21);
v_isSharedCheck_351_ = !lean_is_exclusive(v_s_319_);
if (v_isSharedCheck_351_ == 0)
{
v___x_345_ = v_s_319_;
v_isShared_346_ = v_isSharedCheck_351_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_nonlinearOccs_343_);
lean_inc(v_divMod_341_);
lean_inc(v_diseqSplits_340_);
lean_inc(v_conflict_x3f_339_);
lean_inc(v_numReorderRequests_338_);
lean_inc(v_penalties_337_);
lean_inc(v_steps_336_);
lean_inc(v_nextCnstrId_334_);
lean_inc(v_assignment_333_);
lean_inc(v_occurs_332_);
lean_inc(v_elimStack_331_);
lean_inc(v_active_330_);
lean_inc(v_elimEqs_329_);
lean_inc(v_diseqs_328_);
lean_inc(v_uppers_327_);
lean_inc(v_lowers_326_);
lean_inc(v_dvds_325_);
lean_inc(v_natDef_324_);
lean_inc(v_natToIntMap_323_);
lean_inc(v_varsHistory_322_);
lean_inc(v_varMap_321_);
lean_inc(v_vars_320_);
lean_dec(v_s_319_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_351_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_347_ = lean_nat_add(v_steps_336_, v_steps_318_);
lean_dec(v_steps_336_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 15, v___x_347_);
v___x_349_ = v___x_345_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_vars_320_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_varMap_321_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_varsHistory_322_);
lean_ctor_set(v_reuseFailAlloc_350_, 3, v_natToIntMap_323_);
lean_ctor_set(v_reuseFailAlloc_350_, 4, v_natDef_324_);
lean_ctor_set(v_reuseFailAlloc_350_, 5, v_dvds_325_);
lean_ctor_set(v_reuseFailAlloc_350_, 6, v_lowers_326_);
lean_ctor_set(v_reuseFailAlloc_350_, 7, v_uppers_327_);
lean_ctor_set(v_reuseFailAlloc_350_, 8, v_diseqs_328_);
lean_ctor_set(v_reuseFailAlloc_350_, 9, v_elimEqs_329_);
lean_ctor_set(v_reuseFailAlloc_350_, 10, v_active_330_);
lean_ctor_set(v_reuseFailAlloc_350_, 11, v_elimStack_331_);
lean_ctor_set(v_reuseFailAlloc_350_, 12, v_occurs_332_);
lean_ctor_set(v_reuseFailAlloc_350_, 13, v_assignment_333_);
lean_ctor_set(v_reuseFailAlloc_350_, 14, v_nextCnstrId_334_);
lean_ctor_set(v_reuseFailAlloc_350_, 15, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_350_, 16, v_penalties_337_);
lean_ctor_set(v_reuseFailAlloc_350_, 17, v_numReorderRequests_338_);
lean_ctor_set(v_reuseFailAlloc_350_, 18, v_conflict_x3f_339_);
lean_ctor_set(v_reuseFailAlloc_350_, 19, v_diseqSplits_340_);
lean_ctor_set(v_reuseFailAlloc_350_, 20, v_divMod_341_);
lean_ctor_set(v_reuseFailAlloc_350_, 21, v_nonlinearOccs_343_);
lean_ctor_set_uint8(v_reuseFailAlloc_350_, sizeof(void*)*22, v_caseSplits_335_);
lean_ctor_set_uint8(v_reuseFailAlloc_350_, sizeof(void*)*22 + 1, v_usedCommRing_342_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0___boxed(lean_object* v_steps_352_, lean_object* v_s_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0(v_steps_352_, v_s_353_);
lean_dec(v_steps_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_358_; lean_object* v_steps_359_; lean_object* v___f_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_358_ = lean_st_ref_get(v_a_355_);
v_steps_359_ = lean_ctor_get(v___x_358_, 2);
lean_inc(v_steps_359_);
lean_dec(v___x_358_);
v___f_360_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_360_, 0, v_steps_359_);
v___x_361_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_362_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_361_, v___f_360_, v_a_356_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___boxed(lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec(v_a_363_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps(uint8_t v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(v_a_368_, v_a_369_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___boxed(lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
uint8_t v_a_boxed_394_; lean_object* v_res_395_; 
v_a_boxed_394_ = lean_unbox(v_a_381_);
v_res_395_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps(v_a_boxed_394_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec(v_a_383_);
lean_dec(v_a_382_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0_spec__0(lean_object* v_msgData_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; lean_object* v_env_403_; uint8_t v___x_404_; lean_object* v_env_405_; lean_object* v___x_406_; lean_object* v_toCold_407_; lean_object* v_mctx_408_; lean_object* v_lctx_409_; lean_object* v_options_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_402_ = lean_st_ref_get(v___y_400_);
v_env_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc_ref(v_env_403_);
lean_dec(v___x_402_);
v___x_404_ = 0;
v_env_405_ = l_Lean_Environment_setRecordingDeps(v_env_403_, v___x_404_);
v___x_406_ = lean_st_ref_get(v___y_398_);
v_toCold_407_ = lean_ctor_get(v___y_399_, 0);
v_mctx_408_ = lean_ctor_get(v___x_406_, 0);
lean_inc_ref(v_mctx_408_);
lean_dec(v___x_406_);
v_lctx_409_ = lean_ctor_get(v___y_397_, 2);
v_options_410_ = lean_ctor_get(v_toCold_407_, 2);
lean_inc_ref(v_options_410_);
lean_inc_ref(v_lctx_409_);
v___x_411_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_411_, 0, v_env_405_);
lean_ctor_set(v___x_411_, 1, v_mctx_408_);
lean_ctor_set(v___x_411_, 2, v_lctx_409_);
lean_ctor_set(v___x_411_, 3, v_options_410_);
v___x_412_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v_msgData_396_);
v___x_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0_spec__0___boxed(lean_object* v_msgData_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0_spec__0(v_msgData_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_420_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_421_; double v___x_422_; 
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_float_of_nat(v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg(lean_object* v_cls_426_, lean_object* v_msg_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_ref_433_; lean_object* v___x_434_; lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_480_; 
v_ref_433_ = lean_ctor_get(v___y_430_, 2);
v___x_434_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0_spec__0(v_msg_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_480_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_480_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_480_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v_traceState_440_; lean_object* v_env_441_; lean_object* v_nextMacroScope_442_; lean_object* v_ngen_443_; lean_object* v_auxDeclNGen_444_; lean_object* v_cache_445_; lean_object* v_recordedDeps_446_; lean_object* v_messages_447_; lean_object* v_infoState_448_; lean_object* v_snapshotTasks_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_479_; 
v___x_439_ = lean_st_ref_take(v___y_431_);
v_traceState_440_ = lean_ctor_get(v___x_439_, 4);
v_env_441_ = lean_ctor_get(v___x_439_, 0);
v_nextMacroScope_442_ = lean_ctor_get(v___x_439_, 1);
v_ngen_443_ = lean_ctor_get(v___x_439_, 2);
v_auxDeclNGen_444_ = lean_ctor_get(v___x_439_, 3);
v_cache_445_ = lean_ctor_get(v___x_439_, 5);
v_recordedDeps_446_ = lean_ctor_get(v___x_439_, 6);
v_messages_447_ = lean_ctor_get(v___x_439_, 7);
v_infoState_448_ = lean_ctor_get(v___x_439_, 8);
v_snapshotTasks_449_ = lean_ctor_get(v___x_439_, 9);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_479_ == 0)
{
v___x_451_ = v___x_439_;
v_isShared_452_ = v_isSharedCheck_479_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_snapshotTasks_449_);
lean_inc(v_infoState_448_);
lean_inc(v_messages_447_);
lean_inc(v_recordedDeps_446_);
lean_inc(v_cache_445_);
lean_inc(v_traceState_440_);
lean_inc(v_auxDeclNGen_444_);
lean_inc(v_ngen_443_);
lean_inc(v_nextMacroScope_442_);
lean_inc(v_env_441_);
lean_dec(v___x_439_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_479_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
uint64_t v_tid_453_; lean_object* v_traces_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_478_; 
v_tid_453_ = lean_ctor_get_uint64(v_traceState_440_, sizeof(void*)*1);
v_traces_454_ = lean_ctor_get(v_traceState_440_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v_traceState_440_);
if (v_isSharedCheck_478_ == 0)
{
v___x_456_ = v_traceState_440_;
v_isShared_457_ = v_isSharedCheck_478_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_traces_454_);
lean_dec(v_traceState_440_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_478_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_459_; double v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_458_ = lean_box(0);
v___x_459_ = lean_box(0);
v___x_460_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__0);
v___x_461_ = 0;
v___x_462_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__1));
v___x_463_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_463_, 0, v_cls_426_);
lean_ctor_set(v___x_463_, 1, v___x_459_);
lean_ctor_set(v___x_463_, 2, v___x_462_);
lean_ctor_set_float(v___x_463_, sizeof(void*)*3, v___x_460_);
lean_ctor_set_float(v___x_463_, sizeof(void*)*3 + 8, v___x_460_);
lean_ctor_set_uint8(v___x_463_, sizeof(void*)*3 + 16, v___x_461_);
v___x_464_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__2));
v___x_465_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v_a_435_);
lean_ctor_set(v___x_465_, 2, v___x_464_);
lean_inc(v_ref_433_);
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v_ref_433_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = l_Lean_PersistentArray_push___redArg(v_traces_454_, v___x_466_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_467_);
v___x_469_ = v___x_456_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_467_);
lean_ctor_set_uint64(v_reuseFailAlloc_477_, sizeof(void*)*1, v_tid_453_);
v___x_469_ = v_reuseFailAlloc_477_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_471_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 4, v___x_469_);
v___x_471_ = v___x_451_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_env_441_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_nextMacroScope_442_);
lean_ctor_set(v_reuseFailAlloc_476_, 2, v_ngen_443_);
lean_ctor_set(v_reuseFailAlloc_476_, 3, v_auxDeclNGen_444_);
lean_ctor_set(v_reuseFailAlloc_476_, 4, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_476_, 5, v_cache_445_);
lean_ctor_set(v_reuseFailAlloc_476_, 6, v_recordedDeps_446_);
lean_ctor_set(v_reuseFailAlloc_476_, 7, v_messages_447_);
lean_ctor_set(v_reuseFailAlloc_476_, 8, v_infoState_448_);
lean_ctor_set(v_reuseFailAlloc_476_, 9, v_snapshotTasks_449_);
v___x_471_ = v_reuseFailAlloc_476_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_472_ = lean_st_ref_put(v___y_431_, v___x_471_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_458_);
v___x_474_ = v___x_437_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_458_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___boxed(lean_object* v_cls_481_, lean_object* v_msg_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg(v_cls_481_, v_msg_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
return v_res_488_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__7(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__4));
v___x_502_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__6));
v___x_503_ = l_Lean_Name_append(v___x_502_, v___x_501_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__9(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__8));
v___x_506_ = l_Lean_stringToMessageData(v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder(lean_object* v_x_507_, uint8_t v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_510_, v_a_518_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
v___x_523_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_512_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_591_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_591_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_591_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_591_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v_liaReorders_528_; lean_object* v_numReorderRequests_529_; uint8_t v___x_530_; 
v_liaReorders_528_ = lean_ctor_get(v_a_524_, 11);
lean_inc(v_liaReorders_528_);
lean_dec(v_a_524_);
v_numReorderRequests_529_ = lean_ctor_get(v_a_522_, 17);
lean_inc(v_numReorderRequests_529_);
lean_dec(v_a_522_);
v___x_530_ = lean_nat_dec_le(v_liaReorders_528_, v_numReorderRequests_529_);
lean_dec(v_numReorderRequests_529_);
lean_dec(v_liaReorders_528_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; 
lean_del_object(v___x_526_);
v___x_531_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_507_, v_a_510_, v_a_518_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_577_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_577_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_577_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_577_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___y_537_; lean_object* v_toCold_558_; lean_object* v_options_559_; uint8_t v_hasTrace_560_; 
v_toCold_558_ = lean_ctor_get(v_a_518_, 0);
v_options_559_ = lean_ctor_get(v_toCold_558_, 2);
v_hasTrace_560_ = lean_ctor_get_uint8(v_options_559_, sizeof(void*)*1);
if (v_hasTrace_560_ == 0)
{
v___y_537_ = v_a_509_;
goto v___jp_536_;
}
else
{
lean_object* v_inheritedTraceOptions_561_; lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_inheritedTraceOptions_561_ = lean_ctor_get(v_toCold_558_, 11);
v___x_562_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__4));
v___x_563_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__7);
v___x_564_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_561_, v_options_559_, v___x_563_);
if (v___x_564_ == 0)
{
v___y_537_ = v_a_509_;
goto v___jp_536_;
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_565_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__9);
lean_inc(v_a_532_);
v___x_566_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_532_);
v___x_567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg(v___x_562_, v___x_567_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_dec_ref_known(v___x_568_, 1);
v___y_537_ = v_a_509_;
goto v___jp_536_;
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_del_object(v___x_534_);
lean_dec(v_a_532_);
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
v___jp_536_:
{
lean_object* v___x_538_; lean_object* v_cases_539_; uint8_t v_precise_540_; lean_object* v_decVars_541_; lean_object* v_steps_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_556_; 
v___x_538_ = lean_st_ref_take(v___y_537_);
v_cases_539_ = lean_ctor_get(v___x_538_, 0);
v_precise_540_ = lean_ctor_get_uint8(v___x_538_, sizeof(void*)*4);
v_decVars_541_ = lean_ctor_get(v___x_538_, 1);
v_steps_542_ = lean_ctor_get(v___x_538_, 2);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v___x_538_, 3);
lean_dec(v_unused_557_);
v___x_544_ = v___x_538_;
v_isShared_545_ = v_isSharedCheck_556_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_steps_542_);
lean_inc(v_decVars_541_);
lean_inc(v_cases_539_);
lean_dec(v___x_538_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_556_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v_a_532_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 3, v___x_546_);
v___x_548_ = v___x_544_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_cases_539_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_decVars_541_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_steps_542_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v___x_546_);
lean_ctor_set_uint8(v_reuseFailAlloc_555_, sizeof(void*)*4, v_precise_540_);
v___x_548_ = v_reuseFailAlloc_555_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_549_; uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_549_ = lean_st_ref_put(v___y_537_, v___x_548_);
v___x_550_ = 1;
v___x_551_ = lean_box(v___x_550_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_551_);
v___x_553_ = v___x_534_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
v_a_578_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_531_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_531_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
uint8_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_586_ = 0;
v___x_587_ = lean_box(v___x_586_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_587_);
v___x_589_ = v___x_526_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
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
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec(v_a_522_);
v_a_592_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_523_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_523_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
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
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
v_a_600_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_521_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_521_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___boxed(lean_object* v_x_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
uint8_t v_a_boxed_622_; lean_object* v_res_623_; 
v_a_boxed_622_ = lean_unbox(v_a_609_);
v_res_623_ = l_Lean_Meta_Grind_Arith_Cutsat_requestReorder(v_x_608_, v_a_boxed_622_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec(v_a_611_);
lean_dec(v_a_610_);
lean_dec(v_x_608_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0(lean_object* v_cls_624_, lean_object* v_msg_625_, uint8_t v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg(v_cls_624_, v_msg_625_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___boxed(lean_object* v_cls_640_, lean_object* v_msg_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
uint8_t v___y_24235__boxed_655_; lean_object* v_res_656_; 
v___y_24235__boxed_655_ = lean_unbox(v___y_642_);
v_res_656_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0(v_cls_640_, v_msg_641_, v___y_24235__boxed_655_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec(v___y_644_);
lean_dec(v___y_643_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_657_, lean_object* v_vals_658_, lean_object* v_i_659_, lean_object* v_k_660_){
_start:
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = lean_array_get_size(v_keys_657_);
v___x_662_ = lean_nat_dec_lt(v_i_659_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
lean_dec(v_i_659_);
v___x_663_ = lean_box(0);
return v___x_663_;
}
else
{
lean_object* v_k_x27_664_; size_t v___x_665_; size_t v___x_666_; uint8_t v___x_667_; 
v_k_x27_664_ = lean_array_fget_borrowed(v_keys_657_, v_i_659_);
v___x_665_ = lean_ptr_addr(v_k_660_);
v___x_666_ = lean_ptr_addr(v_k_x27_664_);
v___x_667_ = lean_usize_dec_eq(v___x_665_, v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_unsigned_to_nat(1u);
v___x_669_ = lean_nat_add(v_i_659_, v___x_668_);
lean_dec(v_i_659_);
v_i_659_ = v___x_669_;
goto _start;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_array_fget_borrowed(v_vals_658_, v_i_659_);
lean_dec(v_i_659_);
lean_inc(v___x_671_);
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_673_, lean_object* v_vals_674_, lean_object* v_i_675_, lean_object* v_k_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg(v_keys_673_, v_vals_674_, v_i_675_, v_k_676_);
lean_dec_ref(v_k_676_);
lean_dec_ref(v_vals_674_);
lean_dec_ref(v_keys_673_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg(lean_object* v_x_678_, size_t v_x_679_, lean_object* v_x_680_){
_start:
{
if (lean_obj_tag(v_x_678_) == 0)
{
lean_object* v_es_681_; lean_object* v___x_682_; size_t v___x_683_; size_t v___x_684_; lean_object* v_j_685_; lean_object* v___x_686_; 
v_es_681_ = lean_ctor_get(v_x_678_, 0);
v___x_682_ = lean_box(2);
v___x_683_ = ((size_t)31ULL);
v___x_684_ = lean_usize_land(v_x_679_, v___x_683_);
v_j_685_ = lean_usize_to_nat(v___x_684_);
v___x_686_ = lean_array_get_borrowed(v___x_682_, v_es_681_, v_j_685_);
lean_dec(v_j_685_);
switch(lean_obj_tag(v___x_686_))
{
case 0:
{
lean_object* v_key_687_; lean_object* v_val_688_; size_t v___x_689_; size_t v___x_690_; uint8_t v___x_691_; 
v_key_687_ = lean_ctor_get(v___x_686_, 0);
v_val_688_ = lean_ctor_get(v___x_686_, 1);
v___x_689_ = lean_ptr_addr(v_x_680_);
v___x_690_ = lean_ptr_addr(v_key_687_);
v___x_691_ = lean_usize_dec_eq(v___x_689_, v___x_690_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; 
v___x_692_ = lean_box(0);
return v___x_692_;
}
else
{
lean_object* v___x_693_; 
lean_inc(v_val_688_);
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v_val_688_);
return v___x_693_;
}
}
case 1:
{
lean_object* v_node_694_; size_t v___x_695_; size_t v___x_696_; 
v_node_694_ = lean_ctor_get(v___x_686_, 0);
v___x_695_ = ((size_t)5ULL);
v___x_696_ = lean_usize_shift_right(v_x_679_, v___x_695_);
v_x_678_ = v_node_694_;
v_x_679_ = v___x_696_;
goto _start;
}
default: 
{
lean_object* v___x_698_; 
v___x_698_ = lean_box(0);
return v___x_698_;
}
}
}
else
{
lean_object* v_ks_699_; lean_object* v_vs_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_ks_699_ = lean_ctor_get(v_x_678_, 0);
v_vs_700_ = lean_ctor_get(v_x_678_, 1);
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg(v_ks_699_, v_vs_700_, v___x_701_, v_x_680_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg___boxed(lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_x_705_){
_start:
{
size_t v_x_4597__boxed_706_; lean_object* v_res_707_; 
v_x_4597__boxed_706_ = lean_unbox_usize(v_x_704_);
lean_dec(v_x_704_);
v_res_707_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg(v_x_703_, v_x_4597__boxed_706_, v_x_705_);
lean_dec_ref(v_x_705_);
lean_dec_ref(v_x_703_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg(lean_object* v_x_708_, lean_object* v_x_709_){
_start:
{
size_t v___x_710_; size_t v___x_711_; size_t v___x_712_; uint64_t v___x_713_; size_t v___x_714_; lean_object* v___x_715_; 
v___x_710_ = lean_ptr_addr(v_x_709_);
v___x_711_ = ((size_t)3ULL);
v___x_712_ = lean_usize_shift_right(v___x_710_, v___x_711_);
v___x_713_ = lean_usize_to_uint64(v___x_712_);
v___x_714_ = lean_uint64_to_usize(v___x_713_);
v___x_715_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg(v_x_708_, v___x_714_, v_x_709_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg___boxed(lean_object* v_x_716_, lean_object* v_x_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg(v_x_716_, v_x_717_);
lean_dec_ref(v_x_717_);
lean_dec_ref(v_x_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_719_, lean_object* v_x_720_, lean_object* v_x_721_, lean_object* v_x_722_){
_start:
{
lean_object* v_ks_723_; lean_object* v_vs_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_750_; 
v_ks_723_ = lean_ctor_get(v_x_719_, 0);
v_vs_724_ = lean_ctor_get(v_x_719_, 1);
v_isSharedCheck_750_ = !lean_is_exclusive(v_x_719_);
if (v_isSharedCheck_750_ == 0)
{
v___x_726_ = v_x_719_;
v_isShared_727_ = v_isSharedCheck_750_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_vs_724_);
lean_inc(v_ks_723_);
lean_dec(v_x_719_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_750_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = lean_array_get_size(v_ks_723_);
v___x_729_ = lean_nat_dec_lt(v_x_720_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
lean_dec(v_x_720_);
v___x_730_ = lean_array_push(v_ks_723_, v_x_721_);
v___x_731_ = lean_array_push(v_vs_724_, v_x_722_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v___x_731_);
lean_ctor_set(v___x_726_, 0, v___x_730_);
v___x_733_ = v___x_726_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
else
{
lean_object* v_k_x27_735_; size_t v___x_736_; size_t v___x_737_; uint8_t v___x_738_; 
v_k_x27_735_ = lean_array_fget_borrowed(v_ks_723_, v_x_720_);
v___x_736_ = lean_ptr_addr(v_x_721_);
v___x_737_ = lean_ptr_addr(v_k_x27_735_);
v___x_738_ = lean_usize_dec_eq(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_740_; 
if (v_isShared_727_ == 0)
{
v___x_740_ = v___x_726_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_ks_723_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_vs_724_);
v___x_740_ = v_reuseFailAlloc_744_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_unsigned_to_nat(1u);
v___x_742_ = lean_nat_add(v_x_720_, v___x_741_);
lean_dec(v_x_720_);
v_x_719_ = v___x_740_;
v_x_720_ = v___x_742_;
goto _start;
}
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_745_ = lean_array_fset(v_ks_723_, v_x_720_, v_x_721_);
v___x_746_ = lean_array_fset(v_vs_724_, v_x_720_, v_x_722_);
lean_dec(v_x_720_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v___x_746_);
lean_ctor_set(v___x_726_, 0, v___x_745_);
v___x_748_ = v___x_726_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1___redArg(lean_object* v_n_751_, lean_object* v_k_752_, lean_object* v_v_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1_spec__3___redArg(v_n_751_, v___x_754_, v_k_752_, v_v_753_);
return v___x_755_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(lean_object* v_x_757_, size_t v_x_758_, size_t v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
if (lean_obj_tag(v_x_757_) == 0)
{
lean_object* v_es_762_; size_t v___x_763_; size_t v___x_764_; lean_object* v_j_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_es_762_ = lean_ctor_get(v_x_757_, 0);
v___x_763_ = ((size_t)31ULL);
v___x_764_ = lean_usize_land(v_x_758_, v___x_763_);
v_j_765_ = lean_usize_to_nat(v___x_764_);
v___x_766_ = lean_array_get_size(v_es_762_);
v___x_767_ = lean_nat_dec_lt(v_j_765_, v___x_766_);
if (v___x_767_ == 0)
{
lean_dec(v_j_765_);
lean_dec(v_x_761_);
lean_dec_ref(v_x_760_);
return v_x_757_;
}
else
{
lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_808_; 
lean_inc_ref(v_es_762_);
v_isSharedCheck_808_ = !lean_is_exclusive(v_x_757_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v_x_757_, 0);
lean_dec(v_unused_809_);
v___x_769_ = v_x_757_;
v_isShared_770_ = v_isSharedCheck_808_;
goto v_resetjp_768_;
}
else
{
lean_dec(v_x_757_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_808_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_v_771_; lean_object* v___x_772_; lean_object* v_xs_x27_773_; lean_object* v___y_775_; 
v_v_771_ = lean_array_fget(v_es_762_, v_j_765_);
v___x_772_ = lean_box(0);
v_xs_x27_773_ = lean_array_fset(v_es_762_, v_j_765_, v___x_772_);
switch(lean_obj_tag(v_v_771_))
{
case 0:
{
lean_object* v_key_780_; lean_object* v_val_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_793_; 
v_key_780_ = lean_ctor_get(v_v_771_, 0);
v_val_781_ = lean_ctor_get(v_v_771_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_v_771_);
if (v_isSharedCheck_793_ == 0)
{
v___x_783_ = v_v_771_;
v_isShared_784_ = v_isSharedCheck_793_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_val_781_);
lean_inc(v_key_780_);
lean_dec(v_v_771_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_793_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
size_t v___x_785_; size_t v___x_786_; uint8_t v___x_787_; 
v___x_785_ = lean_ptr_addr(v_x_760_);
v___x_786_ = lean_ptr_addr(v_key_780_);
v___x_787_ = lean_usize_dec_eq(v___x_785_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; 
lean_del_object(v___x_783_);
v___x_788_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_780_, v_val_781_, v_x_760_, v_x_761_);
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
v___y_775_ = v___x_789_;
goto v___jp_774_;
}
else
{
lean_object* v___x_791_; 
lean_dec(v_val_781_);
lean_dec(v_key_780_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v_x_761_);
lean_ctor_set(v___x_783_, 0, v_x_760_);
v___x_791_ = v___x_783_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_x_760_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_x_761_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
v___y_775_ = v___x_791_;
goto v___jp_774_;
}
}
}
}
case 1:
{
lean_object* v_node_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_806_; 
v_node_794_ = lean_ctor_get(v_v_771_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_v_771_);
if (v_isSharedCheck_806_ == 0)
{
v___x_796_ = v_v_771_;
v_isShared_797_ = v_isSharedCheck_806_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_node_794_);
lean_dec(v_v_771_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_806_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
size_t v___x_798_; size_t v___x_799_; size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_798_ = ((size_t)5ULL);
v___x_799_ = lean_usize_shift_right(v_x_758_, v___x_798_);
v___x_800_ = ((size_t)1ULL);
v___x_801_ = lean_usize_add(v_x_759_, v___x_800_);
v___x_802_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(v_node_794_, v___x_799_, v___x_801_, v_x_760_, v_x_761_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_802_);
v___x_804_ = v___x_796_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
v___y_775_ = v___x_804_;
goto v___jp_774_;
}
}
}
default: 
{
lean_object* v___x_807_; 
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_x_760_);
lean_ctor_set(v___x_807_, 1, v_x_761_);
v___y_775_ = v___x_807_;
goto v___jp_774_;
}
}
v___jp_774_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = lean_array_fset(v_xs_x27_773_, v_j_765_, v___y_775_);
lean_dec(v_j_765_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_776_);
v___x_778_ = v___x_769_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
else
{
lean_object* v_ks_810_; lean_object* v_vs_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_829_; 
v_ks_810_ = lean_ctor_get(v_x_757_, 0);
v_vs_811_ = lean_ctor_get(v_x_757_, 1);
v_isSharedCheck_829_ = !lean_is_exclusive(v_x_757_);
if (v_isSharedCheck_829_ == 0)
{
v___x_813_ = v_x_757_;
v_isShared_814_ = v_isSharedCheck_829_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_vs_811_);
lean_inc(v_ks_810_);
lean_dec(v_x_757_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_829_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_ks_810_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_vs_811_);
v___x_816_ = v_reuseFailAlloc_828_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v_newNode_817_; size_t v___x_818_; uint8_t v___x_819_; 
v_newNode_817_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1___redArg(v___x_816_, v_x_760_, v_x_761_);
v___x_818_ = ((size_t)7ULL);
v___x_819_ = lean_usize_dec_le(v___x_818_, v_x_759_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_820_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_817_);
v___x_821_ = lean_unsigned_to_nat(4u);
v___x_822_ = lean_nat_dec_lt(v___x_820_, v___x_821_);
lean_dec(v___x_820_);
if (v___x_822_ == 0)
{
lean_object* v_ks_823_; lean_object* v_vs_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_ks_823_ = lean_ctor_get(v_newNode_817_, 0);
lean_inc_ref(v_ks_823_);
v_vs_824_ = lean_ctor_get(v_newNode_817_, 1);
lean_inc_ref(v_vs_824_);
lean_dec_ref(v_newNode_817_);
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___closed__0);
v___x_827_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg(v_x_759_, v_ks_823_, v_vs_824_, v___x_825_, v___x_826_);
lean_dec_ref(v_vs_824_);
lean_dec_ref(v_ks_823_);
return v___x_827_;
}
else
{
return v_newNode_817_;
}
}
else
{
return v_newNode_817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg(size_t v_depth_830_, lean_object* v_keys_831_, lean_object* v_vals_832_, lean_object* v_i_833_, lean_object* v_entries_834_){
_start:
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = lean_array_get_size(v_keys_831_);
v___x_836_ = lean_nat_dec_lt(v_i_833_, v___x_835_);
if (v___x_836_ == 0)
{
lean_dec(v_i_833_);
return v_entries_834_;
}
else
{
lean_object* v_k_837_; lean_object* v_v_838_; size_t v___x_839_; size_t v___x_840_; size_t v___x_841_; uint64_t v___x_842_; size_t v_h_843_; size_t v___x_844_; lean_object* v___x_845_; size_t v___x_846_; size_t v___x_847_; size_t v___x_848_; size_t v_h_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_k_837_ = lean_array_fget_borrowed(v_keys_831_, v_i_833_);
v_v_838_ = lean_array_fget_borrowed(v_vals_832_, v_i_833_);
v___x_839_ = lean_ptr_addr(v_k_837_);
v___x_840_ = ((size_t)3ULL);
v___x_841_ = lean_usize_shift_right(v___x_839_, v___x_840_);
v___x_842_ = lean_usize_to_uint64(v___x_841_);
v_h_843_ = lean_uint64_to_usize(v___x_842_);
v___x_844_ = ((size_t)5ULL);
v___x_845_ = lean_unsigned_to_nat(1u);
v___x_846_ = ((size_t)1ULL);
v___x_847_ = lean_usize_sub(v_depth_830_, v___x_846_);
v___x_848_ = lean_usize_mul(v___x_844_, v___x_847_);
v_h_849_ = lean_usize_shift_right(v_h_843_, v___x_848_);
v___x_850_ = lean_nat_add(v_i_833_, v___x_845_);
lean_dec(v_i_833_);
lean_inc(v_v_838_);
lean_inc(v_k_837_);
v___x_851_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(v_entries_834_, v_h_849_, v_depth_830_, v_k_837_, v_v_838_);
v_i_833_ = v___x_850_;
v_entries_834_ = v___x_851_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_853_, lean_object* v_keys_854_, lean_object* v_vals_855_, lean_object* v_i_856_, lean_object* v_entries_857_){
_start:
{
size_t v_depth_boxed_858_; lean_object* v_res_859_; 
v_depth_boxed_858_ = lean_unbox_usize(v_depth_853_);
lean_dec(v_depth_853_);
v_res_859_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg(v_depth_boxed_858_, v_keys_854_, v_vals_855_, v_i_856_, v_entries_857_);
lean_dec_ref(v_vals_855_);
lean_dec_ref(v_keys_854_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___boxed(lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
size_t v_x_4749__boxed_865_; size_t v_x_4750__boxed_866_; lean_object* v_res_867_; 
v_x_4749__boxed_865_ = lean_unbox_usize(v_x_861_);
lean_dec(v_x_861_);
v_x_4750__boxed_866_ = lean_unbox_usize(v_x_862_);
lean_dec(v_x_862_);
v_res_867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(v_x_860_, v_x_4749__boxed_865_, v_x_4750__boxed_866_, v_x_863_, v_x_864_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0___redArg(lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
size_t v___x_871_; size_t v___x_872_; size_t v___x_873_; uint64_t v___x_874_; size_t v___x_875_; size_t v___x_876_; lean_object* v___x_877_; 
v___x_871_ = lean_ptr_addr(v_x_869_);
v___x_872_ = ((size_t)3ULL);
v___x_873_ = lean_usize_shift_right(v___x_871_, v___x_872_);
v___x_874_ = lean_usize_to_uint64(v___x_873_);
v___x_875_ = lean_uint64_to_usize(v___x_874_);
v___x_876_ = ((size_t)1ULL);
v___x_877_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(v_x_868_, v___x_875_, v___x_876_, v_x_869_, v_x_870_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg___lam__0(lean_object* v_val_878_, lean_object* v_s_879_){
_start:
{
lean_object* v_vars_880_; lean_object* v_varMap_881_; lean_object* v_varsHistory_882_; lean_object* v_natToIntMap_883_; lean_object* v_natDef_884_; lean_object* v_dvds_885_; lean_object* v_lowers_886_; lean_object* v_uppers_887_; lean_object* v_diseqs_888_; lean_object* v_elimEqs_889_; lean_object* v_active_890_; lean_object* v_elimStack_891_; lean_object* v_occurs_892_; lean_object* v_assignment_893_; lean_object* v_nextCnstrId_894_; uint8_t v_caseSplits_895_; lean_object* v_steps_896_; lean_object* v_penalties_897_; lean_object* v_numReorderRequests_898_; lean_object* v_conflict_x3f_899_; lean_object* v_diseqSplits_900_; lean_object* v_divMod_901_; uint8_t v_usedCommRing_902_; lean_object* v_nonlinearOccs_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_919_; 
v_vars_880_ = lean_ctor_get(v_s_879_, 0);
v_varMap_881_ = lean_ctor_get(v_s_879_, 1);
v_varsHistory_882_ = lean_ctor_get(v_s_879_, 2);
v_natToIntMap_883_ = lean_ctor_get(v_s_879_, 3);
v_natDef_884_ = lean_ctor_get(v_s_879_, 4);
v_dvds_885_ = lean_ctor_get(v_s_879_, 5);
v_lowers_886_ = lean_ctor_get(v_s_879_, 6);
v_uppers_887_ = lean_ctor_get(v_s_879_, 7);
v_diseqs_888_ = lean_ctor_get(v_s_879_, 8);
v_elimEqs_889_ = lean_ctor_get(v_s_879_, 9);
v_active_890_ = lean_ctor_get(v_s_879_, 10);
v_elimStack_891_ = lean_ctor_get(v_s_879_, 11);
v_occurs_892_ = lean_ctor_get(v_s_879_, 12);
v_assignment_893_ = lean_ctor_get(v_s_879_, 13);
v_nextCnstrId_894_ = lean_ctor_get(v_s_879_, 14);
v_caseSplits_895_ = lean_ctor_get_uint8(v_s_879_, sizeof(void*)*22);
v_steps_896_ = lean_ctor_get(v_s_879_, 15);
v_penalties_897_ = lean_ctor_get(v_s_879_, 16);
v_numReorderRequests_898_ = lean_ctor_get(v_s_879_, 17);
v_conflict_x3f_899_ = lean_ctor_get(v_s_879_, 18);
v_diseqSplits_900_ = lean_ctor_get(v_s_879_, 19);
v_divMod_901_ = lean_ctor_get(v_s_879_, 20);
v_usedCommRing_902_ = lean_ctor_get_uint8(v_s_879_, sizeof(void*)*22 + 1);
v_nonlinearOccs_903_ = lean_ctor_get(v_s_879_, 21);
v_isSharedCheck_919_ = !lean_is_exclusive(v_s_879_);
if (v_isSharedCheck_919_ == 0)
{
v___x_905_ = v_s_879_;
v_isShared_906_ = v_isSharedCheck_919_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_nonlinearOccs_903_);
lean_inc(v_divMod_901_);
lean_inc(v_diseqSplits_900_);
lean_inc(v_conflict_x3f_899_);
lean_inc(v_numReorderRequests_898_);
lean_inc(v_penalties_897_);
lean_inc(v_steps_896_);
lean_inc(v_nextCnstrId_894_);
lean_inc(v_assignment_893_);
lean_inc(v_occurs_892_);
lean_inc(v_elimStack_891_);
lean_inc(v_active_890_);
lean_inc(v_elimEqs_889_);
lean_inc(v_diseqs_888_);
lean_inc(v_uppers_887_);
lean_inc(v_lowers_886_);
lean_inc(v_dvds_885_);
lean_inc(v_natDef_884_);
lean_inc(v_natToIntMap_883_);
lean_inc(v_varsHistory_882_);
lean_inc(v_varMap_881_);
lean_inc(v_vars_880_);
lean_dec(v_s_879_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_919_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___y_908_; lean_object* v___x_916_; 
v___x_916_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg(v_penalties_897_, v_val_878_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v___x_917_; 
v___x_917_ = lean_unsigned_to_nat(0u);
v___y_908_ = v___x_917_;
goto v___jp_907_;
}
else
{
lean_object* v_val_918_; 
v_val_918_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_val_918_);
lean_dec_ref_known(v___x_916_, 1);
v___y_908_ = v_val_918_;
goto v___jp_907_;
}
v___jp_907_:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_909_ = lean_unsigned_to_nat(1u);
v___x_910_ = lean_nat_add(v___y_908_, v___x_909_);
lean_dec(v___y_908_);
v___x_911_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0___redArg(v_penalties_897_, v_val_878_, v___x_910_);
v___x_912_ = lean_nat_add(v_numReorderRequests_898_, v___x_909_);
lean_dec(v_numReorderRequests_898_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 17, v___x_912_);
lean_ctor_set(v___x_905_, 16, v___x_911_);
v___x_914_ = v___x_905_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_vars_880_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_varMap_881_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_varsHistory_882_);
lean_ctor_set(v_reuseFailAlloc_915_, 3, v_natToIntMap_883_);
lean_ctor_set(v_reuseFailAlloc_915_, 4, v_natDef_884_);
lean_ctor_set(v_reuseFailAlloc_915_, 5, v_dvds_885_);
lean_ctor_set(v_reuseFailAlloc_915_, 6, v_lowers_886_);
lean_ctor_set(v_reuseFailAlloc_915_, 7, v_uppers_887_);
lean_ctor_set(v_reuseFailAlloc_915_, 8, v_diseqs_888_);
lean_ctor_set(v_reuseFailAlloc_915_, 9, v_elimEqs_889_);
lean_ctor_set(v_reuseFailAlloc_915_, 10, v_active_890_);
lean_ctor_set(v_reuseFailAlloc_915_, 11, v_elimStack_891_);
lean_ctor_set(v_reuseFailAlloc_915_, 12, v_occurs_892_);
lean_ctor_set(v_reuseFailAlloc_915_, 13, v_assignment_893_);
lean_ctor_set(v_reuseFailAlloc_915_, 14, v_nextCnstrId_894_);
lean_ctor_set(v_reuseFailAlloc_915_, 15, v_steps_896_);
lean_ctor_set(v_reuseFailAlloc_915_, 16, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_915_, 17, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_915_, 18, v_conflict_x3f_899_);
lean_ctor_set(v_reuseFailAlloc_915_, 19, v_diseqSplits_900_);
lean_ctor_set(v_reuseFailAlloc_915_, 20, v_divMod_901_);
lean_ctor_set(v_reuseFailAlloc_915_, 21, v_nonlinearOccs_903_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*22, v_caseSplits_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*22 + 1, v_usedCommRing_902_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg(lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v___x_923_; lean_object* v_reorderRequest_x3f_924_; 
v___x_923_ = lean_st_ref_get(v_a_920_);
v_reorderRequest_x3f_924_ = lean_ctor_get(v___x_923_, 3);
lean_inc(v_reorderRequest_x3f_924_);
lean_dec(v___x_923_);
if (lean_obj_tag(v_reorderRequest_x3f_924_) == 1)
{
lean_object* v_val_925_; lean_object* v___f_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_val_925_ = lean_ctor_get(v_reorderRequest_x3f_924_, 0);
lean_inc(v_val_925_);
lean_dec_ref_known(v_reorderRequest_x3f_924_, 1);
v___f_926_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg___lam__0), 2, 1);
lean_closure_set(v___f_926_, 0, v_val_925_);
v___x_927_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_928_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_927_, v___f_926_, v_a_921_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_937_; 
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v___x_928_, 0);
lean_dec(v_unused_938_);
v___x_930_ = v___x_928_;
v_isShared_931_ = v_isSharedCheck_937_;
goto v_resetjp_929_;
}
else
{
lean_dec(v___x_928_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_937_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
uint8_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_932_ = 1;
v___x_933_ = lean_box(v___x_932_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_933_);
v___x_935_ = v___x_930_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
v_a_939_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_928_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_928_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
else
{
uint8_t v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec(v_reorderRequest_x3f_924_);
v___x_947_ = 0;
v___x_948_ = lean_box(v___x_947_);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg___boxed(lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg(v_a_950_, v_a_951_);
lean_dec(v_a_951_);
lean_dec(v_a_950_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest(uint8_t v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg(v_a_955_, v_a_956_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___boxed(lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
uint8_t v_a_boxed_981_; lean_object* v_res_982_; 
v_a_boxed_981_ = lean_unbox(v_a_968_);
v_res_982_ = l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest(v_a_boxed_981_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec(v_a_970_);
lean_dec(v_a_969_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0(lean_object* v_00_u03b2_983_, lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_x_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0___redArg(v_x_984_, v_x_985_, v_x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1(lean_object* v_00_u03b2_988_, lean_object* v_x_989_, lean_object* v_x_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg(v_x_989_, v_x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___boxed(lean_object* v_00_u03b2_992_, lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1(v_00_u03b2_992_, v_x_993_, v_x_994_);
lean_dec_ref(v_x_994_);
lean_dec_ref(v_x_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0(lean_object* v_00_u03b2_996_, lean_object* v_x_997_, size_t v_x_998_, size_t v_x_999_, lean_object* v_x_1000_, lean_object* v_x_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(v_x_997_, v_x_998_, v_x_999_, v_x_1000_, v_x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
size_t v_x_5039__boxed_1009_; size_t v_x_5040__boxed_1010_; lean_object* v_res_1011_; 
v_x_5039__boxed_1009_ = lean_unbox_usize(v_x_1005_);
lean_dec(v_x_1005_);
v_x_5040__boxed_1010_ = lean_unbox_usize(v_x_1006_);
lean_dec(v_x_1006_);
v_res_1011_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0(v_00_u03b2_1003_, v_x_1004_, v_x_5039__boxed_1009_, v_x_5040__boxed_1010_, v_x_1007_, v_x_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2(lean_object* v_00_u03b2_1012_, lean_object* v_x_1013_, size_t v_x_1014_, lean_object* v_x_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg(v_x_1013_, v_x_1014_, v_x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1017_, lean_object* v_x_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_){
_start:
{
size_t v_x_5056__boxed_1021_; lean_object* v_res_1022_; 
v_x_5056__boxed_1021_ = lean_unbox_usize(v_x_1019_);
lean_dec(v_x_1019_);
v_res_1022_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2(v_00_u03b2_1017_, v_x_1018_, v_x_5056__boxed_1021_, v_x_1020_);
lean_dec_ref(v_x_1020_);
lean_dec_ref(v_x_1018_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1023_, lean_object* v_n_1024_, lean_object* v_k_1025_, lean_object* v_v_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1___redArg(v_n_1024_, v_k_1025_, v_v_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1028_, size_t v_depth_1029_, lean_object* v_keys_1030_, lean_object* v_vals_1031_, lean_object* v_heq_1032_, lean_object* v_i_1033_, lean_object* v_entries_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg(v_depth_1029_, v_keys_1030_, v_vals_1031_, v_i_1033_, v_entries_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1036_, lean_object* v_depth_1037_, lean_object* v_keys_1038_, lean_object* v_vals_1039_, lean_object* v_heq_1040_, lean_object* v_i_1041_, lean_object* v_entries_1042_){
_start:
{
size_t v_depth_boxed_1043_; lean_object* v_res_1044_; 
v_depth_boxed_1043_ = lean_unbox_usize(v_depth_1037_);
lean_dec(v_depth_1037_);
v_res_1044_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2(v_00_u03b2_1036_, v_depth_boxed_1043_, v_keys_1038_, v_vals_1039_, v_heq_1040_, v_i_1041_, v_entries_1042_);
lean_dec_ref(v_vals_1039_);
lean_dec_ref(v_keys_1038_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1045_, lean_object* v_keys_1046_, lean_object* v_vals_1047_, lean_object* v_heq_1048_, lean_object* v_i_1049_, lean_object* v_k_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg(v_keys_1046_, v_vals_1047_, v_i_1049_, v_k_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1052_, lean_object* v_keys_1053_, lean_object* v_vals_1054_, lean_object* v_heq_1055_, lean_object* v_i_1056_, lean_object* v_k_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5(v_00_u03b2_1052_, v_keys_1053_, v_vals_1054_, v_heq_1055_, v_i_1056_, v_k_1057_);
lean_dec_ref(v_k_1057_);
lean_dec_ref(v_vals_1054_);
lean_dec_ref(v_keys_1053_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1060_, v_x_1061_, v_x_1062_, v_x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___lam__0(lean_object* v_s_1065_){
_start:
{
lean_object* v_vars_1066_; lean_object* v_varMap_1067_; lean_object* v_varsHistory_1068_; lean_object* v_natToIntMap_1069_; lean_object* v_natDef_1070_; lean_object* v_dvds_1071_; lean_object* v_lowers_1072_; lean_object* v_uppers_1073_; lean_object* v_diseqs_1074_; lean_object* v_elimEqs_1075_; lean_object* v_active_1076_; lean_object* v_elimStack_1077_; lean_object* v_occurs_1078_; lean_object* v_assignment_1079_; lean_object* v_nextCnstrId_1080_; lean_object* v_steps_1081_; lean_object* v_penalties_1082_; lean_object* v_numReorderRequests_1083_; lean_object* v_conflict_x3f_1084_; lean_object* v_diseqSplits_1085_; lean_object* v_divMod_1086_; uint8_t v_usedCommRing_1087_; lean_object* v_nonlinearOccs_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1096_; 
v_vars_1066_ = lean_ctor_get(v_s_1065_, 0);
v_varMap_1067_ = lean_ctor_get(v_s_1065_, 1);
v_varsHistory_1068_ = lean_ctor_get(v_s_1065_, 2);
v_natToIntMap_1069_ = lean_ctor_get(v_s_1065_, 3);
v_natDef_1070_ = lean_ctor_get(v_s_1065_, 4);
v_dvds_1071_ = lean_ctor_get(v_s_1065_, 5);
v_lowers_1072_ = lean_ctor_get(v_s_1065_, 6);
v_uppers_1073_ = lean_ctor_get(v_s_1065_, 7);
v_diseqs_1074_ = lean_ctor_get(v_s_1065_, 8);
v_elimEqs_1075_ = lean_ctor_get(v_s_1065_, 9);
v_active_1076_ = lean_ctor_get(v_s_1065_, 10);
v_elimStack_1077_ = lean_ctor_get(v_s_1065_, 11);
v_occurs_1078_ = lean_ctor_get(v_s_1065_, 12);
v_assignment_1079_ = lean_ctor_get(v_s_1065_, 13);
v_nextCnstrId_1080_ = lean_ctor_get(v_s_1065_, 14);
v_steps_1081_ = lean_ctor_get(v_s_1065_, 15);
v_penalties_1082_ = lean_ctor_get(v_s_1065_, 16);
v_numReorderRequests_1083_ = lean_ctor_get(v_s_1065_, 17);
v_conflict_x3f_1084_ = lean_ctor_get(v_s_1065_, 18);
v_diseqSplits_1085_ = lean_ctor_get(v_s_1065_, 19);
v_divMod_1086_ = lean_ctor_get(v_s_1065_, 20);
v_usedCommRing_1087_ = lean_ctor_get_uint8(v_s_1065_, sizeof(void*)*22 + 1);
v_nonlinearOccs_1088_ = lean_ctor_get(v_s_1065_, 21);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_s_1065_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1090_ = v_s_1065_;
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_nonlinearOccs_1088_);
lean_inc(v_divMod_1086_);
lean_inc(v_diseqSplits_1085_);
lean_inc(v_conflict_x3f_1084_);
lean_inc(v_numReorderRequests_1083_);
lean_inc(v_penalties_1082_);
lean_inc(v_steps_1081_);
lean_inc(v_nextCnstrId_1080_);
lean_inc(v_assignment_1079_);
lean_inc(v_occurs_1078_);
lean_inc(v_elimStack_1077_);
lean_inc(v_active_1076_);
lean_inc(v_elimEqs_1075_);
lean_inc(v_diseqs_1074_);
lean_inc(v_uppers_1073_);
lean_inc(v_lowers_1072_);
lean_inc(v_dvds_1071_);
lean_inc(v_natDef_1070_);
lean_inc(v_natToIntMap_1069_);
lean_inc(v_varsHistory_1068_);
lean_inc(v_varMap_1067_);
lean_inc(v_vars_1066_);
lean_dec(v_s_1065_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
uint8_t v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = 1;
if (v_isShared_1091_ == 0)
{
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_vars_1066_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_varMap_1067_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_varsHistory_1068_);
lean_ctor_set(v_reuseFailAlloc_1095_, 3, v_natToIntMap_1069_);
lean_ctor_set(v_reuseFailAlloc_1095_, 4, v_natDef_1070_);
lean_ctor_set(v_reuseFailAlloc_1095_, 5, v_dvds_1071_);
lean_ctor_set(v_reuseFailAlloc_1095_, 6, v_lowers_1072_);
lean_ctor_set(v_reuseFailAlloc_1095_, 7, v_uppers_1073_);
lean_ctor_set(v_reuseFailAlloc_1095_, 8, v_diseqs_1074_);
lean_ctor_set(v_reuseFailAlloc_1095_, 9, v_elimEqs_1075_);
lean_ctor_set(v_reuseFailAlloc_1095_, 10, v_active_1076_);
lean_ctor_set(v_reuseFailAlloc_1095_, 11, v_elimStack_1077_);
lean_ctor_set(v_reuseFailAlloc_1095_, 12, v_occurs_1078_);
lean_ctor_set(v_reuseFailAlloc_1095_, 13, v_assignment_1079_);
lean_ctor_set(v_reuseFailAlloc_1095_, 14, v_nextCnstrId_1080_);
lean_ctor_set(v_reuseFailAlloc_1095_, 15, v_steps_1081_);
lean_ctor_set(v_reuseFailAlloc_1095_, 16, v_penalties_1082_);
lean_ctor_set(v_reuseFailAlloc_1095_, 17, v_numReorderRequests_1083_);
lean_ctor_set(v_reuseFailAlloc_1095_, 18, v_conflict_x3f_1084_);
lean_ctor_set(v_reuseFailAlloc_1095_, 19, v_diseqSplits_1085_);
lean_ctor_set(v_reuseFailAlloc_1095_, 20, v_divMod_1086_);
lean_ctor_set(v_reuseFailAlloc_1095_, 21, v_nonlinearOccs_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1095_, sizeof(void*)*22 + 1, v_usedCommRing_1087_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*22, v___x_1092_);
return v___x_1094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; lean_object* v_ngen_1100_; lean_object* v_namePrefix_1101_; lean_object* v_idx_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1132_; 
v___x_1099_ = lean_st_ref_get(v___y_1097_);
v_ngen_1100_ = lean_ctor_get(v___x_1099_, 2);
lean_inc_ref(v_ngen_1100_);
lean_dec(v___x_1099_);
v_namePrefix_1101_ = lean_ctor_get(v_ngen_1100_, 0);
v_idx_1102_ = lean_ctor_get(v_ngen_1100_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_ngen_1100_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1104_ = v_ngen_1100_;
v_isShared_1105_ = v_isSharedCheck_1132_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_idx_1102_);
lean_inc(v_namePrefix_1101_);
lean_dec(v_ngen_1100_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1132_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v_r_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
lean_inc(v_idx_1102_);
lean_inc(v_namePrefix_1101_);
v_r_1106_ = l_Lean_Name_num___override(v_namePrefix_1101_, v_idx_1102_);
v___x_1107_ = lean_unsigned_to_nat(1u);
v___x_1108_ = lean_nat_add(v_idx_1102_, v___x_1107_);
lean_dec(v_idx_1102_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 1, v___x_1108_);
v___x_1110_ = v___x_1104_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_namePrefix_1101_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; lean_object* v_env_1112_; lean_object* v_nextMacroScope_1113_; lean_object* v_auxDeclNGen_1114_; lean_object* v_traceState_1115_; lean_object* v_cache_1116_; lean_object* v_recordedDeps_1117_; lean_object* v_messages_1118_; lean_object* v_infoState_1119_; lean_object* v_snapshotTasks_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1129_; 
v___x_1111_ = lean_st_ref_take(v___y_1097_);
v_env_1112_ = lean_ctor_get(v___x_1111_, 0);
v_nextMacroScope_1113_ = lean_ctor_get(v___x_1111_, 1);
v_auxDeclNGen_1114_ = lean_ctor_get(v___x_1111_, 3);
v_traceState_1115_ = lean_ctor_get(v___x_1111_, 4);
v_cache_1116_ = lean_ctor_get(v___x_1111_, 5);
v_recordedDeps_1117_ = lean_ctor_get(v___x_1111_, 6);
v_messages_1118_ = lean_ctor_get(v___x_1111_, 7);
v_infoState_1119_ = lean_ctor_get(v___x_1111_, 8);
v_snapshotTasks_1120_ = lean_ctor_get(v___x_1111_, 9);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; 
v_unused_1130_ = lean_ctor_get(v___x_1111_, 2);
lean_dec(v_unused_1130_);
v___x_1122_ = v___x_1111_;
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_snapshotTasks_1120_);
lean_inc(v_infoState_1119_);
lean_inc(v_messages_1118_);
lean_inc(v_recordedDeps_1117_);
lean_inc(v_cache_1116_);
lean_inc(v_traceState_1115_);
lean_inc(v_auxDeclNGen_1114_);
lean_inc(v_nextMacroScope_1113_);
lean_inc(v_env_1112_);
lean_dec(v___x_1111_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 2, v___x_1110_);
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_env_1112_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_nextMacroScope_1113_);
lean_ctor_set(v_reuseFailAlloc_1128_, 2, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1128_, 3, v_auxDeclNGen_1114_);
lean_ctor_set(v_reuseFailAlloc_1128_, 4, v_traceState_1115_);
lean_ctor_set(v_reuseFailAlloc_1128_, 5, v_cache_1116_);
lean_ctor_set(v_reuseFailAlloc_1128_, 6, v_recordedDeps_1117_);
lean_ctor_set(v_reuseFailAlloc_1128_, 7, v_messages_1118_);
lean_ctor_set(v_reuseFailAlloc_1128_, 8, v_infoState_1119_);
lean_ctor_set(v_reuseFailAlloc_1128_, 9, v_snapshotTasks_1120_);
v___x_1125_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_st_ref_put(v___y_1097_, v___x_1125_);
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v_r_1106_);
return v___x_1127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg___boxed(lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_1133_);
lean_dec(v___y_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(uint8_t v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
v___x_1149_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_1147_);
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0___boxed(lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
uint8_t v___y_12318__boxed_1171_; lean_object* v_res_1172_; 
v___y_12318__boxed_1171_ = lean_unbox(v___y_1158_);
v_res_1172_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(v___y_12318__boxed_1171_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec(v___y_1159_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase(lean_object* v_kind_1174_, uint8_t v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___f_1188_; lean_object* v___x_1189_; 
v___f_1188_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0));
v___x_1189_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1191_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1189_, 1);
v___x_1191_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1177_, v_a_1185_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1193_; lean_object* v_cases_1194_; uint8_t v_precise_1195_; lean_object* v_decVars_1196_; lean_object* v_steps_1197_; lean_object* v_reorderRequest_x3f_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1227_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
lean_dec_ref_known(v___x_1191_, 1);
v___x_1193_ = lean_st_ref_take(v_a_1176_);
v_cases_1194_ = lean_ctor_get(v___x_1193_, 0);
v_precise_1195_ = lean_ctor_get_uint8(v___x_1193_, sizeof(void*)*4);
v_decVars_1196_ = lean_ctor_get(v___x_1193_, 1);
v_steps_1197_ = lean_ctor_get(v___x_1193_, 2);
v_reorderRequest_x3f_1198_ = lean_ctor_get(v___x_1193_, 3);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1200_ = v___x_1193_;
v_isShared_1201_ = v_isSharedCheck_1227_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_reorderRequest_x3f_1198_);
lean_inc(v_steps_1197_);
lean_inc(v_decVars_1196_);
lean_inc(v_cases_1194_);
lean_dec(v___x_1193_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1227_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
lean_inc_n(v_a_1190_, 2);
v___x_1202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1202_, 0, v_kind_1174_);
lean_ctor_set(v___x_1202_, 1, v_a_1190_);
lean_ctor_set(v___x_1202_, 2, v_a_1192_);
v___x_1203_ = l_Lean_PersistentArray_push___redArg(v_cases_1194_, v___x_1202_);
v___x_1204_ = l_Lean_FVarIdSet_insert(v_decVars_1196_, v_a_1190_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 1, v___x_1204_);
lean_ctor_set(v___x_1200_, 0, v___x_1203_);
v___x_1206_ = v___x_1200_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_steps_1197_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v_reorderRequest_x3f_1198_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*4, v_precise_1195_);
v___x_1206_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = lean_st_ref_put(v_a_1176_, v___x_1206_);
v___x_1208_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1209_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1208_, v___f_1188_, v_a_1177_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; 
v_unused_1217_ = lean_ctor_get(v___x_1209_, 0);
lean_dec(v_unused_1217_);
v___x_1211_ = v___x_1209_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_dec(v___x_1209_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v_a_1190_);
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1190_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v_a_1190_);
v_a_1218_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1209_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1209_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec(v_a_1190_);
lean_dec_ref(v_kind_1174_);
v_a_1228_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1191_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1191_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
else
{
lean_dec_ref(v_kind_1174_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___boxed(lean_object* v_kind_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
uint8_t v_a_boxed_1250_; lean_object* v_res_1251_; 
v_a_boxed_1250_ = lean_unbox(v_a_1237_);
v_res_1251_ = l_Lean_Meta_Grind_Arith_Cutsat_mkCase(v_kind_1236_, v_a_boxed_1250_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec(v_a_1238_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(uint8_t v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___boxed(lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
uint8_t v___y_12470__boxed_1279_; lean_object* v_res_1280_; 
v___y_12470__boxed_1279_ = lean_unbox(v___y_1266_);
v_res_1280_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(v___y_12470__boxed_1279_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec(v___y_1267_);
return v_res_1280_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase);
l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default();
l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind = _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(builtin);
}
#ifdef __cplusplus
}
#endif
