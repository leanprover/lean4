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
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5);
v___x_54_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; uint8_t v___x_58_; lean_object* v___x_59_; 
v___x_56_ = lean_box(0);
v___x_57_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6);
v___x_58_ = 0;
v___x_59_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_59_, 0, v___x_57_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
lean_ctor_set(v___x_59_, 2, v___x_56_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*3, v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = lean_box(1);
v___x_63_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8));
v___x_64_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7);
v___x_65_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
lean_ctor_set(v___x_65_, 2, v___x_62_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default(void){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind(void){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default;
return v___x_67_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
v___x_69_ = lean_box(0);
v___x_70_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default;
v___x_71_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default;
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___impl(uint8_t v_x_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_box(v_x_74_);
v___x_76_ = lean_obj_tag_nat(v___x_75_);
lean_dec(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___impl___boxed(lean_object* v_x_77_){
_start:
{
uint8_t v_x_4__boxed_78_; lean_object* v_res_79_; 
v_x_4__boxed_78_ = lean_unbox(v_x_77_);
v_res_79_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___impl(v_x_4__boxed_78_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg(lean_object* v_k_80_){
_start:
{
lean_inc(v_k_80_);
return v_k_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg___boxed(lean_object* v_k_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg(v_k_81_);
lean_dec(v_k_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(lean_object* v_motive_83_, lean_object* v_ctorIdx_84_, uint8_t v_t_85_, lean_object* v_h_86_, lean_object* v_k_87_){
_start:
{
lean_inc(v_k_87_);
return v_k_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___boxed(lean_object* v_motive_88_, lean_object* v_ctorIdx_89_, lean_object* v_t_90_, lean_object* v_h_91_, lean_object* v_k_92_){
_start:
{
uint8_t v_t_boxed_93_; lean_object* v_res_94_; 
v_t_boxed_93_ = lean_unbox(v_t_90_);
v_res_94_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(v_motive_88_, v_ctorIdx_89_, v_t_boxed_93_, v_h_91_, v_k_92_);
lean_dec(v_k_92_);
lean_dec(v_ctorIdx_89_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(lean_object* v_rat_95_){
_start:
{
lean_inc(v_rat_95_);
return v_rat_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg___boxed(lean_object* v_rat_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(v_rat_96_);
lean_dec(v_rat_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(lean_object* v_motive_98_, uint8_t v_t_99_, lean_object* v_h_100_, lean_object* v_rat_101_){
_start:
{
lean_inc(v_rat_101_);
return v_rat_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___boxed(lean_object* v_motive_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_rat_105_){
_start:
{
uint8_t v_t_boxed_106_; lean_object* v_res_107_; 
v_t_boxed_106_ = lean_unbox(v_t_103_);
v_res_107_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(v_motive_102_, v_t_boxed_106_, v_h_104_, v_rat_105_);
lean_dec(v_rat_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(lean_object* v_int_108_){
_start:
{
lean_inc(v_int_108_);
return v_int_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg___boxed(lean_object* v_int_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(v_int_109_);
lean_dec(v_int_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(lean_object* v_motive_111_, uint8_t v_t_112_, lean_object* v_h_113_, lean_object* v_int_114_){
_start:
{
lean_inc(v_int_114_);
return v_int_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___boxed(lean_object* v_motive_115_, lean_object* v_t_116_, lean_object* v_h_117_, lean_object* v_int_118_){
_start:
{
uint8_t v_t_boxed_119_; lean_object* v_res_120_; 
v_t_boxed_119_ = lean_unbox(v_t_116_);
v_res_120_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(v_motive_115_, v_t_boxed_119_, v_h_117_, v_int_118_);
lean_dec(v_int_118_);
return v_res_120_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default(void){
_start:
{
uint8_t v___x_121_; 
v___x_121_ = 0;
return v___x_121_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind(void){
_start:
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(uint8_t v_x_123_, uint8_t v_y_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_125_ = lean_box(v_x_123_);
v___x_126_ = lean_obj_tag_nat(v___x_125_);
lean_dec(v___x_125_);
v___x_127_ = lean_box(v_y_124_);
v___x_128_ = lean_obj_tag_nat(v___x_127_);
lean_dec(v___x_127_);
v___x_129_ = lean_nat_dec_eq(v___x_126_, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq___boxed(lean_object* v_x_130_, lean_object* v_y_131_){
_start:
{
uint8_t v_x_24__boxed_132_; uint8_t v_y_25__boxed_133_; uint8_t v_res_134_; lean_object* v_r_135_; 
v_x_24__boxed_132_ = lean_unbox(v_x_130_);
v_y_25__boxed_133_ = lean_unbox(v_y_131_);
v_res_134_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(v_x_24__boxed_132_, v_y_25__boxed_133_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(uint8_t v_a_138_){
_start:
{
uint8_t v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_140_ = 0;
v___x_141_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(v_a_138_, v___x_140_);
v___x_142_ = lean_box(v___x_141_);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg___boxed(lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
uint8_t v_a_boxed_146_; lean_object* v_res_147_; 
v_a_boxed_146_ = lean_unbox(v_a_144_);
v_res_147_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(v_a_boxed_146_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox(uint8_t v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(v_a_148_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___boxed(lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
uint8_t v_a_boxed_175_; lean_object* v_res_176_; 
v_a_boxed_175_ = lean_unbox(v_a_162_);
v_res_176_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox(v_a_boxed_175_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec(v_a_164_);
lean_dec(v_a_163_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(lean_object* v_a_177_){
_start:
{
lean_object* v___x_179_; lean_object* v_cases_180_; lean_object* v_decVars_181_; lean_object* v_steps_182_; lean_object* v_reorderRequest_x3f_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_194_; 
v___x_179_ = lean_st_ref_take(v_a_177_);
v_cases_180_ = lean_ctor_get(v___x_179_, 0);
v_decVars_181_ = lean_ctor_get(v___x_179_, 1);
v_steps_182_ = lean_ctor_get(v___x_179_, 2);
v_reorderRequest_x3f_183_ = lean_ctor_get(v___x_179_, 3);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_194_ == 0)
{
v___x_185_ = v___x_179_;
v_isShared_186_ = v_isSharedCheck_194_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_reorderRequest_x3f_183_);
lean_inc(v_steps_182_);
lean_inc(v_decVars_181_);
lean_inc(v_cases_180_);
lean_dec(v___x_179_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_194_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; uint8_t v___x_188_; lean_object* v___x_190_; 
v___x_187_ = lean_box(0);
v___x_188_ = 0;
if (v_isShared_186_ == 0)
{
v___x_190_ = v___x_185_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_cases_180_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_decVars_181_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v_steps_182_);
lean_ctor_set(v_reuseFailAlloc_193_, 3, v_reorderRequest_x3f_183_);
v___x_190_ = v_reuseFailAlloc_193_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*4, v___x_188_);
v___x_191_ = lean_st_ref_put(v_a_177_, v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_187_);
return v___x_192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg___boxed(lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(v_a_195_);
lean_dec(v_a_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(uint8_t v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(v_a_199_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___boxed(lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
uint8_t v_a_boxed_225_; lean_object* v_res_226_; 
v_a_boxed_225_ = lean_unbox(v_a_212_);
v_res_226_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(v_a_boxed_225_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec(v_a_214_);
lean_dec(v_a_213_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v___x_232_; lean_object* v_cases_233_; uint8_t v_precise_234_; lean_object* v_decVars_235_; lean_object* v_steps_236_; lean_object* v_reorderRequest_x3f_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_281_; 
v___x_232_ = lean_st_ref_take(v_a_227_);
v_cases_233_ = lean_ctor_get(v___x_232_, 0);
v_precise_234_ = lean_ctor_get_uint8(v___x_232_, sizeof(void*)*4);
v_decVars_235_ = lean_ctor_get(v___x_232_, 1);
v_steps_236_ = lean_ctor_get(v___x_232_, 2);
v_reorderRequest_x3f_237_ = lean_ctor_get(v___x_232_, 3);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_281_ == 0)
{
v___x_239_ = v___x_232_;
v_isShared_240_ = v_isSharedCheck_281_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_reorderRequest_x3f_237_);
lean_inc(v_steps_236_);
lean_inc(v_decVars_235_);
lean_inc(v_cases_233_);
lean_dec(v___x_232_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_281_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_add(v_steps_236_, v___x_241_);
lean_dec(v_steps_236_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 2, v___x_242_);
v___x_244_ = v___x_239_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_cases_233_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_decVars_235_);
lean_ctor_set(v_reuseFailAlloc_280_, 2, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_280_, 3, v_reorderRequest_x3f_237_);
lean_ctor_set_uint8(v_reuseFailAlloc_280_, sizeof(void*)*4, v_precise_234_);
v___x_244_ = v_reuseFailAlloc_280_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_st_ref_put(v_a_227_, v___x_244_);
v___x_246_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_228_, v_a_230_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_247_);
lean_dec_ref_known(v___x_246_, 1);
v___x_248_ = lean_st_ref_get(v_a_227_);
v___x_249_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_229_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_263_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_263_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_263_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_263_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v_liaSteps_254_; lean_object* v_steps_255_; lean_object* v_steps_256_; lean_object* v___x_257_; uint8_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v_liaSteps_254_ = lean_ctor_get(v_a_250_, 9);
lean_inc(v_liaSteps_254_);
lean_dec(v_a_250_);
v_steps_255_ = lean_ctor_get(v_a_247_, 14);
lean_inc(v_steps_255_);
lean_dec(v_a_247_);
v_steps_256_ = lean_ctor_get(v___x_248_, 2);
lean_inc(v_steps_256_);
lean_dec(v___x_248_);
v___x_257_ = lean_nat_add(v_steps_255_, v_steps_256_);
lean_dec(v_steps_256_);
lean_dec(v_steps_255_);
v___x_258_ = lean_nat_dec_lt(v_liaSteps_254_, v___x_257_);
lean_dec(v___x_257_);
lean_dec(v_liaSteps_254_);
v___x_259_ = lean_box(v___x_258_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_259_);
v___x_261_ = v___x_252_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec(v___x_248_);
lean_dec(v_a_247_);
v_a_264_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_249_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_249_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
v_a_272_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_246_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_246_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg___boxed(lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec_ref(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec(v_a_282_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps(uint8_t v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(v_a_289_, v_a_290_, v_a_292_, v_a_298_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___boxed(lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
uint8_t v_a_boxed_315_; lean_object* v_res_316_; 
v_a_boxed_315_ = lean_unbox(v_a_302_);
v_res_316_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps(v_a_boxed_315_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec(v_a_304_);
lean_dec(v_a_303_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0(lean_object* v_steps_317_, lean_object* v_s_318_){
_start:
{
lean_object* v_vars_319_; lean_object* v_varMap_320_; lean_object* v_varsHistory_321_; lean_object* v_natToIntMap_322_; lean_object* v_natDef_323_; lean_object* v_dvds_324_; lean_object* v_lowers_325_; lean_object* v_uppers_326_; lean_object* v_diseqs_327_; lean_object* v_elimEqs_328_; lean_object* v_elimStack_329_; lean_object* v_occurs_330_; lean_object* v_assignment_331_; lean_object* v_nextCnstrId_332_; uint8_t v_caseSplits_333_; lean_object* v_steps_334_; lean_object* v_penalties_335_; lean_object* v_numReorderRequests_336_; lean_object* v_conflict_x3f_337_; lean_object* v_diseqSplits_338_; lean_object* v_divMod_339_; uint8_t v_usedCommRing_340_; lean_object* v_nonlinearOccs_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_349_; 
v_vars_319_ = lean_ctor_get(v_s_318_, 0);
v_varMap_320_ = lean_ctor_get(v_s_318_, 1);
v_varsHistory_321_ = lean_ctor_get(v_s_318_, 2);
v_natToIntMap_322_ = lean_ctor_get(v_s_318_, 3);
v_natDef_323_ = lean_ctor_get(v_s_318_, 4);
v_dvds_324_ = lean_ctor_get(v_s_318_, 5);
v_lowers_325_ = lean_ctor_get(v_s_318_, 6);
v_uppers_326_ = lean_ctor_get(v_s_318_, 7);
v_diseqs_327_ = lean_ctor_get(v_s_318_, 8);
v_elimEqs_328_ = lean_ctor_get(v_s_318_, 9);
v_elimStack_329_ = lean_ctor_get(v_s_318_, 10);
v_occurs_330_ = lean_ctor_get(v_s_318_, 11);
v_assignment_331_ = lean_ctor_get(v_s_318_, 12);
v_nextCnstrId_332_ = lean_ctor_get(v_s_318_, 13);
v_caseSplits_333_ = lean_ctor_get_uint8(v_s_318_, sizeof(void*)*21);
v_steps_334_ = lean_ctor_get(v_s_318_, 14);
v_penalties_335_ = lean_ctor_get(v_s_318_, 15);
v_numReorderRequests_336_ = lean_ctor_get(v_s_318_, 16);
v_conflict_x3f_337_ = lean_ctor_get(v_s_318_, 17);
v_diseqSplits_338_ = lean_ctor_get(v_s_318_, 18);
v_divMod_339_ = lean_ctor_get(v_s_318_, 19);
v_usedCommRing_340_ = lean_ctor_get_uint8(v_s_318_, sizeof(void*)*21 + 1);
v_nonlinearOccs_341_ = lean_ctor_get(v_s_318_, 20);
v_isSharedCheck_349_ = !lean_is_exclusive(v_s_318_);
if (v_isSharedCheck_349_ == 0)
{
v___x_343_ = v_s_318_;
v_isShared_344_ = v_isSharedCheck_349_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_nonlinearOccs_341_);
lean_inc(v_divMod_339_);
lean_inc(v_diseqSplits_338_);
lean_inc(v_conflict_x3f_337_);
lean_inc(v_numReorderRequests_336_);
lean_inc(v_penalties_335_);
lean_inc(v_steps_334_);
lean_inc(v_nextCnstrId_332_);
lean_inc(v_assignment_331_);
lean_inc(v_occurs_330_);
lean_inc(v_elimStack_329_);
lean_inc(v_elimEqs_328_);
lean_inc(v_diseqs_327_);
lean_inc(v_uppers_326_);
lean_inc(v_lowers_325_);
lean_inc(v_dvds_324_);
lean_inc(v_natDef_323_);
lean_inc(v_natToIntMap_322_);
lean_inc(v_varsHistory_321_);
lean_inc(v_varMap_320_);
lean_inc(v_vars_319_);
lean_dec(v_s_318_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_349_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_345_ = lean_nat_add(v_steps_334_, v_steps_317_);
lean_dec(v_steps_334_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 14, v___x_345_);
v___x_347_ = v___x_343_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_vars_319_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_varMap_320_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v_varsHistory_321_);
lean_ctor_set(v_reuseFailAlloc_348_, 3, v_natToIntMap_322_);
lean_ctor_set(v_reuseFailAlloc_348_, 4, v_natDef_323_);
lean_ctor_set(v_reuseFailAlloc_348_, 5, v_dvds_324_);
lean_ctor_set(v_reuseFailAlloc_348_, 6, v_lowers_325_);
lean_ctor_set(v_reuseFailAlloc_348_, 7, v_uppers_326_);
lean_ctor_set(v_reuseFailAlloc_348_, 8, v_diseqs_327_);
lean_ctor_set(v_reuseFailAlloc_348_, 9, v_elimEqs_328_);
lean_ctor_set(v_reuseFailAlloc_348_, 10, v_elimStack_329_);
lean_ctor_set(v_reuseFailAlloc_348_, 11, v_occurs_330_);
lean_ctor_set(v_reuseFailAlloc_348_, 12, v_assignment_331_);
lean_ctor_set(v_reuseFailAlloc_348_, 13, v_nextCnstrId_332_);
lean_ctor_set(v_reuseFailAlloc_348_, 14, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_348_, 15, v_penalties_335_);
lean_ctor_set(v_reuseFailAlloc_348_, 16, v_numReorderRequests_336_);
lean_ctor_set(v_reuseFailAlloc_348_, 17, v_conflict_x3f_337_);
lean_ctor_set(v_reuseFailAlloc_348_, 18, v_diseqSplits_338_);
lean_ctor_set(v_reuseFailAlloc_348_, 19, v_divMod_339_);
lean_ctor_set(v_reuseFailAlloc_348_, 20, v_nonlinearOccs_341_);
lean_ctor_set_uint8(v_reuseFailAlloc_348_, sizeof(void*)*21, v_caseSplits_333_);
lean_ctor_set_uint8(v_reuseFailAlloc_348_, sizeof(void*)*21 + 1, v_usedCommRing_340_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0___boxed(lean_object* v_steps_350_, lean_object* v_s_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0(v_steps_350_, v_s_351_);
lean_dec(v_steps_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___x_356_; lean_object* v_steps_357_; lean_object* v___f_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_356_ = lean_st_ref_get(v_a_353_);
v_steps_357_ = lean_ctor_get(v___x_356_, 2);
lean_inc(v_steps_357_);
lean_dec(v___x_356_);
v___f_358_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_358_, 0, v_steps_357_);
v___x_359_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_360_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_359_, v___f_358_, v_a_354_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___boxed(lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(v_a_361_, v_a_362_);
lean_dec(v_a_362_);
lean_dec(v_a_361_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps(uint8_t v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(v_a_366_, v_a_367_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___boxed(lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
uint8_t v_a_boxed_392_; lean_object* v_res_393_; 
v_a_boxed_392_ = lean_unbox(v_a_379_);
v_res_393_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps(v_a_boxed_392_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec(v_a_381_);
lean_dec(v_a_380_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0_spec__0(lean_object* v_msgData_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___x_400_; lean_object* v_env_401_; uint8_t v___x_402_; lean_object* v_env_403_; lean_object* v___x_404_; lean_object* v_toCold_405_; lean_object* v_mctx_406_; lean_object* v_lctx_407_; lean_object* v_options_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_400_ = lean_st_ref_get(v___y_398_);
v_env_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc_ref(v_env_401_);
lean_dec(v___x_400_);
v___x_402_ = 0;
v_env_403_ = l_Lean_Environment_setRecordingDeps(v_env_401_, v___x_402_);
v___x_404_ = lean_st_ref_get(v___y_396_);
v_toCold_405_ = lean_ctor_get(v___y_397_, 0);
v_mctx_406_ = lean_ctor_get(v___x_404_, 0);
lean_inc_ref(v_mctx_406_);
lean_dec(v___x_404_);
v_lctx_407_ = lean_ctor_get(v___y_395_, 2);
v_options_408_ = lean_ctor_get(v_toCold_405_, 2);
lean_inc_ref(v_options_408_);
lean_inc_ref(v_lctx_407_);
v___x_409_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_409_, 0, v_env_403_);
lean_ctor_set(v___x_409_, 1, v_mctx_406_);
lean_ctor_set(v___x_409_, 2, v_lctx_407_);
lean_ctor_set(v___x_409_, 3, v_options_408_);
v___x_410_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v_msgData_394_);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0_spec__0___boxed(lean_object* v_msgData_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0_spec__0(v_msgData_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
return v_res_418_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_419_; double v___x_420_; 
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_float_of_nat(v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg(lean_object* v_cls_424_, lean_object* v_msg_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_ref_431_; lean_object* v___x_432_; lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_478_; 
v_ref_431_ = lean_ctor_get(v___y_428_, 2);
v___x_432_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0_spec__0(v_msg_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_478_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_478_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_478_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v_traceState_438_; lean_object* v_env_439_; lean_object* v_nextMacroScope_440_; lean_object* v_ngen_441_; lean_object* v_auxDeclNGen_442_; lean_object* v_cache_443_; lean_object* v_recordedDeps_444_; lean_object* v_messages_445_; lean_object* v_infoState_446_; lean_object* v_snapshotTasks_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_477_; 
v___x_437_ = lean_st_ref_take(v___y_429_);
v_traceState_438_ = lean_ctor_get(v___x_437_, 4);
v_env_439_ = lean_ctor_get(v___x_437_, 0);
v_nextMacroScope_440_ = lean_ctor_get(v___x_437_, 1);
v_ngen_441_ = lean_ctor_get(v___x_437_, 2);
v_auxDeclNGen_442_ = lean_ctor_get(v___x_437_, 3);
v_cache_443_ = lean_ctor_get(v___x_437_, 5);
v_recordedDeps_444_ = lean_ctor_get(v___x_437_, 6);
v_messages_445_ = lean_ctor_get(v___x_437_, 7);
v_infoState_446_ = lean_ctor_get(v___x_437_, 8);
v_snapshotTasks_447_ = lean_ctor_get(v___x_437_, 9);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_477_ == 0)
{
v___x_449_ = v___x_437_;
v_isShared_450_ = v_isSharedCheck_477_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_snapshotTasks_447_);
lean_inc(v_infoState_446_);
lean_inc(v_messages_445_);
lean_inc(v_recordedDeps_444_);
lean_inc(v_cache_443_);
lean_inc(v_traceState_438_);
lean_inc(v_auxDeclNGen_442_);
lean_inc(v_ngen_441_);
lean_inc(v_nextMacroScope_440_);
lean_inc(v_env_439_);
lean_dec(v___x_437_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_477_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
uint64_t v_tid_451_; lean_object* v_traces_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_476_; 
v_tid_451_ = lean_ctor_get_uint64(v_traceState_438_, sizeof(void*)*1);
v_traces_452_ = lean_ctor_get(v_traceState_438_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v_traceState_438_);
if (v_isSharedCheck_476_ == 0)
{
v___x_454_ = v_traceState_438_;
v_isShared_455_ = v_isSharedCheck_476_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_traces_452_);
lean_dec(v_traceState_438_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_476_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_457_; double v___x_458_; uint8_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_456_ = lean_box(0);
v___x_457_ = lean_box(0);
v___x_458_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__0);
v___x_459_ = 0;
v___x_460_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__1));
v___x_461_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_461_, 0, v_cls_424_);
lean_ctor_set(v___x_461_, 1, v___x_457_);
lean_ctor_set(v___x_461_, 2, v___x_460_);
lean_ctor_set_float(v___x_461_, sizeof(void*)*3, v___x_458_);
lean_ctor_set_float(v___x_461_, sizeof(void*)*3 + 8, v___x_458_);
lean_ctor_set_uint8(v___x_461_, sizeof(void*)*3 + 16, v___x_459_);
v___x_462_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__2));
v___x_463_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v_a_433_);
lean_ctor_set(v___x_463_, 2, v___x_462_);
lean_inc(v_ref_431_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v_ref_431_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = l_Lean_PersistentArray_push___redArg(v_traces_452_, v___x_464_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_465_);
v___x_467_ = v___x_454_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_465_);
lean_ctor_set_uint64(v_reuseFailAlloc_475_, sizeof(void*)*1, v_tid_451_);
v___x_467_ = v_reuseFailAlloc_475_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_469_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 4, v___x_467_);
v___x_469_ = v___x_449_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_env_439_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_nextMacroScope_440_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_ngen_441_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_auxDeclNGen_442_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_474_, 5, v_cache_443_);
lean_ctor_set(v_reuseFailAlloc_474_, 6, v_recordedDeps_444_);
lean_ctor_set(v_reuseFailAlloc_474_, 7, v_messages_445_);
lean_ctor_set(v_reuseFailAlloc_474_, 8, v_infoState_446_);
lean_ctor_set(v_reuseFailAlloc_474_, 9, v_snapshotTasks_447_);
v___x_469_ = v_reuseFailAlloc_474_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = lean_st_ref_put(v___y_429_, v___x_469_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_456_);
v___x_472_ = v___x_435_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_456_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___boxed(lean_object* v_cls_479_, lean_object* v_msg_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg(v_cls_479_, v_msg_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
return v_res_486_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__7(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__4));
v___x_500_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__6));
v___x_501_ = l_Lean_Name_append(v___x_500_, v___x_499_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__9(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__8));
v___x_504_ = l_Lean_stringToMessageData(v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder(lean_object* v_x_505_, uint8_t v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_508_, v_a_516_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_510_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_589_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_589_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_589_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_589_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_liaReorders_526_; lean_object* v_numReorderRequests_527_; uint8_t v___x_528_; 
v_liaReorders_526_ = lean_ctor_get(v_a_522_, 10);
lean_inc(v_liaReorders_526_);
lean_dec(v_a_522_);
v_numReorderRequests_527_ = lean_ctor_get(v_a_520_, 16);
lean_inc(v_numReorderRequests_527_);
lean_dec(v_a_520_);
v___x_528_ = lean_nat_dec_le(v_liaReorders_526_, v_numReorderRequests_527_);
lean_dec(v_numReorderRequests_527_);
lean_dec(v_liaReorders_526_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
lean_del_object(v___x_524_);
v___x_529_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_505_, v_a_508_, v_a_516_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_575_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_575_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_575_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_575_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___y_535_; lean_object* v_toCold_556_; lean_object* v_options_557_; uint8_t v_hasTrace_558_; 
v_toCold_556_ = lean_ctor_get(v_a_516_, 0);
v_options_557_ = lean_ctor_get(v_toCold_556_, 2);
v_hasTrace_558_ = lean_ctor_get_uint8(v_options_557_, sizeof(void*)*1);
if (v_hasTrace_558_ == 0)
{
v___y_535_ = v_a_507_;
goto v___jp_534_;
}
else
{
lean_object* v_inheritedTraceOptions_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v_inheritedTraceOptions_559_ = lean_ctor_get(v_toCold_556_, 11);
v___x_560_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__4));
v___x_561_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__7);
v___x_562_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_559_, v_options_557_, v___x_561_);
if (v___x_562_ == 0)
{
v___y_535_ = v_a_507_;
goto v___jp_534_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_563_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__9);
lean_inc(v_a_530_);
v___x_564_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_530_);
v___x_565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg(v___x_560_, v___x_565_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_dec_ref_known(v___x_566_, 1);
v___y_535_ = v_a_507_;
goto v___jp_534_;
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_del_object(v___x_532_);
lean_dec(v_a_530_);
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
v___jp_534_:
{
lean_object* v___x_536_; lean_object* v_cases_537_; uint8_t v_precise_538_; lean_object* v_decVars_539_; lean_object* v_steps_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_554_; 
v___x_536_ = lean_st_ref_take(v___y_535_);
v_cases_537_ = lean_ctor_get(v___x_536_, 0);
v_precise_538_ = lean_ctor_get_uint8(v___x_536_, sizeof(void*)*4);
v_decVars_539_ = lean_ctor_get(v___x_536_, 1);
v_steps_540_ = lean_ctor_get(v___x_536_, 2);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v___x_536_, 3);
lean_dec(v_unused_555_);
v___x_542_ = v___x_536_;
v_isShared_543_ = v_isSharedCheck_554_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_steps_540_);
lean_inc(v_decVars_539_);
lean_inc(v_cases_537_);
lean_dec(v___x_536_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_554_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v_a_530_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 3, v___x_544_);
v___x_546_ = v___x_542_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_cases_537_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_decVars_539_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_steps_540_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v___x_544_);
lean_ctor_set_uint8(v_reuseFailAlloc_553_, sizeof(void*)*4, v_precise_538_);
v___x_546_ = v_reuseFailAlloc_553_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_547_ = lean_st_ref_put(v___y_535_, v___x_546_);
v___x_548_ = 1;
v___x_549_ = lean_box(v___x_548_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_549_);
v___x_551_ = v___x_532_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
v_a_576_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_529_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_529_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
else
{
uint8_t v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_584_ = 0;
v___x_585_ = lean_box(v___x_584_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_585_);
v___x_587_ = v___x_524_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec(v_a_520_);
v_a_590_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_521_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_521_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
v_a_598_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_519_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_519_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___boxed(lean_object* v_x_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
uint8_t v_a_boxed_620_; lean_object* v_res_621_; 
v_a_boxed_620_ = lean_unbox(v_a_607_);
v_res_621_ = l_Lean_Meta_Grind_Arith_Cutsat_requestReorder(v_x_606_, v_a_boxed_620_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
lean_dec(v_a_609_);
lean_dec(v_a_608_);
lean_dec(v_x_606_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0(lean_object* v_cls_622_, lean_object* v_msg_623_, uint8_t v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg(v_cls_622_, v_msg_623_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___boxed(lean_object* v_cls_638_, lean_object* v_msg_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
uint8_t v___y_24222__boxed_653_; lean_object* v_res_654_; 
v___y_24222__boxed_653_ = lean_unbox(v___y_640_);
v_res_654_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0(v_cls_638_, v_msg_639_, v___y_24222__boxed_653_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec(v___y_642_);
lean_dec(v___y_641_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_655_, lean_object* v_vals_656_, lean_object* v_i_657_, lean_object* v_k_658_){
_start:
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = lean_array_get_size(v_keys_655_);
v___x_660_ = lean_nat_dec_lt(v_i_657_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
lean_dec(v_i_657_);
v___x_661_ = lean_box(0);
return v___x_661_;
}
else
{
lean_object* v_k_x27_662_; size_t v___x_663_; size_t v___x_664_; uint8_t v___x_665_; 
v_k_x27_662_ = lean_array_fget_borrowed(v_keys_655_, v_i_657_);
v___x_663_ = lean_ptr_addr(v_k_658_);
v___x_664_ = lean_ptr_addr(v_k_x27_662_);
v___x_665_ = lean_usize_dec_eq(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = lean_nat_add(v_i_657_, v___x_666_);
lean_dec(v_i_657_);
v_i_657_ = v___x_667_;
goto _start;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_array_fget_borrowed(v_vals_656_, v_i_657_);
lean_dec(v_i_657_);
lean_inc(v___x_669_);
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_671_, lean_object* v_vals_672_, lean_object* v_i_673_, lean_object* v_k_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg(v_keys_671_, v_vals_672_, v_i_673_, v_k_674_);
lean_dec_ref(v_k_674_);
lean_dec_ref(v_vals_672_);
lean_dec_ref(v_keys_671_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg(lean_object* v_x_676_, size_t v_x_677_, lean_object* v_x_678_){
_start:
{
if (lean_obj_tag(v_x_676_) == 0)
{
lean_object* v_es_679_; lean_object* v___x_680_; size_t v___x_681_; size_t v___x_682_; lean_object* v_j_683_; lean_object* v___x_684_; 
v_es_679_ = lean_ctor_get(v_x_676_, 0);
v___x_680_ = lean_box(2);
v___x_681_ = ((size_t)31ULL);
v___x_682_ = lean_usize_land(v_x_677_, v___x_681_);
v_j_683_ = lean_usize_to_nat(v___x_682_);
v___x_684_ = lean_array_get_borrowed(v___x_680_, v_es_679_, v_j_683_);
lean_dec(v_j_683_);
switch(lean_obj_tag(v___x_684_))
{
case 0:
{
lean_object* v_key_685_; lean_object* v_val_686_; size_t v___x_687_; size_t v___x_688_; uint8_t v___x_689_; 
v_key_685_ = lean_ctor_get(v___x_684_, 0);
v_val_686_ = lean_ctor_get(v___x_684_, 1);
v___x_687_ = lean_ptr_addr(v_x_678_);
v___x_688_ = lean_ptr_addr(v_key_685_);
v___x_689_ = lean_usize_dec_eq(v___x_687_, v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; 
v___x_690_ = lean_box(0);
return v___x_690_;
}
else
{
lean_object* v___x_691_; 
lean_inc(v_val_686_);
v___x_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_691_, 0, v_val_686_);
return v___x_691_;
}
}
case 1:
{
lean_object* v_node_692_; size_t v___x_693_; size_t v___x_694_; 
v_node_692_ = lean_ctor_get(v___x_684_, 0);
v___x_693_ = ((size_t)5ULL);
v___x_694_ = lean_usize_shift_right(v_x_677_, v___x_693_);
v_x_676_ = v_node_692_;
v_x_677_ = v___x_694_;
goto _start;
}
default: 
{
lean_object* v___x_696_; 
v___x_696_ = lean_box(0);
return v___x_696_;
}
}
}
else
{
lean_object* v_ks_697_; lean_object* v_vs_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_ks_697_ = lean_ctor_get(v_x_676_, 0);
v_vs_698_ = lean_ctor_get(v_x_676_, 1);
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg(v_ks_697_, v_vs_698_, v___x_699_, v_x_678_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg___boxed(lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_x_703_){
_start:
{
size_t v_x_4570__boxed_704_; lean_object* v_res_705_; 
v_x_4570__boxed_704_ = lean_unbox_usize(v_x_702_);
lean_dec(v_x_702_);
v_res_705_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg(v_x_701_, v_x_4570__boxed_704_, v_x_703_);
lean_dec_ref(v_x_703_);
lean_dec_ref(v_x_701_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg(lean_object* v_x_706_, lean_object* v_x_707_){
_start:
{
size_t v___x_708_; size_t v___x_709_; size_t v___x_710_; uint64_t v___x_711_; size_t v___x_712_; lean_object* v___x_713_; 
v___x_708_ = lean_ptr_addr(v_x_707_);
v___x_709_ = ((size_t)3ULL);
v___x_710_ = lean_usize_shift_right(v___x_708_, v___x_709_);
v___x_711_ = lean_usize_to_uint64(v___x_710_);
v___x_712_ = lean_uint64_to_usize(v___x_711_);
v___x_713_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg(v_x_706_, v___x_712_, v_x_707_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg___boxed(lean_object* v_x_714_, lean_object* v_x_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg(v_x_714_, v_x_715_);
lean_dec_ref(v_x_715_);
lean_dec_ref(v_x_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_x_719_, lean_object* v_x_720_){
_start:
{
lean_object* v_ks_721_; lean_object* v_vs_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_748_; 
v_ks_721_ = lean_ctor_get(v_x_717_, 0);
v_vs_722_ = lean_ctor_get(v_x_717_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v_x_717_);
if (v_isSharedCheck_748_ == 0)
{
v___x_724_ = v_x_717_;
v_isShared_725_ = v_isSharedCheck_748_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_vs_722_);
lean_inc(v_ks_721_);
lean_dec(v_x_717_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_748_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = lean_array_get_size(v_ks_721_);
v___x_727_ = lean_nat_dec_lt(v_x_718_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
lean_dec(v_x_718_);
v___x_728_ = lean_array_push(v_ks_721_, v_x_719_);
v___x_729_ = lean_array_push(v_vs_722_, v_x_720_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 1, v___x_729_);
lean_ctor_set(v___x_724_, 0, v___x_728_);
v___x_731_ = v___x_724_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
else
{
lean_object* v_k_x27_733_; size_t v___x_734_; size_t v___x_735_; uint8_t v___x_736_; 
v_k_x27_733_ = lean_array_fget_borrowed(v_ks_721_, v_x_718_);
v___x_734_ = lean_ptr_addr(v_x_719_);
v___x_735_ = lean_ptr_addr(v_k_x27_733_);
v___x_736_ = lean_usize_dec_eq(v___x_734_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_738_; 
if (v_isShared_725_ == 0)
{
v___x_738_ = v___x_724_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_ks_721_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_vs_722_);
v___x_738_ = v_reuseFailAlloc_742_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = lean_nat_add(v_x_718_, v___x_739_);
lean_dec(v_x_718_);
v_x_717_ = v___x_738_;
v_x_718_ = v___x_740_;
goto _start;
}
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_743_ = lean_array_fset(v_ks_721_, v_x_718_, v_x_719_);
v___x_744_ = lean_array_fset(v_vs_722_, v_x_718_, v_x_720_);
lean_dec(v_x_718_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 1, v___x_744_);
lean_ctor_set(v___x_724_, 0, v___x_743_);
v___x_746_ = v___x_724_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v___x_744_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1___redArg(lean_object* v_n_749_, lean_object* v_k_750_, lean_object* v_v_751_){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1_spec__3___redArg(v_n_749_, v___x_752_, v_k_750_, v_v_751_);
return v___x_753_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(lean_object* v_x_755_, size_t v_x_756_, size_t v_x_757_, lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
if (lean_obj_tag(v_x_755_) == 0)
{
lean_object* v_es_760_; size_t v___x_761_; size_t v___x_762_; lean_object* v_j_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v_es_760_ = lean_ctor_get(v_x_755_, 0);
v___x_761_ = ((size_t)31ULL);
v___x_762_ = lean_usize_land(v_x_756_, v___x_761_);
v_j_763_ = lean_usize_to_nat(v___x_762_);
v___x_764_ = lean_array_get_size(v_es_760_);
v___x_765_ = lean_nat_dec_lt(v_j_763_, v___x_764_);
if (v___x_765_ == 0)
{
lean_dec(v_j_763_);
lean_dec(v_x_759_);
lean_dec_ref(v_x_758_);
return v_x_755_;
}
else
{
lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_806_; 
lean_inc_ref(v_es_760_);
v_isSharedCheck_806_ = !lean_is_exclusive(v_x_755_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; 
v_unused_807_ = lean_ctor_get(v_x_755_, 0);
lean_dec(v_unused_807_);
v___x_767_ = v_x_755_;
v_isShared_768_ = v_isSharedCheck_806_;
goto v_resetjp_766_;
}
else
{
lean_dec(v_x_755_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_806_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v_v_769_; lean_object* v___x_770_; lean_object* v_xs_x27_771_; lean_object* v___y_773_; 
v_v_769_ = lean_array_fget(v_es_760_, v_j_763_);
v___x_770_ = lean_box(0);
v_xs_x27_771_ = lean_array_fset(v_es_760_, v_j_763_, v___x_770_);
switch(lean_obj_tag(v_v_769_))
{
case 0:
{
lean_object* v_key_778_; lean_object* v_val_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_791_; 
v_key_778_ = lean_ctor_get(v_v_769_, 0);
v_val_779_ = lean_ctor_get(v_v_769_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v_v_769_);
if (v_isSharedCheck_791_ == 0)
{
v___x_781_ = v_v_769_;
v_isShared_782_ = v_isSharedCheck_791_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_val_779_);
lean_inc(v_key_778_);
lean_dec(v_v_769_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_791_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
size_t v___x_783_; size_t v___x_784_; uint8_t v___x_785_; 
v___x_783_ = lean_ptr_addr(v_x_758_);
v___x_784_ = lean_ptr_addr(v_key_778_);
v___x_785_ = lean_usize_dec_eq(v___x_783_, v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; 
lean_del_object(v___x_781_);
v___x_786_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_778_, v_val_779_, v_x_758_, v_x_759_);
v___x_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
v___y_773_ = v___x_787_;
goto v___jp_772_;
}
else
{
lean_object* v___x_789_; 
lean_dec(v_val_779_);
lean_dec(v_key_778_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v_x_759_);
lean_ctor_set(v___x_781_, 0, v_x_758_);
v___x_789_ = v___x_781_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_x_758_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_x_759_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
v___y_773_ = v___x_789_;
goto v___jp_772_;
}
}
}
}
case 1:
{
lean_object* v_node_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_804_; 
v_node_792_ = lean_ctor_get(v_v_769_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v_v_769_);
if (v_isSharedCheck_804_ == 0)
{
v___x_794_ = v_v_769_;
v_isShared_795_ = v_isSharedCheck_804_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_node_792_);
lean_dec(v_v_769_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_804_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
size_t v___x_796_; size_t v___x_797_; size_t v___x_798_; size_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_796_ = ((size_t)5ULL);
v___x_797_ = lean_usize_shift_right(v_x_756_, v___x_796_);
v___x_798_ = ((size_t)1ULL);
v___x_799_ = lean_usize_add(v_x_757_, v___x_798_);
v___x_800_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(v_node_792_, v___x_797_, v___x_799_, v_x_758_, v_x_759_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_800_);
v___x_802_ = v___x_794_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
v___y_773_ = v___x_802_;
goto v___jp_772_;
}
}
}
default: 
{
lean_object* v___x_805_; 
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v_x_758_);
lean_ctor_set(v___x_805_, 1, v_x_759_);
v___y_773_ = v___x_805_;
goto v___jp_772_;
}
}
v___jp_772_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = lean_array_fset(v_xs_x27_771_, v_j_763_, v___y_773_);
lean_dec(v_j_763_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_774_);
v___x_776_ = v___x_767_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
else
{
lean_object* v_ks_808_; lean_object* v_vs_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_827_; 
v_ks_808_ = lean_ctor_get(v_x_755_, 0);
v_vs_809_ = lean_ctor_get(v_x_755_, 1);
v_isSharedCheck_827_ = !lean_is_exclusive(v_x_755_);
if (v_isSharedCheck_827_ == 0)
{
v___x_811_ = v_x_755_;
v_isShared_812_ = v_isSharedCheck_827_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_vs_809_);
lean_inc(v_ks_808_);
lean_dec(v_x_755_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_827_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_ks_808_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_vs_809_);
v___x_814_ = v_reuseFailAlloc_826_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v_newNode_815_; size_t v___x_816_; uint8_t v___x_817_; 
v_newNode_815_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1___redArg(v___x_814_, v_x_758_, v_x_759_);
v___x_816_ = ((size_t)7ULL);
v___x_817_ = lean_usize_dec_le(v___x_816_, v_x_757_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_818_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_815_);
v___x_819_ = lean_unsigned_to_nat(4u);
v___x_820_ = lean_nat_dec_lt(v___x_818_, v___x_819_);
lean_dec(v___x_818_);
if (v___x_820_ == 0)
{
lean_object* v_ks_821_; lean_object* v_vs_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_ks_821_ = lean_ctor_get(v_newNode_815_, 0);
lean_inc_ref(v_ks_821_);
v_vs_822_ = lean_ctor_get(v_newNode_815_, 1);
lean_inc_ref(v_vs_822_);
lean_dec_ref(v_newNode_815_);
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___closed__0);
v___x_825_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg(v_x_757_, v_ks_821_, v_vs_822_, v___x_823_, v___x_824_);
lean_dec_ref(v_vs_822_);
lean_dec_ref(v_ks_821_);
return v___x_825_;
}
else
{
return v_newNode_815_;
}
}
else
{
return v_newNode_815_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg(size_t v_depth_828_, lean_object* v_keys_829_, lean_object* v_vals_830_, lean_object* v_i_831_, lean_object* v_entries_832_){
_start:
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = lean_array_get_size(v_keys_829_);
v___x_834_ = lean_nat_dec_lt(v_i_831_, v___x_833_);
if (v___x_834_ == 0)
{
lean_dec(v_i_831_);
return v_entries_832_;
}
else
{
lean_object* v_k_835_; lean_object* v_v_836_; size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; uint64_t v___x_840_; size_t v_h_841_; size_t v___x_842_; lean_object* v___x_843_; size_t v___x_844_; size_t v___x_845_; size_t v___x_846_; size_t v_h_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_k_835_ = lean_array_fget_borrowed(v_keys_829_, v_i_831_);
v_v_836_ = lean_array_fget_borrowed(v_vals_830_, v_i_831_);
v___x_837_ = lean_ptr_addr(v_k_835_);
v___x_838_ = ((size_t)3ULL);
v___x_839_ = lean_usize_shift_right(v___x_837_, v___x_838_);
v___x_840_ = lean_usize_to_uint64(v___x_839_);
v_h_841_ = lean_uint64_to_usize(v___x_840_);
v___x_842_ = ((size_t)5ULL);
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = ((size_t)1ULL);
v___x_845_ = lean_usize_sub(v_depth_828_, v___x_844_);
v___x_846_ = lean_usize_mul(v___x_842_, v___x_845_);
v_h_847_ = lean_usize_shift_right(v_h_841_, v___x_846_);
v___x_848_ = lean_nat_add(v_i_831_, v___x_843_);
lean_dec(v_i_831_);
lean_inc(v_v_836_);
lean_inc(v_k_835_);
v___x_849_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(v_entries_832_, v_h_847_, v_depth_828_, v_k_835_, v_v_836_);
v_i_831_ = v___x_848_;
v_entries_832_ = v___x_849_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_851_, lean_object* v_keys_852_, lean_object* v_vals_853_, lean_object* v_i_854_, lean_object* v_entries_855_){
_start:
{
size_t v_depth_boxed_856_; lean_object* v_res_857_; 
v_depth_boxed_856_ = lean_unbox_usize(v_depth_851_);
lean_dec(v_depth_851_);
v_res_857_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg(v_depth_boxed_856_, v_keys_852_, v_vals_853_, v_i_854_, v_entries_855_);
lean_dec_ref(v_vals_853_);
lean_dec_ref(v_keys_852_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___boxed(lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
size_t v_x_4722__boxed_863_; size_t v_x_4723__boxed_864_; lean_object* v_res_865_; 
v_x_4722__boxed_863_ = lean_unbox_usize(v_x_859_);
lean_dec(v_x_859_);
v_x_4723__boxed_864_ = lean_unbox_usize(v_x_860_);
lean_dec(v_x_860_);
v_res_865_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(v_x_858_, v_x_4722__boxed_863_, v_x_4723__boxed_864_, v_x_861_, v_x_862_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0___redArg(lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
size_t v___x_869_; size_t v___x_870_; size_t v___x_871_; uint64_t v___x_872_; size_t v___x_873_; size_t v___x_874_; lean_object* v___x_875_; 
v___x_869_ = lean_ptr_addr(v_x_867_);
v___x_870_ = ((size_t)3ULL);
v___x_871_ = lean_usize_shift_right(v___x_869_, v___x_870_);
v___x_872_ = lean_usize_to_uint64(v___x_871_);
v___x_873_ = lean_uint64_to_usize(v___x_872_);
v___x_874_ = ((size_t)1ULL);
v___x_875_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(v_x_866_, v___x_873_, v___x_874_, v_x_867_, v_x_868_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg___lam__0(lean_object* v_val_876_, lean_object* v_s_877_){
_start:
{
lean_object* v_vars_878_; lean_object* v_varMap_879_; lean_object* v_varsHistory_880_; lean_object* v_natToIntMap_881_; lean_object* v_natDef_882_; lean_object* v_dvds_883_; lean_object* v_lowers_884_; lean_object* v_uppers_885_; lean_object* v_diseqs_886_; lean_object* v_elimEqs_887_; lean_object* v_elimStack_888_; lean_object* v_occurs_889_; lean_object* v_assignment_890_; lean_object* v_nextCnstrId_891_; uint8_t v_caseSplits_892_; lean_object* v_steps_893_; lean_object* v_penalties_894_; lean_object* v_numReorderRequests_895_; lean_object* v_conflict_x3f_896_; lean_object* v_diseqSplits_897_; lean_object* v_divMod_898_; uint8_t v_usedCommRing_899_; lean_object* v_nonlinearOccs_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_916_; 
v_vars_878_ = lean_ctor_get(v_s_877_, 0);
v_varMap_879_ = lean_ctor_get(v_s_877_, 1);
v_varsHistory_880_ = lean_ctor_get(v_s_877_, 2);
v_natToIntMap_881_ = lean_ctor_get(v_s_877_, 3);
v_natDef_882_ = lean_ctor_get(v_s_877_, 4);
v_dvds_883_ = lean_ctor_get(v_s_877_, 5);
v_lowers_884_ = lean_ctor_get(v_s_877_, 6);
v_uppers_885_ = lean_ctor_get(v_s_877_, 7);
v_diseqs_886_ = lean_ctor_get(v_s_877_, 8);
v_elimEqs_887_ = lean_ctor_get(v_s_877_, 9);
v_elimStack_888_ = lean_ctor_get(v_s_877_, 10);
v_occurs_889_ = lean_ctor_get(v_s_877_, 11);
v_assignment_890_ = lean_ctor_get(v_s_877_, 12);
v_nextCnstrId_891_ = lean_ctor_get(v_s_877_, 13);
v_caseSplits_892_ = lean_ctor_get_uint8(v_s_877_, sizeof(void*)*21);
v_steps_893_ = lean_ctor_get(v_s_877_, 14);
v_penalties_894_ = lean_ctor_get(v_s_877_, 15);
v_numReorderRequests_895_ = lean_ctor_get(v_s_877_, 16);
v_conflict_x3f_896_ = lean_ctor_get(v_s_877_, 17);
v_diseqSplits_897_ = lean_ctor_get(v_s_877_, 18);
v_divMod_898_ = lean_ctor_get(v_s_877_, 19);
v_usedCommRing_899_ = lean_ctor_get_uint8(v_s_877_, sizeof(void*)*21 + 1);
v_nonlinearOccs_900_ = lean_ctor_get(v_s_877_, 20);
v_isSharedCheck_916_ = !lean_is_exclusive(v_s_877_);
if (v_isSharedCheck_916_ == 0)
{
v___x_902_ = v_s_877_;
v_isShared_903_ = v_isSharedCheck_916_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_nonlinearOccs_900_);
lean_inc(v_divMod_898_);
lean_inc(v_diseqSplits_897_);
lean_inc(v_conflict_x3f_896_);
lean_inc(v_numReorderRequests_895_);
lean_inc(v_penalties_894_);
lean_inc(v_steps_893_);
lean_inc(v_nextCnstrId_891_);
lean_inc(v_assignment_890_);
lean_inc(v_occurs_889_);
lean_inc(v_elimStack_888_);
lean_inc(v_elimEqs_887_);
lean_inc(v_diseqs_886_);
lean_inc(v_uppers_885_);
lean_inc(v_lowers_884_);
lean_inc(v_dvds_883_);
lean_inc(v_natDef_882_);
lean_inc(v_natToIntMap_881_);
lean_inc(v_varsHistory_880_);
lean_inc(v_varMap_879_);
lean_inc(v_vars_878_);
lean_dec(v_s_877_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_916_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___y_905_; lean_object* v___x_913_; 
v___x_913_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg(v_penalties_894_, v_val_876_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v___x_914_; 
v___x_914_ = lean_unsigned_to_nat(0u);
v___y_905_ = v___x_914_;
goto v___jp_904_;
}
else
{
lean_object* v_val_915_; 
v_val_915_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_val_915_);
lean_dec_ref_known(v___x_913_, 1);
v___y_905_ = v_val_915_;
goto v___jp_904_;
}
v___jp_904_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_906_ = lean_unsigned_to_nat(1u);
v___x_907_ = lean_nat_add(v___y_905_, v___x_906_);
lean_dec(v___y_905_);
v___x_908_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0___redArg(v_penalties_894_, v_val_876_, v___x_907_);
v___x_909_ = lean_nat_add(v_numReorderRequests_895_, v___x_906_);
lean_dec(v_numReorderRequests_895_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 16, v___x_909_);
lean_ctor_set(v___x_902_, 15, v___x_908_);
v___x_911_ = v___x_902_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_vars_878_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_varMap_879_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_varsHistory_880_);
lean_ctor_set(v_reuseFailAlloc_912_, 3, v_natToIntMap_881_);
lean_ctor_set(v_reuseFailAlloc_912_, 4, v_natDef_882_);
lean_ctor_set(v_reuseFailAlloc_912_, 5, v_dvds_883_);
lean_ctor_set(v_reuseFailAlloc_912_, 6, v_lowers_884_);
lean_ctor_set(v_reuseFailAlloc_912_, 7, v_uppers_885_);
lean_ctor_set(v_reuseFailAlloc_912_, 8, v_diseqs_886_);
lean_ctor_set(v_reuseFailAlloc_912_, 9, v_elimEqs_887_);
lean_ctor_set(v_reuseFailAlloc_912_, 10, v_elimStack_888_);
lean_ctor_set(v_reuseFailAlloc_912_, 11, v_occurs_889_);
lean_ctor_set(v_reuseFailAlloc_912_, 12, v_assignment_890_);
lean_ctor_set(v_reuseFailAlloc_912_, 13, v_nextCnstrId_891_);
lean_ctor_set(v_reuseFailAlloc_912_, 14, v_steps_893_);
lean_ctor_set(v_reuseFailAlloc_912_, 15, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_912_, 16, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_912_, 17, v_conflict_x3f_896_);
lean_ctor_set(v_reuseFailAlloc_912_, 18, v_diseqSplits_897_);
lean_ctor_set(v_reuseFailAlloc_912_, 19, v_divMod_898_);
lean_ctor_set(v_reuseFailAlloc_912_, 20, v_nonlinearOccs_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*21, v_caseSplits_892_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*21 + 1, v_usedCommRing_899_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg(lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_920_; lean_object* v_reorderRequest_x3f_921_; 
v___x_920_ = lean_st_ref_get(v_a_917_);
v_reorderRequest_x3f_921_ = lean_ctor_get(v___x_920_, 3);
lean_inc(v_reorderRequest_x3f_921_);
lean_dec(v___x_920_);
if (lean_obj_tag(v_reorderRequest_x3f_921_) == 1)
{
lean_object* v_val_922_; lean_object* v___f_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_val_922_ = lean_ctor_get(v_reorderRequest_x3f_921_, 0);
lean_inc(v_val_922_);
lean_dec_ref_known(v_reorderRequest_x3f_921_, 1);
v___f_923_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg___lam__0), 2, 1);
lean_closure_set(v___f_923_, 0, v_val_922_);
v___x_924_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_925_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_924_, v___f_923_, v_a_918_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_934_; 
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; 
v_unused_935_ = lean_ctor_get(v___x_925_, 0);
lean_dec(v_unused_935_);
v___x_927_ = v___x_925_;
v_isShared_928_ = v_isSharedCheck_934_;
goto v_resetjp_926_;
}
else
{
lean_dec(v___x_925_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_934_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_929_ = 1;
v___x_930_ = lean_box(v___x_929_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_930_);
v___x_932_ = v___x_927_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
v_a_936_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_925_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_925_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
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
else
{
uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
lean_dec(v_reorderRequest_x3f_921_);
v___x_944_ = 0;
v___x_945_ = lean_box(v___x_944_);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg___boxed(lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg(v_a_947_, v_a_948_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest(uint8_t v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg(v_a_952_, v_a_953_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___boxed(lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
uint8_t v_a_boxed_978_; lean_object* v_res_979_; 
v_a_boxed_978_ = lean_unbox(v_a_965_);
v_res_979_ = l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest(v_a_boxed_978_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
lean_dec(v_a_966_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0(lean_object* v_00_u03b2_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0___redArg(v_x_981_, v_x_982_, v_x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1(lean_object* v_00_u03b2_985_, lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg(v_x_986_, v_x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___boxed(lean_object* v_00_u03b2_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1(v_00_u03b2_989_, v_x_990_, v_x_991_);
lean_dec_ref(v_x_991_);
lean_dec_ref(v_x_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0(lean_object* v_00_u03b2_993_, lean_object* v_x_994_, size_t v_x_995_, size_t v_x_996_, lean_object* v_x_997_, lean_object* v_x_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(v_x_994_, v_x_995_, v_x_996_, v_x_997_, v_x_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
size_t v_x_5012__boxed_1006_; size_t v_x_5013__boxed_1007_; lean_object* v_res_1008_; 
v_x_5012__boxed_1006_ = lean_unbox_usize(v_x_1002_);
lean_dec(v_x_1002_);
v_x_5013__boxed_1007_ = lean_unbox_usize(v_x_1003_);
lean_dec(v_x_1003_);
v_res_1008_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0(v_00_u03b2_1000_, v_x_1001_, v_x_5012__boxed_1006_, v_x_5013__boxed_1007_, v_x_1004_, v_x_1005_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2(lean_object* v_00_u03b2_1009_, lean_object* v_x_1010_, size_t v_x_1011_, lean_object* v_x_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg(v_x_1010_, v_x_1011_, v_x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_){
_start:
{
size_t v_x_5029__boxed_1018_; lean_object* v_res_1019_; 
v_x_5029__boxed_1018_ = lean_unbox_usize(v_x_1016_);
lean_dec(v_x_1016_);
v_res_1019_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2(v_00_u03b2_1014_, v_x_1015_, v_x_5029__boxed_1018_, v_x_1017_);
lean_dec_ref(v_x_1017_);
lean_dec_ref(v_x_1015_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1020_, lean_object* v_n_1021_, lean_object* v_k_1022_, lean_object* v_v_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1___redArg(v_n_1021_, v_k_1022_, v_v_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1025_, size_t v_depth_1026_, lean_object* v_keys_1027_, lean_object* v_vals_1028_, lean_object* v_heq_1029_, lean_object* v_i_1030_, lean_object* v_entries_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg(v_depth_1026_, v_keys_1027_, v_vals_1028_, v_i_1030_, v_entries_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1033_, lean_object* v_depth_1034_, lean_object* v_keys_1035_, lean_object* v_vals_1036_, lean_object* v_heq_1037_, lean_object* v_i_1038_, lean_object* v_entries_1039_){
_start:
{
size_t v_depth_boxed_1040_; lean_object* v_res_1041_; 
v_depth_boxed_1040_ = lean_unbox_usize(v_depth_1034_);
lean_dec(v_depth_1034_);
v_res_1041_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2(v_00_u03b2_1033_, v_depth_boxed_1040_, v_keys_1035_, v_vals_1036_, v_heq_1037_, v_i_1038_, v_entries_1039_);
lean_dec_ref(v_vals_1036_);
lean_dec_ref(v_keys_1035_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1042_, lean_object* v_keys_1043_, lean_object* v_vals_1044_, lean_object* v_heq_1045_, lean_object* v_i_1046_, lean_object* v_k_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg(v_keys_1043_, v_vals_1044_, v_i_1046_, v_k_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1049_, lean_object* v_keys_1050_, lean_object* v_vals_1051_, lean_object* v_heq_1052_, lean_object* v_i_1053_, lean_object* v_k_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5(v_00_u03b2_1049_, v_keys_1050_, v_vals_1051_, v_heq_1052_, v_i_1053_, v_k_1054_);
lean_dec_ref(v_k_1054_);
lean_dec_ref(v_vals_1051_);
lean_dec_ref(v_keys_1050_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1056_, lean_object* v_x_1057_, lean_object* v_x_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1057_, v_x_1058_, v_x_1059_, v_x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___lam__0(lean_object* v_s_1062_){
_start:
{
lean_object* v_vars_1063_; lean_object* v_varMap_1064_; lean_object* v_varsHistory_1065_; lean_object* v_natToIntMap_1066_; lean_object* v_natDef_1067_; lean_object* v_dvds_1068_; lean_object* v_lowers_1069_; lean_object* v_uppers_1070_; lean_object* v_diseqs_1071_; lean_object* v_elimEqs_1072_; lean_object* v_elimStack_1073_; lean_object* v_occurs_1074_; lean_object* v_assignment_1075_; lean_object* v_nextCnstrId_1076_; lean_object* v_steps_1077_; lean_object* v_penalties_1078_; lean_object* v_numReorderRequests_1079_; lean_object* v_conflict_x3f_1080_; lean_object* v_diseqSplits_1081_; lean_object* v_divMod_1082_; uint8_t v_usedCommRing_1083_; lean_object* v_nonlinearOccs_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1092_; 
v_vars_1063_ = lean_ctor_get(v_s_1062_, 0);
v_varMap_1064_ = lean_ctor_get(v_s_1062_, 1);
v_varsHistory_1065_ = lean_ctor_get(v_s_1062_, 2);
v_natToIntMap_1066_ = lean_ctor_get(v_s_1062_, 3);
v_natDef_1067_ = lean_ctor_get(v_s_1062_, 4);
v_dvds_1068_ = lean_ctor_get(v_s_1062_, 5);
v_lowers_1069_ = lean_ctor_get(v_s_1062_, 6);
v_uppers_1070_ = lean_ctor_get(v_s_1062_, 7);
v_diseqs_1071_ = lean_ctor_get(v_s_1062_, 8);
v_elimEqs_1072_ = lean_ctor_get(v_s_1062_, 9);
v_elimStack_1073_ = lean_ctor_get(v_s_1062_, 10);
v_occurs_1074_ = lean_ctor_get(v_s_1062_, 11);
v_assignment_1075_ = lean_ctor_get(v_s_1062_, 12);
v_nextCnstrId_1076_ = lean_ctor_get(v_s_1062_, 13);
v_steps_1077_ = lean_ctor_get(v_s_1062_, 14);
v_penalties_1078_ = lean_ctor_get(v_s_1062_, 15);
v_numReorderRequests_1079_ = lean_ctor_get(v_s_1062_, 16);
v_conflict_x3f_1080_ = lean_ctor_get(v_s_1062_, 17);
v_diseqSplits_1081_ = lean_ctor_get(v_s_1062_, 18);
v_divMod_1082_ = lean_ctor_get(v_s_1062_, 19);
v_usedCommRing_1083_ = lean_ctor_get_uint8(v_s_1062_, sizeof(void*)*21 + 1);
v_nonlinearOccs_1084_ = lean_ctor_get(v_s_1062_, 20);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_s_1062_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1086_ = v_s_1062_;
v_isShared_1087_ = v_isSharedCheck_1092_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_nonlinearOccs_1084_);
lean_inc(v_divMod_1082_);
lean_inc(v_diseqSplits_1081_);
lean_inc(v_conflict_x3f_1080_);
lean_inc(v_numReorderRequests_1079_);
lean_inc(v_penalties_1078_);
lean_inc(v_steps_1077_);
lean_inc(v_nextCnstrId_1076_);
lean_inc(v_assignment_1075_);
lean_inc(v_occurs_1074_);
lean_inc(v_elimStack_1073_);
lean_inc(v_elimEqs_1072_);
lean_inc(v_diseqs_1071_);
lean_inc(v_uppers_1070_);
lean_inc(v_lowers_1069_);
lean_inc(v_dvds_1068_);
lean_inc(v_natDef_1067_);
lean_inc(v_natToIntMap_1066_);
lean_inc(v_varsHistory_1065_);
lean_inc(v_varMap_1064_);
lean_inc(v_vars_1063_);
lean_dec(v_s_1062_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1092_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
uint8_t v___x_1088_; lean_object* v___x_1090_; 
v___x_1088_ = 1;
if (v_isShared_1087_ == 0)
{
v___x_1090_ = v___x_1086_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_vars_1063_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_varMap_1064_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_varsHistory_1065_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v_natToIntMap_1066_);
lean_ctor_set(v_reuseFailAlloc_1091_, 4, v_natDef_1067_);
lean_ctor_set(v_reuseFailAlloc_1091_, 5, v_dvds_1068_);
lean_ctor_set(v_reuseFailAlloc_1091_, 6, v_lowers_1069_);
lean_ctor_set(v_reuseFailAlloc_1091_, 7, v_uppers_1070_);
lean_ctor_set(v_reuseFailAlloc_1091_, 8, v_diseqs_1071_);
lean_ctor_set(v_reuseFailAlloc_1091_, 9, v_elimEqs_1072_);
lean_ctor_set(v_reuseFailAlloc_1091_, 10, v_elimStack_1073_);
lean_ctor_set(v_reuseFailAlloc_1091_, 11, v_occurs_1074_);
lean_ctor_set(v_reuseFailAlloc_1091_, 12, v_assignment_1075_);
lean_ctor_set(v_reuseFailAlloc_1091_, 13, v_nextCnstrId_1076_);
lean_ctor_set(v_reuseFailAlloc_1091_, 14, v_steps_1077_);
lean_ctor_set(v_reuseFailAlloc_1091_, 15, v_penalties_1078_);
lean_ctor_set(v_reuseFailAlloc_1091_, 16, v_numReorderRequests_1079_);
lean_ctor_set(v_reuseFailAlloc_1091_, 17, v_conflict_x3f_1080_);
lean_ctor_set(v_reuseFailAlloc_1091_, 18, v_diseqSplits_1081_);
lean_ctor_set(v_reuseFailAlloc_1091_, 19, v_divMod_1082_);
lean_ctor_set(v_reuseFailAlloc_1091_, 20, v_nonlinearOccs_1084_);
lean_ctor_set_uint8(v_reuseFailAlloc_1091_, sizeof(void*)*21 + 1, v_usedCommRing_1083_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*21, v___x_1088_);
return v___x_1090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; lean_object* v_ngen_1096_; lean_object* v_namePrefix_1097_; lean_object* v_idx_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1128_; 
v___x_1095_ = lean_st_ref_get(v___y_1093_);
v_ngen_1096_ = lean_ctor_get(v___x_1095_, 2);
lean_inc_ref(v_ngen_1096_);
lean_dec(v___x_1095_);
v_namePrefix_1097_ = lean_ctor_get(v_ngen_1096_, 0);
v_idx_1098_ = lean_ctor_get(v_ngen_1096_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_ngen_1096_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1100_ = v_ngen_1096_;
v_isShared_1101_ = v_isSharedCheck_1128_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_idx_1098_);
lean_inc(v_namePrefix_1097_);
lean_dec(v_ngen_1096_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1128_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_r_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
lean_inc(v_idx_1098_);
lean_inc(v_namePrefix_1097_);
v_r_1102_ = l_Lean_Name_num___override(v_namePrefix_1097_, v_idx_1098_);
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1104_ = lean_nat_add(v_idx_1098_, v___x_1103_);
lean_dec(v_idx_1098_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 1, v___x_1104_);
v___x_1106_ = v___x_1100_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_namePrefix_1097_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1107_; lean_object* v_env_1108_; lean_object* v_nextMacroScope_1109_; lean_object* v_auxDeclNGen_1110_; lean_object* v_traceState_1111_; lean_object* v_cache_1112_; lean_object* v_recordedDeps_1113_; lean_object* v_messages_1114_; lean_object* v_infoState_1115_; lean_object* v_snapshotTasks_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1125_; 
v___x_1107_ = lean_st_ref_take(v___y_1093_);
v_env_1108_ = lean_ctor_get(v___x_1107_, 0);
v_nextMacroScope_1109_ = lean_ctor_get(v___x_1107_, 1);
v_auxDeclNGen_1110_ = lean_ctor_get(v___x_1107_, 3);
v_traceState_1111_ = lean_ctor_get(v___x_1107_, 4);
v_cache_1112_ = lean_ctor_get(v___x_1107_, 5);
v_recordedDeps_1113_ = lean_ctor_get(v___x_1107_, 6);
v_messages_1114_ = lean_ctor_get(v___x_1107_, 7);
v_infoState_1115_ = lean_ctor_get(v___x_1107_, 8);
v_snapshotTasks_1116_ = lean_ctor_get(v___x_1107_, 9);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v___x_1107_, 2);
lean_dec(v_unused_1126_);
v___x_1118_ = v___x_1107_;
v_isShared_1119_ = v_isSharedCheck_1125_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_snapshotTasks_1116_);
lean_inc(v_infoState_1115_);
lean_inc(v_messages_1114_);
lean_inc(v_recordedDeps_1113_);
lean_inc(v_cache_1112_);
lean_inc(v_traceState_1111_);
lean_inc(v_auxDeclNGen_1110_);
lean_inc(v_nextMacroScope_1109_);
lean_inc(v_env_1108_);
lean_dec(v___x_1107_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1125_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 2, v___x_1106_);
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_env_1108_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_nextMacroScope_1109_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_auxDeclNGen_1110_);
lean_ctor_set(v_reuseFailAlloc_1124_, 4, v_traceState_1111_);
lean_ctor_set(v_reuseFailAlloc_1124_, 5, v_cache_1112_);
lean_ctor_set(v_reuseFailAlloc_1124_, 6, v_recordedDeps_1113_);
lean_ctor_set(v_reuseFailAlloc_1124_, 7, v_messages_1114_);
lean_ctor_set(v_reuseFailAlloc_1124_, 8, v_infoState_1115_);
lean_ctor_set(v_reuseFailAlloc_1124_, 9, v_snapshotTasks_1116_);
v___x_1121_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_st_ref_put(v___y_1093_, v___x_1121_);
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v_r_1102_);
return v___x_1123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg___boxed(lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_1129_);
lean_dec(v___y_1129_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(uint8_t v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1145_; lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v___x_1145_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_1143_);
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0___boxed(lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
uint8_t v___y_12228__boxed_1167_; lean_object* v_res_1168_; 
v___y_12228__boxed_1167_ = lean_unbox(v___y_1154_);
v_res_1168_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(v___y_12228__boxed_1167_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec(v___y_1155_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase(lean_object* v_kind_1170_, uint8_t v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v___f_1184_; lean_object* v___x_1185_; 
v___f_1184_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0));
v___x_1185_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1187_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v___x_1185_, 1);
v___x_1187_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1173_, v_a_1181_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1189_; lean_object* v_cases_1190_; uint8_t v_precise_1191_; lean_object* v_decVars_1192_; lean_object* v_steps_1193_; lean_object* v_reorderRequest_x3f_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1223_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 1);
v___x_1189_ = lean_st_ref_take(v_a_1172_);
v_cases_1190_ = lean_ctor_get(v___x_1189_, 0);
v_precise_1191_ = lean_ctor_get_uint8(v___x_1189_, sizeof(void*)*4);
v_decVars_1192_ = lean_ctor_get(v___x_1189_, 1);
v_steps_1193_ = lean_ctor_get(v___x_1189_, 2);
v_reorderRequest_x3f_1194_ = lean_ctor_get(v___x_1189_, 3);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1196_ = v___x_1189_;
v_isShared_1197_ = v_isSharedCheck_1223_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_reorderRequest_x3f_1194_);
lean_inc(v_steps_1193_);
lean_inc(v_decVars_1192_);
lean_inc(v_cases_1190_);
lean_dec(v___x_1189_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1223_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
lean_inc_n(v_a_1186_, 2);
v___x_1198_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1198_, 0, v_kind_1170_);
lean_ctor_set(v___x_1198_, 1, v_a_1186_);
lean_ctor_set(v___x_1198_, 2, v_a_1188_);
v___x_1199_ = l_Lean_PersistentArray_push___redArg(v_cases_1190_, v___x_1198_);
v___x_1200_ = l_Lean_FVarIdSet_insert(v_decVars_1192_, v_a_1186_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 1, v___x_1200_);
lean_ctor_set(v___x_1196_, 0, v___x_1199_);
v___x_1202_ = v___x_1196_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_steps_1193_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_reorderRequest_x3f_1194_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*4, v_precise_1191_);
v___x_1202_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = lean_st_ref_put(v_a_1172_, v___x_1202_);
v___x_1204_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1205_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1204_, v___f_1184_, v_a_1173_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; 
v_unused_1213_ = lean_ctor_get(v___x_1205_, 0);
lean_dec(v_unused_1213_);
v___x_1207_ = v___x_1205_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_dec(v___x_1205_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v_a_1186_);
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1186_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec(v_a_1186_);
v_a_1214_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1205_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1205_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec(v_a_1186_);
lean_dec_ref(v_kind_1170_);
v_a_1224_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1187_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1187_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
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
else
{
lean_dec_ref(v_kind_1170_);
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___boxed(lean_object* v_kind_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
uint8_t v_a_boxed_1246_; lean_object* v_res_1247_; 
v_a_boxed_1246_ = lean_unbox(v_a_1233_);
v_res_1247_ = l_Lean_Meta_Grind_Arith_Cutsat_mkCase(v_kind_1232_, v_a_boxed_1246_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec(v_a_1234_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(uint8_t v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___boxed(lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
uint8_t v___y_12380__boxed_1275_; lean_object* v_res_1276_; 
v___y_12380__boxed_1275_ = lean_unbox(v___y_1262_);
v_res_1276_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(v___y_12380__boxed_1275_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec(v___y_1263_);
return v_res_1276_;
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
