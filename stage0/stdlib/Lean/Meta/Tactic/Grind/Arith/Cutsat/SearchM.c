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
v_liaSteps_255_ = lean_ctor_get(v_a_251_, 9);
lean_inc(v_liaSteps_255_);
lean_dec(v_a_251_);
v_steps_256_ = lean_ctor_get(v_a_248_, 14);
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
lean_object* v_vars_320_; lean_object* v_varMap_321_; lean_object* v_varsHistory_322_; lean_object* v_natToIntMap_323_; lean_object* v_natDef_324_; lean_object* v_dvds_325_; lean_object* v_lowers_326_; lean_object* v_uppers_327_; lean_object* v_diseqs_328_; lean_object* v_elimEqs_329_; lean_object* v_elimStack_330_; lean_object* v_occurs_331_; lean_object* v_assignment_332_; lean_object* v_nextCnstrId_333_; uint8_t v_caseSplits_334_; lean_object* v_steps_335_; lean_object* v_penalties_336_; lean_object* v_numReorderRequests_337_; lean_object* v_conflict_x3f_338_; lean_object* v_diseqSplits_339_; lean_object* v_divMod_340_; uint8_t v_usedCommRing_341_; lean_object* v_nonlinearOccs_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_350_; 
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
v_elimStack_330_ = lean_ctor_get(v_s_319_, 10);
v_occurs_331_ = lean_ctor_get(v_s_319_, 11);
v_assignment_332_ = lean_ctor_get(v_s_319_, 12);
v_nextCnstrId_333_ = lean_ctor_get(v_s_319_, 13);
v_caseSplits_334_ = lean_ctor_get_uint8(v_s_319_, sizeof(void*)*21);
v_steps_335_ = lean_ctor_get(v_s_319_, 14);
v_penalties_336_ = lean_ctor_get(v_s_319_, 15);
v_numReorderRequests_337_ = lean_ctor_get(v_s_319_, 16);
v_conflict_x3f_338_ = lean_ctor_get(v_s_319_, 17);
v_diseqSplits_339_ = lean_ctor_get(v_s_319_, 18);
v_divMod_340_ = lean_ctor_get(v_s_319_, 19);
v_usedCommRing_341_ = lean_ctor_get_uint8(v_s_319_, sizeof(void*)*21 + 1);
v_nonlinearOccs_342_ = lean_ctor_get(v_s_319_, 20);
v_isSharedCheck_350_ = !lean_is_exclusive(v_s_319_);
if (v_isSharedCheck_350_ == 0)
{
v___x_344_ = v_s_319_;
v_isShared_345_ = v_isSharedCheck_350_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_nonlinearOccs_342_);
lean_inc(v_divMod_340_);
lean_inc(v_diseqSplits_339_);
lean_inc(v_conflict_x3f_338_);
lean_inc(v_numReorderRequests_337_);
lean_inc(v_penalties_336_);
lean_inc(v_steps_335_);
lean_inc(v_nextCnstrId_333_);
lean_inc(v_assignment_332_);
lean_inc(v_occurs_331_);
lean_inc(v_elimStack_330_);
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
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_350_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_346_ = lean_nat_add(v_steps_335_, v_steps_318_);
lean_dec(v_steps_335_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 14, v___x_346_);
v___x_348_ = v___x_344_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_vars_320_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_varMap_321_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v_varsHistory_322_);
lean_ctor_set(v_reuseFailAlloc_349_, 3, v_natToIntMap_323_);
lean_ctor_set(v_reuseFailAlloc_349_, 4, v_natDef_324_);
lean_ctor_set(v_reuseFailAlloc_349_, 5, v_dvds_325_);
lean_ctor_set(v_reuseFailAlloc_349_, 6, v_lowers_326_);
lean_ctor_set(v_reuseFailAlloc_349_, 7, v_uppers_327_);
lean_ctor_set(v_reuseFailAlloc_349_, 8, v_diseqs_328_);
lean_ctor_set(v_reuseFailAlloc_349_, 9, v_elimEqs_329_);
lean_ctor_set(v_reuseFailAlloc_349_, 10, v_elimStack_330_);
lean_ctor_set(v_reuseFailAlloc_349_, 11, v_occurs_331_);
lean_ctor_set(v_reuseFailAlloc_349_, 12, v_assignment_332_);
lean_ctor_set(v_reuseFailAlloc_349_, 13, v_nextCnstrId_333_);
lean_ctor_set(v_reuseFailAlloc_349_, 14, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_349_, 15, v_penalties_336_);
lean_ctor_set(v_reuseFailAlloc_349_, 16, v_numReorderRequests_337_);
lean_ctor_set(v_reuseFailAlloc_349_, 17, v_conflict_x3f_338_);
lean_ctor_set(v_reuseFailAlloc_349_, 18, v_diseqSplits_339_);
lean_ctor_set(v_reuseFailAlloc_349_, 19, v_divMod_340_);
lean_ctor_set(v_reuseFailAlloc_349_, 20, v_nonlinearOccs_342_);
lean_ctor_set_uint8(v_reuseFailAlloc_349_, sizeof(void*)*21, v_caseSplits_334_);
lean_ctor_set_uint8(v_reuseFailAlloc_349_, sizeof(void*)*21 + 1, v_usedCommRing_341_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0___boxed(lean_object* v_steps_351_, lean_object* v_s_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0(v_steps_351_, v_s_352_);
lean_dec(v_steps_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_357_; lean_object* v_steps_358_; lean_object* v___f_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_357_ = lean_st_ref_get(v_a_354_);
v_steps_358_ = lean_ctor_get(v___x_357_, 2);
lean_inc(v_steps_358_);
lean_dec(v___x_357_);
v___f_359_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_359_, 0, v_steps_358_);
v___x_360_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_361_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_360_, v___f_359_, v_a_355_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___boxed(lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(v_a_362_, v_a_363_);
lean_dec(v_a_363_);
lean_dec(v_a_362_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps(uint8_t v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(v_a_367_, v_a_368_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___boxed(lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
uint8_t v_a_boxed_393_; lean_object* v_res_394_; 
v_a_boxed_393_ = lean_unbox(v_a_380_);
v_res_394_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps(v_a_boxed_393_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec(v_a_382_);
lean_dec(v_a_381_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0_spec__0(lean_object* v_msgData_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; lean_object* v_env_402_; uint8_t v___x_403_; lean_object* v_env_404_; lean_object* v___x_405_; lean_object* v_toCold_406_; lean_object* v_mctx_407_; lean_object* v_lctx_408_; lean_object* v_options_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_401_ = lean_st_ref_get(v___y_399_);
v_env_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc_ref(v_env_402_);
lean_dec(v___x_401_);
v___x_403_ = 0;
v_env_404_ = l_Lean_Environment_setRecordingDeps(v_env_402_, v___x_403_);
v___x_405_ = lean_st_ref_get(v___y_397_);
v_toCold_406_ = lean_ctor_get(v___y_398_, 0);
v_mctx_407_ = lean_ctor_get(v___x_405_, 0);
lean_inc_ref(v_mctx_407_);
lean_dec(v___x_405_);
v_lctx_408_ = lean_ctor_get(v___y_396_, 2);
v_options_409_ = lean_ctor_get(v_toCold_406_, 2);
lean_inc_ref(v_options_409_);
lean_inc_ref(v_lctx_408_);
v___x_410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_410_, 0, v_env_404_);
lean_ctor_set(v___x_410_, 1, v_mctx_407_);
lean_ctor_set(v___x_410_, 2, v_lctx_408_);
lean_ctor_set(v___x_410_, 3, v_options_409_);
v___x_411_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_msgData_395_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0_spec__0___boxed(lean_object* v_msgData_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0_spec__0(v_msgData_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_419_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_420_; double v___x_421_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_float_of_nat(v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg(lean_object* v_cls_425_, lean_object* v_msg_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_ref_432_; lean_object* v___x_433_; lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_479_; 
v_ref_432_ = lean_ctor_get(v___y_429_, 2);
v___x_433_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0_spec__0(v_msg_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_479_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_479_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_479_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v_traceState_439_; lean_object* v_env_440_; lean_object* v_nextMacroScope_441_; lean_object* v_ngen_442_; lean_object* v_auxDeclNGen_443_; lean_object* v_cache_444_; lean_object* v_recordedDeps_445_; lean_object* v_messages_446_; lean_object* v_infoState_447_; lean_object* v_snapshotTasks_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_478_; 
v___x_438_ = lean_st_ref_take(v___y_430_);
v_traceState_439_ = lean_ctor_get(v___x_438_, 4);
v_env_440_ = lean_ctor_get(v___x_438_, 0);
v_nextMacroScope_441_ = lean_ctor_get(v___x_438_, 1);
v_ngen_442_ = lean_ctor_get(v___x_438_, 2);
v_auxDeclNGen_443_ = lean_ctor_get(v___x_438_, 3);
v_cache_444_ = lean_ctor_get(v___x_438_, 5);
v_recordedDeps_445_ = lean_ctor_get(v___x_438_, 6);
v_messages_446_ = lean_ctor_get(v___x_438_, 7);
v_infoState_447_ = lean_ctor_get(v___x_438_, 8);
v_snapshotTasks_448_ = lean_ctor_get(v___x_438_, 9);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_478_ == 0)
{
v___x_450_ = v___x_438_;
v_isShared_451_ = v_isSharedCheck_478_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_snapshotTasks_448_);
lean_inc(v_infoState_447_);
lean_inc(v_messages_446_);
lean_inc(v_recordedDeps_445_);
lean_inc(v_cache_444_);
lean_inc(v_traceState_439_);
lean_inc(v_auxDeclNGen_443_);
lean_inc(v_ngen_442_);
lean_inc(v_nextMacroScope_441_);
lean_inc(v_env_440_);
lean_dec(v___x_438_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_478_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
uint64_t v_tid_452_; lean_object* v_traces_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_477_; 
v_tid_452_ = lean_ctor_get_uint64(v_traceState_439_, sizeof(void*)*1);
v_traces_453_ = lean_ctor_get(v_traceState_439_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_traceState_439_);
if (v_isSharedCheck_477_ == 0)
{
v___x_455_ = v_traceState_439_;
v_isShared_456_ = v_isSharedCheck_477_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_traces_453_);
lean_dec(v_traceState_439_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_477_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_458_; double v___x_459_; uint8_t v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_457_ = lean_box(0);
v___x_458_ = lean_box(0);
v___x_459_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__0);
v___x_460_ = 0;
v___x_461_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__1));
v___x_462_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_462_, 0, v_cls_425_);
lean_ctor_set(v___x_462_, 1, v___x_458_);
lean_ctor_set(v___x_462_, 2, v___x_461_);
lean_ctor_set_float(v___x_462_, sizeof(void*)*3, v___x_459_);
lean_ctor_set_float(v___x_462_, sizeof(void*)*3 + 8, v___x_459_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*3 + 16, v___x_460_);
v___x_463_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___closed__2));
v___x_464_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_464_, 0, v___x_462_);
lean_ctor_set(v___x_464_, 1, v_a_434_);
lean_ctor_set(v___x_464_, 2, v___x_463_);
lean_inc(v_ref_432_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v_ref_432_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_Lean_PersistentArray_push___redArg(v_traces_453_, v___x_465_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v___x_466_);
v___x_468_ = v___x_455_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_466_);
lean_ctor_set_uint64(v_reuseFailAlloc_476_, sizeof(void*)*1, v_tid_452_);
v___x_468_ = v_reuseFailAlloc_476_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_470_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 4, v___x_468_);
v___x_470_ = v___x_450_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_env_440_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_nextMacroScope_441_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v_ngen_442_);
lean_ctor_set(v_reuseFailAlloc_475_, 3, v_auxDeclNGen_443_);
lean_ctor_set(v_reuseFailAlloc_475_, 4, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_475_, 5, v_cache_444_);
lean_ctor_set(v_reuseFailAlloc_475_, 6, v_recordedDeps_445_);
lean_ctor_set(v_reuseFailAlloc_475_, 7, v_messages_446_);
lean_ctor_set(v_reuseFailAlloc_475_, 8, v_infoState_447_);
lean_ctor_set(v_reuseFailAlloc_475_, 9, v_snapshotTasks_448_);
v___x_470_ = v_reuseFailAlloc_475_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = lean_st_ref_put(v___y_430_, v___x_470_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_457_);
v___x_473_ = v___x_436_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_457_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg___boxed(lean_object* v_cls_480_, lean_object* v_msg_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg(v_cls_480_, v_msg_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
return v_res_487_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__7(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__4));
v___x_501_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__6));
v___x_502_ = l_Lean_Name_append(v___x_501_, v___x_500_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__9(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__8));
v___x_505_ = l_Lean_stringToMessageData(v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder(lean_object* v_x_506_, uint8_t v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_509_, v_a_517_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v___x_520_, 1);
v___x_522_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_511_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_590_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_590_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_590_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_590_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v_liaReorders_527_; lean_object* v_numReorderRequests_528_; uint8_t v___x_529_; 
v_liaReorders_527_ = lean_ctor_get(v_a_523_, 10);
lean_inc(v_liaReorders_527_);
lean_dec(v_a_523_);
v_numReorderRequests_528_ = lean_ctor_get(v_a_521_, 16);
lean_inc(v_numReorderRequests_528_);
lean_dec(v_a_521_);
v___x_529_ = lean_nat_dec_le(v_liaReorders_527_, v_numReorderRequests_528_);
lean_dec(v_numReorderRequests_528_);
lean_dec(v_liaReorders_527_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; 
lean_del_object(v___x_525_);
v___x_530_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_506_, v_a_509_, v_a_517_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_576_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_576_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_576_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_576_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___y_536_; lean_object* v_toCold_557_; lean_object* v_options_558_; uint8_t v_hasTrace_559_; 
v_toCold_557_ = lean_ctor_get(v_a_517_, 0);
v_options_558_ = lean_ctor_get(v_toCold_557_, 2);
v_hasTrace_559_ = lean_ctor_get_uint8(v_options_558_, sizeof(void*)*1);
if (v_hasTrace_559_ == 0)
{
v___y_536_ = v_a_508_;
goto v___jp_535_;
}
else
{
lean_object* v_inheritedTraceOptions_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v_inheritedTraceOptions_560_ = lean_ctor_get(v_toCold_557_, 11);
v___x_561_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__4));
v___x_562_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__7);
v___x_563_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_560_, v_options_558_, v___x_562_);
if (v___x_563_ == 0)
{
v___y_536_ = v_a_508_;
goto v___jp_535_;
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_564_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___closed__9);
lean_inc(v_a_531_);
v___x_565_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_531_);
v___x_566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg(v___x_561_, v___x_566_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_dec_ref_known(v___x_567_, 1);
v___y_536_ = v_a_508_;
goto v___jp_535_;
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_del_object(v___x_533_);
lean_dec(v_a_531_);
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
v___jp_535_:
{
lean_object* v___x_537_; lean_object* v_cases_538_; uint8_t v_precise_539_; lean_object* v_decVars_540_; lean_object* v_steps_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_555_; 
v___x_537_ = lean_st_ref_take(v___y_536_);
v_cases_538_ = lean_ctor_get(v___x_537_, 0);
v_precise_539_ = lean_ctor_get_uint8(v___x_537_, sizeof(void*)*4);
v_decVars_540_ = lean_ctor_get(v___x_537_, 1);
v_steps_541_ = lean_ctor_get(v___x_537_, 2);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v___x_537_, 3);
lean_dec(v_unused_556_);
v___x_543_ = v___x_537_;
v_isShared_544_ = v_isSharedCheck_555_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_steps_541_);
lean_inc(v_decVars_540_);
lean_inc(v_cases_538_);
lean_dec(v___x_537_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_555_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v_a_531_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 3, v___x_545_);
v___x_547_ = v___x_543_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_cases_538_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_decVars_540_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_steps_541_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v___x_545_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*4, v_precise_539_);
v___x_547_ = v_reuseFailAlloc_554_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_548_ = lean_st_ref_put(v___y_536_, v___x_547_);
v___x_549_ = 1;
v___x_550_ = lean_box(v___x_549_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_550_);
v___x_552_ = v___x_533_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
v_a_577_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_530_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_530_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
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
else
{
uint8_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_585_ = 0;
v___x_586_ = lean_box(v___x_585_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_586_);
v___x_588_ = v___x_525_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec(v_a_521_);
v_a_591_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_522_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_522_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
v_a_599_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_520_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_520_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_requestReorder___boxed(lean_object* v_x_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
uint8_t v_a_boxed_621_; lean_object* v_res_622_; 
v_a_boxed_621_ = lean_unbox(v_a_608_);
v_res_622_ = l_Lean_Meta_Grind_Arith_Cutsat_requestReorder(v_x_607_, v_a_boxed_621_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec(v_a_610_);
lean_dec(v_a_609_);
lean_dec(v_x_607_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0(lean_object* v_cls_623_, lean_object* v_msg_624_, uint8_t v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___redArg(v_cls_623_, v_msg_624_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0___boxed(lean_object* v_cls_639_, lean_object* v_msg_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
uint8_t v___y_24223__boxed_654_; lean_object* v_res_655_; 
v___y_24223__boxed_654_ = lean_unbox(v___y_641_);
v_res_655_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_requestReorder_spec__0(v_cls_639_, v_msg_640_, v___y_24223__boxed_654_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec(v___y_643_);
lean_dec(v___y_642_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_656_, lean_object* v_vals_657_, lean_object* v_i_658_, lean_object* v_k_659_){
_start:
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = lean_array_get_size(v_keys_656_);
v___x_661_ = lean_nat_dec_lt(v_i_658_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
lean_dec(v_i_658_);
v___x_662_ = lean_box(0);
return v___x_662_;
}
else
{
lean_object* v_k_x27_663_; size_t v___x_664_; size_t v___x_665_; uint8_t v___x_666_; 
v_k_x27_663_ = lean_array_fget_borrowed(v_keys_656_, v_i_658_);
v___x_664_ = lean_ptr_addr(v_k_659_);
v___x_665_ = lean_ptr_addr(v_k_x27_663_);
v___x_666_ = lean_usize_dec_eq(v___x_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(1u);
v___x_668_ = lean_nat_add(v_i_658_, v___x_667_);
lean_dec(v_i_658_);
v_i_658_ = v___x_668_;
goto _start;
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_array_fget_borrowed(v_vals_657_, v_i_658_);
lean_dec(v_i_658_);
lean_inc(v___x_670_);
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_672_, lean_object* v_vals_673_, lean_object* v_i_674_, lean_object* v_k_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg(v_keys_672_, v_vals_673_, v_i_674_, v_k_675_);
lean_dec_ref(v_k_675_);
lean_dec_ref(v_vals_673_);
lean_dec_ref(v_keys_672_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg(lean_object* v_x_677_, size_t v_x_678_, lean_object* v_x_679_){
_start:
{
if (lean_obj_tag(v_x_677_) == 0)
{
lean_object* v_es_680_; lean_object* v___x_681_; size_t v___x_682_; size_t v___x_683_; lean_object* v_j_684_; lean_object* v___x_685_; 
v_es_680_ = lean_ctor_get(v_x_677_, 0);
v___x_681_ = lean_box(2);
v___x_682_ = ((size_t)31ULL);
v___x_683_ = lean_usize_land(v_x_678_, v___x_682_);
v_j_684_ = lean_usize_to_nat(v___x_683_);
v___x_685_ = lean_array_get_borrowed(v___x_681_, v_es_680_, v_j_684_);
lean_dec(v_j_684_);
switch(lean_obj_tag(v___x_685_))
{
case 0:
{
lean_object* v_key_686_; lean_object* v_val_687_; size_t v___x_688_; size_t v___x_689_; uint8_t v___x_690_; 
v_key_686_ = lean_ctor_get(v___x_685_, 0);
v_val_687_ = lean_ctor_get(v___x_685_, 1);
v___x_688_ = lean_ptr_addr(v_x_679_);
v___x_689_ = lean_ptr_addr(v_key_686_);
v___x_690_ = lean_usize_dec_eq(v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
v___x_691_ = lean_box(0);
return v___x_691_;
}
else
{
lean_object* v___x_692_; 
lean_inc(v_val_687_);
v___x_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_692_, 0, v_val_687_);
return v___x_692_;
}
}
case 1:
{
lean_object* v_node_693_; size_t v___x_694_; size_t v___x_695_; 
v_node_693_ = lean_ctor_get(v___x_685_, 0);
v___x_694_ = ((size_t)5ULL);
v___x_695_ = lean_usize_shift_right(v_x_678_, v___x_694_);
v_x_677_ = v_node_693_;
v_x_678_ = v___x_695_;
goto _start;
}
default: 
{
lean_object* v___x_697_; 
v___x_697_ = lean_box(0);
return v___x_697_;
}
}
}
else
{
lean_object* v_ks_698_; lean_object* v_vs_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v_ks_698_ = lean_ctor_get(v_x_677_, 0);
v_vs_699_ = lean_ctor_get(v_x_677_, 1);
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg(v_ks_698_, v_vs_699_, v___x_700_, v_x_679_);
return v___x_701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg___boxed(lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_x_704_){
_start:
{
size_t v_x_4570__boxed_705_; lean_object* v_res_706_; 
v_x_4570__boxed_705_ = lean_unbox_usize(v_x_703_);
lean_dec(v_x_703_);
v_res_706_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg(v_x_702_, v_x_4570__boxed_705_, v_x_704_);
lean_dec_ref(v_x_704_);
lean_dec_ref(v_x_702_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg(lean_object* v_x_707_, lean_object* v_x_708_){
_start:
{
size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; uint64_t v___x_712_; size_t v___x_713_; lean_object* v___x_714_; 
v___x_709_ = lean_ptr_addr(v_x_708_);
v___x_710_ = ((size_t)3ULL);
v___x_711_ = lean_usize_shift_right(v___x_709_, v___x_710_);
v___x_712_ = lean_usize_to_uint64(v___x_711_);
v___x_713_ = lean_uint64_to_usize(v___x_712_);
v___x_714_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg(v_x_707_, v___x_713_, v_x_708_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg___boxed(lean_object* v_x_715_, lean_object* v_x_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg(v_x_715_, v_x_716_);
lean_dec_ref(v_x_716_);
lean_dec_ref(v_x_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_718_, lean_object* v_x_719_, lean_object* v_x_720_, lean_object* v_x_721_){
_start:
{
lean_object* v_ks_722_; lean_object* v_vs_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_749_; 
v_ks_722_ = lean_ctor_get(v_x_718_, 0);
v_vs_723_ = lean_ctor_get(v_x_718_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v_x_718_);
if (v_isSharedCheck_749_ == 0)
{
v___x_725_ = v_x_718_;
v_isShared_726_ = v_isSharedCheck_749_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_vs_723_);
lean_inc(v_ks_722_);
lean_dec(v_x_718_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_749_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = lean_array_get_size(v_ks_722_);
v___x_728_ = lean_nat_dec_lt(v_x_719_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
lean_dec(v_x_719_);
v___x_729_ = lean_array_push(v_ks_722_, v_x_720_);
v___x_730_ = lean_array_push(v_vs_723_, v_x_721_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v___x_730_);
lean_ctor_set(v___x_725_, 0, v___x_729_);
v___x_732_ = v___x_725_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
else
{
lean_object* v_k_x27_734_; size_t v___x_735_; size_t v___x_736_; uint8_t v___x_737_; 
v_k_x27_734_ = lean_array_fget_borrowed(v_ks_722_, v_x_719_);
v___x_735_ = lean_ptr_addr(v_x_720_);
v___x_736_ = lean_ptr_addr(v_k_x27_734_);
v___x_737_ = lean_usize_dec_eq(v___x_735_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_739_; 
if (v_isShared_726_ == 0)
{
v___x_739_ = v___x_725_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_ks_722_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_vs_723_);
v___x_739_ = v_reuseFailAlloc_743_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_add(v_x_719_, v___x_740_);
lean_dec(v_x_719_);
v_x_718_ = v___x_739_;
v_x_719_ = v___x_741_;
goto _start;
}
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_744_ = lean_array_fset(v_ks_722_, v_x_719_, v_x_720_);
v___x_745_ = lean_array_fset(v_vs_723_, v_x_719_, v_x_721_);
lean_dec(v_x_719_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v___x_745_);
lean_ctor_set(v___x_725_, 0, v___x_744_);
v___x_747_ = v___x_725_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1___redArg(lean_object* v_n_750_, lean_object* v_k_751_, lean_object* v_v_752_){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1_spec__3___redArg(v_n_750_, v___x_753_, v_k_751_, v_v_752_);
return v___x_754_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(lean_object* v_x_756_, size_t v_x_757_, size_t v_x_758_, lean_object* v_x_759_, lean_object* v_x_760_){
_start:
{
if (lean_obj_tag(v_x_756_) == 0)
{
lean_object* v_es_761_; size_t v___x_762_; size_t v___x_763_; lean_object* v_j_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_es_761_ = lean_ctor_get(v_x_756_, 0);
v___x_762_ = ((size_t)31ULL);
v___x_763_ = lean_usize_land(v_x_757_, v___x_762_);
v_j_764_ = lean_usize_to_nat(v___x_763_);
v___x_765_ = lean_array_get_size(v_es_761_);
v___x_766_ = lean_nat_dec_lt(v_j_764_, v___x_765_);
if (v___x_766_ == 0)
{
lean_dec(v_j_764_);
lean_dec(v_x_760_);
lean_dec_ref(v_x_759_);
return v_x_756_;
}
else
{
lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_807_; 
lean_inc_ref(v_es_761_);
v_isSharedCheck_807_ = !lean_is_exclusive(v_x_756_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v_x_756_, 0);
lean_dec(v_unused_808_);
v___x_768_ = v_x_756_;
v_isShared_769_ = v_isSharedCheck_807_;
goto v_resetjp_767_;
}
else
{
lean_dec(v_x_756_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_807_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v_v_770_; lean_object* v___x_771_; lean_object* v_xs_x27_772_; lean_object* v___y_774_; 
v_v_770_ = lean_array_fget(v_es_761_, v_j_764_);
v___x_771_ = lean_box(0);
v_xs_x27_772_ = lean_array_fset(v_es_761_, v_j_764_, v___x_771_);
switch(lean_obj_tag(v_v_770_))
{
case 0:
{
lean_object* v_key_779_; lean_object* v_val_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_792_; 
v_key_779_ = lean_ctor_get(v_v_770_, 0);
v_val_780_ = lean_ctor_get(v_v_770_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_v_770_);
if (v_isSharedCheck_792_ == 0)
{
v___x_782_ = v_v_770_;
v_isShared_783_ = v_isSharedCheck_792_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_val_780_);
lean_inc(v_key_779_);
lean_dec(v_v_770_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_792_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
size_t v___x_784_; size_t v___x_785_; uint8_t v___x_786_; 
v___x_784_ = lean_ptr_addr(v_x_759_);
v___x_785_ = lean_ptr_addr(v_key_779_);
v___x_786_ = lean_usize_dec_eq(v___x_784_, v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; 
lean_del_object(v___x_782_);
v___x_787_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_779_, v_val_780_, v_x_759_, v_x_760_);
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
v___y_774_ = v___x_788_;
goto v___jp_773_;
}
else
{
lean_object* v___x_790_; 
lean_dec(v_val_780_);
lean_dec(v_key_779_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v_x_760_);
lean_ctor_set(v___x_782_, 0, v_x_759_);
v___x_790_ = v___x_782_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_x_759_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_x_760_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
v___y_774_ = v___x_790_;
goto v___jp_773_;
}
}
}
}
case 1:
{
lean_object* v_node_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_805_; 
v_node_793_ = lean_ctor_get(v_v_770_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v_v_770_);
if (v_isSharedCheck_805_ == 0)
{
v___x_795_ = v_v_770_;
v_isShared_796_ = v_isSharedCheck_805_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_node_793_);
lean_dec(v_v_770_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_805_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
size_t v___x_797_; size_t v___x_798_; size_t v___x_799_; size_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_797_ = ((size_t)5ULL);
v___x_798_ = lean_usize_shift_right(v_x_757_, v___x_797_);
v___x_799_ = ((size_t)1ULL);
v___x_800_ = lean_usize_add(v_x_758_, v___x_799_);
v___x_801_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(v_node_793_, v___x_798_, v___x_800_, v_x_759_, v_x_760_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_801_);
v___x_803_ = v___x_795_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
v___y_774_ = v___x_803_;
goto v___jp_773_;
}
}
}
default: 
{
lean_object* v___x_806_; 
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v_x_759_);
lean_ctor_set(v___x_806_, 1, v_x_760_);
v___y_774_ = v___x_806_;
goto v___jp_773_;
}
}
v___jp_773_:
{
lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_775_ = lean_array_fset(v_xs_x27_772_, v_j_764_, v___y_774_);
lean_dec(v_j_764_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_775_);
v___x_777_ = v___x_768_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
else
{
lean_object* v_ks_809_; lean_object* v_vs_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_828_; 
v_ks_809_ = lean_ctor_get(v_x_756_, 0);
v_vs_810_ = lean_ctor_get(v_x_756_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v_x_756_);
if (v_isSharedCheck_828_ == 0)
{
v___x_812_ = v_x_756_;
v_isShared_813_ = v_isSharedCheck_828_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_vs_810_);
lean_inc(v_ks_809_);
lean_dec(v_x_756_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_828_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_ks_809_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_vs_810_);
v___x_815_ = v_reuseFailAlloc_827_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v_newNode_816_; size_t v___x_817_; uint8_t v___x_818_; 
v_newNode_816_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1___redArg(v___x_815_, v_x_759_, v_x_760_);
v___x_817_ = ((size_t)7ULL);
v___x_818_ = lean_usize_dec_le(v___x_817_, v_x_758_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_819_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_816_);
v___x_820_ = lean_unsigned_to_nat(4u);
v___x_821_ = lean_nat_dec_lt(v___x_819_, v___x_820_);
lean_dec(v___x_819_);
if (v___x_821_ == 0)
{
lean_object* v_ks_822_; lean_object* v_vs_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_ks_822_ = lean_ctor_get(v_newNode_816_, 0);
lean_inc_ref(v_ks_822_);
v_vs_823_ = lean_ctor_get(v_newNode_816_, 1);
lean_inc_ref(v_vs_823_);
lean_dec_ref(v_newNode_816_);
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___closed__0);
v___x_826_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg(v_x_758_, v_ks_822_, v_vs_823_, v___x_824_, v___x_825_);
lean_dec_ref(v_vs_823_);
lean_dec_ref(v_ks_822_);
return v___x_826_;
}
else
{
return v_newNode_816_;
}
}
else
{
return v_newNode_816_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg(size_t v_depth_829_, lean_object* v_keys_830_, lean_object* v_vals_831_, lean_object* v_i_832_, lean_object* v_entries_833_){
_start:
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = lean_array_get_size(v_keys_830_);
v___x_835_ = lean_nat_dec_lt(v_i_832_, v___x_834_);
if (v___x_835_ == 0)
{
lean_dec(v_i_832_);
return v_entries_833_;
}
else
{
lean_object* v_k_836_; lean_object* v_v_837_; size_t v___x_838_; size_t v___x_839_; size_t v___x_840_; uint64_t v___x_841_; size_t v_h_842_; size_t v___x_843_; lean_object* v___x_844_; size_t v___x_845_; size_t v___x_846_; size_t v___x_847_; size_t v_h_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_k_836_ = lean_array_fget_borrowed(v_keys_830_, v_i_832_);
v_v_837_ = lean_array_fget_borrowed(v_vals_831_, v_i_832_);
v___x_838_ = lean_ptr_addr(v_k_836_);
v___x_839_ = ((size_t)3ULL);
v___x_840_ = lean_usize_shift_right(v___x_838_, v___x_839_);
v___x_841_ = lean_usize_to_uint64(v___x_840_);
v_h_842_ = lean_uint64_to_usize(v___x_841_);
v___x_843_ = ((size_t)5ULL);
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = ((size_t)1ULL);
v___x_846_ = lean_usize_sub(v_depth_829_, v___x_845_);
v___x_847_ = lean_usize_mul(v___x_843_, v___x_846_);
v_h_848_ = lean_usize_shift_right(v_h_842_, v___x_847_);
v___x_849_ = lean_nat_add(v_i_832_, v___x_844_);
lean_dec(v_i_832_);
lean_inc(v_v_837_);
lean_inc(v_k_836_);
v___x_850_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(v_entries_833_, v_h_848_, v_depth_829_, v_k_836_, v_v_837_);
v_i_832_ = v___x_849_;
v_entries_833_ = v___x_850_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_852_, lean_object* v_keys_853_, lean_object* v_vals_854_, lean_object* v_i_855_, lean_object* v_entries_856_){
_start:
{
size_t v_depth_boxed_857_; lean_object* v_res_858_; 
v_depth_boxed_857_ = lean_unbox_usize(v_depth_852_);
lean_dec(v_depth_852_);
v_res_858_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg(v_depth_boxed_857_, v_keys_853_, v_vals_854_, v_i_855_, v_entries_856_);
lean_dec_ref(v_vals_854_);
lean_dec_ref(v_keys_853_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg___boxed(lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
size_t v_x_4722__boxed_864_; size_t v_x_4723__boxed_865_; lean_object* v_res_866_; 
v_x_4722__boxed_864_ = lean_unbox_usize(v_x_860_);
lean_dec(v_x_860_);
v_x_4723__boxed_865_ = lean_unbox_usize(v_x_861_);
lean_dec(v_x_861_);
v_res_866_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(v_x_859_, v_x_4722__boxed_864_, v_x_4723__boxed_865_, v_x_862_, v_x_863_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0___redArg(lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
size_t v___x_870_; size_t v___x_871_; size_t v___x_872_; uint64_t v___x_873_; size_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; 
v___x_870_ = lean_ptr_addr(v_x_868_);
v___x_871_ = ((size_t)3ULL);
v___x_872_ = lean_usize_shift_right(v___x_870_, v___x_871_);
v___x_873_ = lean_usize_to_uint64(v___x_872_);
v___x_874_ = lean_uint64_to_usize(v___x_873_);
v___x_875_ = ((size_t)1ULL);
v___x_876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(v_x_867_, v___x_874_, v___x_875_, v_x_868_, v_x_869_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg___lam__0(lean_object* v_val_877_, lean_object* v_s_878_){
_start:
{
lean_object* v_vars_879_; lean_object* v_varMap_880_; lean_object* v_varsHistory_881_; lean_object* v_natToIntMap_882_; lean_object* v_natDef_883_; lean_object* v_dvds_884_; lean_object* v_lowers_885_; lean_object* v_uppers_886_; lean_object* v_diseqs_887_; lean_object* v_elimEqs_888_; lean_object* v_elimStack_889_; lean_object* v_occurs_890_; lean_object* v_assignment_891_; lean_object* v_nextCnstrId_892_; uint8_t v_caseSplits_893_; lean_object* v_steps_894_; lean_object* v_penalties_895_; lean_object* v_numReorderRequests_896_; lean_object* v_conflict_x3f_897_; lean_object* v_diseqSplits_898_; lean_object* v_divMod_899_; uint8_t v_usedCommRing_900_; lean_object* v_nonlinearOccs_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_917_; 
v_vars_879_ = lean_ctor_get(v_s_878_, 0);
v_varMap_880_ = lean_ctor_get(v_s_878_, 1);
v_varsHistory_881_ = lean_ctor_get(v_s_878_, 2);
v_natToIntMap_882_ = lean_ctor_get(v_s_878_, 3);
v_natDef_883_ = lean_ctor_get(v_s_878_, 4);
v_dvds_884_ = lean_ctor_get(v_s_878_, 5);
v_lowers_885_ = lean_ctor_get(v_s_878_, 6);
v_uppers_886_ = lean_ctor_get(v_s_878_, 7);
v_diseqs_887_ = lean_ctor_get(v_s_878_, 8);
v_elimEqs_888_ = lean_ctor_get(v_s_878_, 9);
v_elimStack_889_ = lean_ctor_get(v_s_878_, 10);
v_occurs_890_ = lean_ctor_get(v_s_878_, 11);
v_assignment_891_ = lean_ctor_get(v_s_878_, 12);
v_nextCnstrId_892_ = lean_ctor_get(v_s_878_, 13);
v_caseSplits_893_ = lean_ctor_get_uint8(v_s_878_, sizeof(void*)*21);
v_steps_894_ = lean_ctor_get(v_s_878_, 14);
v_penalties_895_ = lean_ctor_get(v_s_878_, 15);
v_numReorderRequests_896_ = lean_ctor_get(v_s_878_, 16);
v_conflict_x3f_897_ = lean_ctor_get(v_s_878_, 17);
v_diseqSplits_898_ = lean_ctor_get(v_s_878_, 18);
v_divMod_899_ = lean_ctor_get(v_s_878_, 19);
v_usedCommRing_900_ = lean_ctor_get_uint8(v_s_878_, sizeof(void*)*21 + 1);
v_nonlinearOccs_901_ = lean_ctor_get(v_s_878_, 20);
v_isSharedCheck_917_ = !lean_is_exclusive(v_s_878_);
if (v_isSharedCheck_917_ == 0)
{
v___x_903_ = v_s_878_;
v_isShared_904_ = v_isSharedCheck_917_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_nonlinearOccs_901_);
lean_inc(v_divMod_899_);
lean_inc(v_diseqSplits_898_);
lean_inc(v_conflict_x3f_897_);
lean_inc(v_numReorderRequests_896_);
lean_inc(v_penalties_895_);
lean_inc(v_steps_894_);
lean_inc(v_nextCnstrId_892_);
lean_inc(v_assignment_891_);
lean_inc(v_occurs_890_);
lean_inc(v_elimStack_889_);
lean_inc(v_elimEqs_888_);
lean_inc(v_diseqs_887_);
lean_inc(v_uppers_886_);
lean_inc(v_lowers_885_);
lean_inc(v_dvds_884_);
lean_inc(v_natDef_883_);
lean_inc(v_natToIntMap_882_);
lean_inc(v_varsHistory_881_);
lean_inc(v_varMap_880_);
lean_inc(v_vars_879_);
lean_dec(v_s_878_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_917_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___y_906_; lean_object* v___x_914_; 
v___x_914_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg(v_penalties_895_, v_val_877_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v___x_915_; 
v___x_915_ = lean_unsigned_to_nat(0u);
v___y_906_ = v___x_915_;
goto v___jp_905_;
}
else
{
lean_object* v_val_916_; 
v_val_916_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_val_916_);
lean_dec_ref_known(v___x_914_, 1);
v___y_906_ = v_val_916_;
goto v___jp_905_;
}
v___jp_905_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_907_ = lean_unsigned_to_nat(1u);
v___x_908_ = lean_nat_add(v___y_906_, v___x_907_);
lean_dec(v___y_906_);
v___x_909_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0___redArg(v_penalties_895_, v_val_877_, v___x_908_);
v___x_910_ = lean_nat_add(v_numReorderRequests_896_, v___x_907_);
lean_dec(v_numReorderRequests_896_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 16, v___x_910_);
lean_ctor_set(v___x_903_, 15, v___x_909_);
v___x_912_ = v___x_903_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_vars_879_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_varMap_880_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_varsHistory_881_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_natToIntMap_882_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_natDef_883_);
lean_ctor_set(v_reuseFailAlloc_913_, 5, v_dvds_884_);
lean_ctor_set(v_reuseFailAlloc_913_, 6, v_lowers_885_);
lean_ctor_set(v_reuseFailAlloc_913_, 7, v_uppers_886_);
lean_ctor_set(v_reuseFailAlloc_913_, 8, v_diseqs_887_);
lean_ctor_set(v_reuseFailAlloc_913_, 9, v_elimEqs_888_);
lean_ctor_set(v_reuseFailAlloc_913_, 10, v_elimStack_889_);
lean_ctor_set(v_reuseFailAlloc_913_, 11, v_occurs_890_);
lean_ctor_set(v_reuseFailAlloc_913_, 12, v_assignment_891_);
lean_ctor_set(v_reuseFailAlloc_913_, 13, v_nextCnstrId_892_);
lean_ctor_set(v_reuseFailAlloc_913_, 14, v_steps_894_);
lean_ctor_set(v_reuseFailAlloc_913_, 15, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_913_, 16, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_913_, 17, v_conflict_x3f_897_);
lean_ctor_set(v_reuseFailAlloc_913_, 18, v_diseqSplits_898_);
lean_ctor_set(v_reuseFailAlloc_913_, 19, v_divMod_899_);
lean_ctor_set(v_reuseFailAlloc_913_, 20, v_nonlinearOccs_901_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*21, v_caseSplits_893_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*21 + 1, v_usedCommRing_900_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg(lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v___x_921_; lean_object* v_reorderRequest_x3f_922_; 
v___x_921_ = lean_st_ref_get(v_a_918_);
v_reorderRequest_x3f_922_ = lean_ctor_get(v___x_921_, 3);
lean_inc(v_reorderRequest_x3f_922_);
lean_dec(v___x_921_);
if (lean_obj_tag(v_reorderRequest_x3f_922_) == 1)
{
lean_object* v_val_923_; lean_object* v___f_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_val_923_ = lean_ctor_get(v_reorderRequest_x3f_922_, 0);
lean_inc(v_val_923_);
lean_dec_ref_known(v_reorderRequest_x3f_922_, 1);
v___f_924_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg___lam__0), 2, 1);
lean_closure_set(v___f_924_, 0, v_val_923_);
v___x_925_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_926_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_925_, v___f_924_, v_a_919_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_935_; 
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_935_ == 0)
{
lean_object* v_unused_936_; 
v_unused_936_ = lean_ctor_get(v___x_926_, 0);
lean_dec(v_unused_936_);
v___x_928_ = v___x_926_;
v_isShared_929_ = v_isSharedCheck_935_;
goto v_resetjp_927_;
}
else
{
lean_dec(v___x_926_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_935_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_930_ = 1;
v___x_931_ = lean_box(v___x_930_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_931_);
v___x_933_ = v___x_928_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
v_a_937_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_926_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_926_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
else
{
uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec(v_reorderRequest_x3f_922_);
v___x_945_ = 0;
v___x_946_ = lean_box(v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg___boxed(lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg(v_a_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec(v_a_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest(uint8_t v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___redArg(v_a_953_, v_a_954_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest___boxed(lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
uint8_t v_a_boxed_979_; lean_object* v_res_980_; 
v_a_boxed_979_ = lean_unbox(v_a_966_);
v_res_980_ = l_Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest(v_a_boxed_979_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0(lean_object* v_00_u03b2_981_, lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v_x_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0___redArg(v_x_982_, v_x_983_, v_x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1(lean_object* v_00_u03b2_986_, lean_object* v_x_987_, lean_object* v_x_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___redArg(v_x_987_, v_x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1___boxed(lean_object* v_00_u03b2_990_, lean_object* v_x_991_, lean_object* v_x_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1(v_00_u03b2_990_, v_x_991_, v_x_992_);
lean_dec_ref(v_x_992_);
lean_dec_ref(v_x_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0(lean_object* v_00_u03b2_994_, lean_object* v_x_995_, size_t v_x_996_, size_t v_x_997_, lean_object* v_x_998_, lean_object* v_x_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___redArg(v_x_995_, v_x_996_, v_x_997_, v_x_998_, v_x_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_){
_start:
{
size_t v_x_5012__boxed_1007_; size_t v_x_5013__boxed_1008_; lean_object* v_res_1009_; 
v_x_5012__boxed_1007_ = lean_unbox_usize(v_x_1003_);
lean_dec(v_x_1003_);
v_x_5013__boxed_1008_ = lean_unbox_usize(v_x_1004_);
lean_dec(v_x_1004_);
v_res_1009_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0(v_00_u03b2_1001_, v_x_1002_, v_x_5012__boxed_1007_, v_x_5013__boxed_1008_, v_x_1005_, v_x_1006_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2(lean_object* v_00_u03b2_1010_, lean_object* v_x_1011_, size_t v_x_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___redArg(v_x_1011_, v_x_1012_, v_x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_, lean_object* v_x_1018_){
_start:
{
size_t v_x_5029__boxed_1019_; lean_object* v_res_1020_; 
v_x_5029__boxed_1019_ = lean_unbox_usize(v_x_1017_);
lean_dec(v_x_1017_);
v_res_1020_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2(v_00_u03b2_1015_, v_x_1016_, v_x_5029__boxed_1019_, v_x_1018_);
lean_dec_ref(v_x_1018_);
lean_dec_ref(v_x_1016_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1021_, lean_object* v_n_1022_, lean_object* v_k_1023_, lean_object* v_v_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1___redArg(v_n_1022_, v_k_1023_, v_v_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1026_, size_t v_depth_1027_, lean_object* v_keys_1028_, lean_object* v_vals_1029_, lean_object* v_heq_1030_, lean_object* v_i_1031_, lean_object* v_entries_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___redArg(v_depth_1027_, v_keys_1028_, v_vals_1029_, v_i_1031_, v_entries_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1034_, lean_object* v_depth_1035_, lean_object* v_keys_1036_, lean_object* v_vals_1037_, lean_object* v_heq_1038_, lean_object* v_i_1039_, lean_object* v_entries_1040_){
_start:
{
size_t v_depth_boxed_1041_; lean_object* v_res_1042_; 
v_depth_boxed_1041_ = lean_unbox_usize(v_depth_1035_);
lean_dec(v_depth_1035_);
v_res_1042_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__2(v_00_u03b2_1034_, v_depth_boxed_1041_, v_keys_1036_, v_vals_1037_, v_heq_1038_, v_i_1039_, v_entries_1040_);
lean_dec_ref(v_vals_1037_);
lean_dec_ref(v_keys_1036_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1043_, lean_object* v_keys_1044_, lean_object* v_vals_1045_, lean_object* v_heq_1046_, lean_object* v_i_1047_, lean_object* v_k_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___redArg(v_keys_1044_, v_vals_1045_, v_i_1047_, v_k_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1050_, lean_object* v_keys_1051_, lean_object* v_vals_1052_, lean_object* v_heq_1053_, lean_object* v_i_1054_, lean_object* v_k_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__1_spec__2_spec__5(v_00_u03b2_1050_, v_keys_1051_, v_vals_1052_, v_heq_1053_, v_i_1054_, v_k_1055_);
lean_dec_ref(v_k_1055_);
lean_dec_ref(v_vals_1052_);
lean_dec_ref(v_keys_1051_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1057_, lean_object* v_x_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_saveReorderRequest_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1058_, v_x_1059_, v_x_1060_, v_x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___lam__0(lean_object* v_s_1063_){
_start:
{
lean_object* v_vars_1064_; lean_object* v_varMap_1065_; lean_object* v_varsHistory_1066_; lean_object* v_natToIntMap_1067_; lean_object* v_natDef_1068_; lean_object* v_dvds_1069_; lean_object* v_lowers_1070_; lean_object* v_uppers_1071_; lean_object* v_diseqs_1072_; lean_object* v_elimEqs_1073_; lean_object* v_elimStack_1074_; lean_object* v_occurs_1075_; lean_object* v_assignment_1076_; lean_object* v_nextCnstrId_1077_; lean_object* v_steps_1078_; lean_object* v_penalties_1079_; lean_object* v_numReorderRequests_1080_; lean_object* v_conflict_x3f_1081_; lean_object* v_diseqSplits_1082_; lean_object* v_divMod_1083_; uint8_t v_usedCommRing_1084_; lean_object* v_nonlinearOccs_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1093_; 
v_vars_1064_ = lean_ctor_get(v_s_1063_, 0);
v_varMap_1065_ = lean_ctor_get(v_s_1063_, 1);
v_varsHistory_1066_ = lean_ctor_get(v_s_1063_, 2);
v_natToIntMap_1067_ = lean_ctor_get(v_s_1063_, 3);
v_natDef_1068_ = lean_ctor_get(v_s_1063_, 4);
v_dvds_1069_ = lean_ctor_get(v_s_1063_, 5);
v_lowers_1070_ = lean_ctor_get(v_s_1063_, 6);
v_uppers_1071_ = lean_ctor_get(v_s_1063_, 7);
v_diseqs_1072_ = lean_ctor_get(v_s_1063_, 8);
v_elimEqs_1073_ = lean_ctor_get(v_s_1063_, 9);
v_elimStack_1074_ = lean_ctor_get(v_s_1063_, 10);
v_occurs_1075_ = lean_ctor_get(v_s_1063_, 11);
v_assignment_1076_ = lean_ctor_get(v_s_1063_, 12);
v_nextCnstrId_1077_ = lean_ctor_get(v_s_1063_, 13);
v_steps_1078_ = lean_ctor_get(v_s_1063_, 14);
v_penalties_1079_ = lean_ctor_get(v_s_1063_, 15);
v_numReorderRequests_1080_ = lean_ctor_get(v_s_1063_, 16);
v_conflict_x3f_1081_ = lean_ctor_get(v_s_1063_, 17);
v_diseqSplits_1082_ = lean_ctor_get(v_s_1063_, 18);
v_divMod_1083_ = lean_ctor_get(v_s_1063_, 19);
v_usedCommRing_1084_ = lean_ctor_get_uint8(v_s_1063_, sizeof(void*)*21 + 1);
v_nonlinearOccs_1085_ = lean_ctor_get(v_s_1063_, 20);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_s_1063_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1087_ = v_s_1063_;
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_nonlinearOccs_1085_);
lean_inc(v_divMod_1083_);
lean_inc(v_diseqSplits_1082_);
lean_inc(v_conflict_x3f_1081_);
lean_inc(v_numReorderRequests_1080_);
lean_inc(v_penalties_1079_);
lean_inc(v_steps_1078_);
lean_inc(v_nextCnstrId_1077_);
lean_inc(v_assignment_1076_);
lean_inc(v_occurs_1075_);
lean_inc(v_elimStack_1074_);
lean_inc(v_elimEqs_1073_);
lean_inc(v_diseqs_1072_);
lean_inc(v_uppers_1071_);
lean_inc(v_lowers_1070_);
lean_inc(v_dvds_1069_);
lean_inc(v_natDef_1068_);
lean_inc(v_natToIntMap_1067_);
lean_inc(v_varsHistory_1066_);
lean_inc(v_varMap_1065_);
lean_inc(v_vars_1064_);
lean_dec(v_s_1063_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
uint8_t v___x_1089_; lean_object* v___x_1091_; 
v___x_1089_ = 1;
if (v_isShared_1088_ == 0)
{
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_vars_1064_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_varMap_1065_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_varsHistory_1066_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_natToIntMap_1067_);
lean_ctor_set(v_reuseFailAlloc_1092_, 4, v_natDef_1068_);
lean_ctor_set(v_reuseFailAlloc_1092_, 5, v_dvds_1069_);
lean_ctor_set(v_reuseFailAlloc_1092_, 6, v_lowers_1070_);
lean_ctor_set(v_reuseFailAlloc_1092_, 7, v_uppers_1071_);
lean_ctor_set(v_reuseFailAlloc_1092_, 8, v_diseqs_1072_);
lean_ctor_set(v_reuseFailAlloc_1092_, 9, v_elimEqs_1073_);
lean_ctor_set(v_reuseFailAlloc_1092_, 10, v_elimStack_1074_);
lean_ctor_set(v_reuseFailAlloc_1092_, 11, v_occurs_1075_);
lean_ctor_set(v_reuseFailAlloc_1092_, 12, v_assignment_1076_);
lean_ctor_set(v_reuseFailAlloc_1092_, 13, v_nextCnstrId_1077_);
lean_ctor_set(v_reuseFailAlloc_1092_, 14, v_steps_1078_);
lean_ctor_set(v_reuseFailAlloc_1092_, 15, v_penalties_1079_);
lean_ctor_set(v_reuseFailAlloc_1092_, 16, v_numReorderRequests_1080_);
lean_ctor_set(v_reuseFailAlloc_1092_, 17, v_conflict_x3f_1081_);
lean_ctor_set(v_reuseFailAlloc_1092_, 18, v_diseqSplits_1082_);
lean_ctor_set(v_reuseFailAlloc_1092_, 19, v_divMod_1083_);
lean_ctor_set(v_reuseFailAlloc_1092_, 20, v_nonlinearOccs_1085_);
lean_ctor_set_uint8(v_reuseFailAlloc_1092_, sizeof(void*)*21 + 1, v_usedCommRing_1084_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_ctor_set_uint8(v___x_1091_, sizeof(void*)*21, v___x_1089_);
return v___x_1091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(lean_object* v___y_1094_){
_start:
{
lean_object* v___x_1096_; lean_object* v_ngen_1097_; lean_object* v_namePrefix_1098_; lean_object* v_idx_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1129_; 
v___x_1096_ = lean_st_ref_get(v___y_1094_);
v_ngen_1097_ = lean_ctor_get(v___x_1096_, 2);
lean_inc_ref(v_ngen_1097_);
lean_dec(v___x_1096_);
v_namePrefix_1098_ = lean_ctor_get(v_ngen_1097_, 0);
v_idx_1099_ = lean_ctor_get(v_ngen_1097_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_ngen_1097_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1101_ = v_ngen_1097_;
v_isShared_1102_ = v_isSharedCheck_1129_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_idx_1099_);
lean_inc(v_namePrefix_1098_);
lean_dec(v_ngen_1097_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1129_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_r_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
lean_inc(v_idx_1099_);
lean_inc(v_namePrefix_1098_);
v_r_1103_ = l_Lean_Name_num___override(v_namePrefix_1098_, v_idx_1099_);
v___x_1104_ = lean_unsigned_to_nat(1u);
v___x_1105_ = lean_nat_add(v_idx_1099_, v___x_1104_);
lean_dec(v_idx_1099_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v___x_1105_);
v___x_1107_ = v___x_1101_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_namePrefix_1098_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1108_; lean_object* v_env_1109_; lean_object* v_nextMacroScope_1110_; lean_object* v_auxDeclNGen_1111_; lean_object* v_traceState_1112_; lean_object* v_cache_1113_; lean_object* v_recordedDeps_1114_; lean_object* v_messages_1115_; lean_object* v_infoState_1116_; lean_object* v_snapshotTasks_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1126_; 
v___x_1108_ = lean_st_ref_take(v___y_1094_);
v_env_1109_ = lean_ctor_get(v___x_1108_, 0);
v_nextMacroScope_1110_ = lean_ctor_get(v___x_1108_, 1);
v_auxDeclNGen_1111_ = lean_ctor_get(v___x_1108_, 3);
v_traceState_1112_ = lean_ctor_get(v___x_1108_, 4);
v_cache_1113_ = lean_ctor_get(v___x_1108_, 5);
v_recordedDeps_1114_ = lean_ctor_get(v___x_1108_, 6);
v_messages_1115_ = lean_ctor_get(v___x_1108_, 7);
v_infoState_1116_ = lean_ctor_get(v___x_1108_, 8);
v_snapshotTasks_1117_ = lean_ctor_get(v___x_1108_, 9);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v___x_1108_, 2);
lean_dec(v_unused_1127_);
v___x_1119_ = v___x_1108_;
v_isShared_1120_ = v_isSharedCheck_1126_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_snapshotTasks_1117_);
lean_inc(v_infoState_1116_);
lean_inc(v_messages_1115_);
lean_inc(v_recordedDeps_1114_);
lean_inc(v_cache_1113_);
lean_inc(v_traceState_1112_);
lean_inc(v_auxDeclNGen_1111_);
lean_inc(v_nextMacroScope_1110_);
lean_inc(v_env_1109_);
lean_dec(v___x_1108_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1126_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 2, v___x_1107_);
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_env_1109_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_nextMacroScope_1110_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1125_, 3, v_auxDeclNGen_1111_);
lean_ctor_set(v_reuseFailAlloc_1125_, 4, v_traceState_1112_);
lean_ctor_set(v_reuseFailAlloc_1125_, 5, v_cache_1113_);
lean_ctor_set(v_reuseFailAlloc_1125_, 6, v_recordedDeps_1114_);
lean_ctor_set(v_reuseFailAlloc_1125_, 7, v_messages_1115_);
lean_ctor_set(v_reuseFailAlloc_1125_, 8, v_infoState_1116_);
lean_ctor_set(v_reuseFailAlloc_1125_, 9, v_snapshotTasks_1117_);
v___x_1122_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_st_ref_put(v___y_1094_, v___x_1122_);
v___x_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1124_, 0, v_r_1103_);
return v___x_1124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg___boxed(lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_1130_);
lean_dec(v___y_1130_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(uint8_t v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
v___x_1146_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_1144_);
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0___boxed(lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
uint8_t v___y_12228__boxed_1168_; lean_object* v_res_1169_; 
v___y_12228__boxed_1168_ = lean_unbox(v___y_1155_);
v_res_1169_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(v___y_12228__boxed_1168_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec(v___y_1156_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase(lean_object* v_kind_1171_, uint8_t v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v___f_1185_; lean_object* v___x_1186_; 
v___f_1185_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0));
v___x_1186_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1188_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1186_, 1);
v___x_1188_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1174_, v_a_1182_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1190_; lean_object* v_cases_1191_; uint8_t v_precise_1192_; lean_object* v_decVars_1193_; lean_object* v_steps_1194_; lean_object* v_reorderRequest_x3f_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1224_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1188_, 1);
v___x_1190_ = lean_st_ref_take(v_a_1173_);
v_cases_1191_ = lean_ctor_get(v___x_1190_, 0);
v_precise_1192_ = lean_ctor_get_uint8(v___x_1190_, sizeof(void*)*4);
v_decVars_1193_ = lean_ctor_get(v___x_1190_, 1);
v_steps_1194_ = lean_ctor_get(v___x_1190_, 2);
v_reorderRequest_x3f_1195_ = lean_ctor_get(v___x_1190_, 3);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1197_ = v___x_1190_;
v_isShared_1198_ = v_isSharedCheck_1224_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_reorderRequest_x3f_1195_);
lean_inc(v_steps_1194_);
lean_inc(v_decVars_1193_);
lean_inc(v_cases_1191_);
lean_dec(v___x_1190_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1224_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
lean_inc_n(v_a_1187_, 2);
v___x_1199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1199_, 0, v_kind_1171_);
lean_ctor_set(v___x_1199_, 1, v_a_1187_);
lean_ctor_set(v___x_1199_, 2, v_a_1189_);
v___x_1200_ = l_Lean_PersistentArray_push___redArg(v_cases_1191_, v___x_1199_);
v___x_1201_ = l_Lean_FVarIdSet_insert(v_decVars_1193_, v_a_1187_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 1, v___x_1201_);
lean_ctor_set(v___x_1197_, 0, v___x_1200_);
v___x_1203_ = v___x_1197_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v_steps_1194_);
lean_ctor_set(v_reuseFailAlloc_1223_, 3, v_reorderRequest_x3f_1195_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, sizeof(void*)*4, v_precise_1192_);
v___x_1203_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = lean_st_ref_put(v_a_1173_, v___x_1203_);
v___x_1205_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1206_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1205_, v___f_1185_, v_a_1174_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v___x_1206_, 0);
lean_dec(v_unused_1214_);
v___x_1208_ = v___x_1206_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_dec(v___x_1206_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v_a_1187_);
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1187_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v_a_1187_);
v_a_1215_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1206_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1206_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec(v_a_1187_);
lean_dec_ref(v_kind_1171_);
v_a_1225_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1188_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1188_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
lean_dec_ref(v_kind_1171_);
return v___x_1186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___boxed(lean_object* v_kind_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
uint8_t v_a_boxed_1247_; lean_object* v_res_1248_; 
v_a_boxed_1247_ = lean_unbox(v_a_1234_);
v_res_1248_ = l_Lean_Meta_Grind_Arith_Cutsat_mkCase(v_kind_1233_, v_a_boxed_1247_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec(v_a_1235_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(uint8_t v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___boxed(lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
uint8_t v___y_12380__boxed_1276_; lean_object* v_res_1277_; 
v___y_12380__boxed_1276_ = lean_unbox(v___y_1263_);
v_res_1277_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(v___y_12380__boxed_1276_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec(v___y_1264_);
return v_res_1277_;
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
