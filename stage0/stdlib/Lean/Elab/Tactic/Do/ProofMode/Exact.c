// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Exact
// Imports: public import Lean.Elab.Tactic.Do.ProofMode.Basic public import Lean.Elab.Tactic.Do.ProofMode.Focus public import Lean.Elab.Tactic.ElabTerm
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Exact"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assumption"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4_value),LEAN_SCALAR_PTR_LITERAL(247, 90, 235, 148, 72, 45, 123, 55)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__5_value),LEAN_SCALAR_PTR_LITERAL(117, 200, 132, 33, 80, 180, 87, 145)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "mexact tactic failed, hypothesis "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = " is not definitionally equal to "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "PropAsSPredTautology"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__3_value),LEAN_SCALAR_PTR_LITERAL(48, 191, 216, 96, 0, 209, 179, 40)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "from_tautology"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4_value),LEAN_SCALAR_PTR_LITERAL(247, 90, 235, 148, 72, 45, 123, 55)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__5_value),LEAN_SCALAR_PTR_LITERAL(63, 82, 124, 192, 70, 8, 53, 251)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "mexact tactic failed, "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = " is not an SPred tautology"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "not in proof mode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mexact"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 177, 11, 252, 148, 218, 54, 90)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabMExact"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 228, 61, 69, 215, 146, 157, 115)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_ref_29_ = lean_ctor_get(v___y_26_, 5);
v___x_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(v_msg_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
lean_inc(v_ref_29_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_ref_29_);
lean_ctor_set(v___x_35_, 1, v_a_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set_tag(v___x_33_, 1);
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg___boxed(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__7));
v___x_62_ = l_Lean_stringToMessageData(v___x_61_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__9));
v___x_65_ = l_Lean_stringToMessageData(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(lean_object* v_goal_66_, lean_object* v_hyp_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = l_Lean_Syntax_getId(v_hyp_67_);
lean_inc_ref(v_goal_66_);
v___x_74_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(v_goal_66_, v___x_73_);
lean_dec(v___x_73_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v_hyp_67_);
lean_dec_ref(v_goal_66_);
v___x_75_ = lean_box(0);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
else
{
lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_140_; 
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; 
v_unused_141_ = lean_ctor_get(v___x_74_, 0);
lean_dec(v_unused_141_);
v___x_78_ = v___x_74_;
v_isShared_79_ = v_isSharedCheck_140_;
goto v_resetjp_77_;
}
else
{
lean_dec(v___x_74_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_140_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; 
lean_inc(v_hyp_67_);
lean_inc_ref(v_goal_66_);
v___x_80_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_goal_66_, v_hyp_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_131_; 
v_a_81_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_131_ == 0)
{
v___x_83_ = v___x_80_;
v_isShared_84_ = v_isSharedCheck_131_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_80_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_131_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v_u_85_; lean_object* v_00_u03c3s_86_; lean_object* v_hyps_87_; lean_object* v_target_88_; lean_object* v_focusHyp_89_; lean_object* v_restHyps_90_; lean_object* v_proof_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_104_; 
v_u_85_ = lean_ctor_get(v_goal_66_, 0);
lean_inc(v_u_85_);
v_00_u03c3s_86_ = lean_ctor_get(v_goal_66_, 1);
lean_inc_ref(v_00_u03c3s_86_);
v_hyps_87_ = lean_ctor_get(v_goal_66_, 2);
lean_inc_ref(v_hyps_87_);
v_target_88_ = lean_ctor_get(v_goal_66_, 3);
lean_inc_ref_n(v_target_88_, 3);
lean_dec_ref(v_goal_66_);
v_focusHyp_89_ = lean_ctor_get(v_a_81_, 0);
lean_inc_ref(v_focusHyp_89_);
v_restHyps_90_ = lean_ctor_get(v_a_81_, 1);
lean_inc_ref(v_restHyps_90_);
v_proof_91_ = lean_ctor_get(v_a_81_, 2);
lean_inc_ref(v_proof_91_);
lean_dec(v_a_81_);
v___x_92_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6));
v___x_93_ = lean_box(0);
v___x_94_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_94_, 0, v_u_85_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = l_Lean_mkConst(v___x_92_, v___x_94_);
v___x_96_ = l_Lean_mkApp5(v___x_95_, v_00_u03c3s_86_, v_hyps_87_, v_restHyps_90_, v_target_88_, v_proof_91_);
v___x_104_ = l_Lean_Meta_isExprDefEq(v_focusHyp_89_, v_target_88_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; uint8_t v___x_106_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
v___x_106_ = lean_unbox(v_a_105_);
lean_dec(v_a_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_dec_ref(v___x_96_);
lean_del_object(v___x_83_);
lean_del_object(v___x_78_);
v___x_107_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8);
v___x_108_ = l_Lean_MessageData_ofSyntax(v_hyp_67_);
v___x_109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_107_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10);
v___x_111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = l_Lean_MessageData_ofExpr(v_target_88_);
v___x_113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(v___x_113_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
else
{
lean_dec_ref(v_target_88_);
lean_dec(v_hyp_67_);
goto v___jp_97_;
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec_ref(v___x_96_);
lean_dec_ref(v_target_88_);
lean_del_object(v___x_83_);
lean_del_object(v___x_78_);
lean_dec(v_hyp_67_);
v_a_123_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_104_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_104_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
v___jp_97_:
{
lean_object* v___x_99_; 
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v___x_96_);
v___x_99_ = v___x_78_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_96_);
v___x_99_ = v_reuseFailAlloc_103_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_101_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_99_);
v___x_101_ = v___x_83_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
lean_del_object(v___x_78_);
lean_dec(v_hyp_67_);
lean_dec_ref(v_goal_66_);
v_a_132_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_80_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_80_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___boxed(lean_object* v_goal_142_, lean_object* v_hyp_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(v_goal_142_, v_hyp_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0(lean_object* v_00_u03b1_150_, lean_object* v_msg_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(v_msg_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___boxed(lean_object* v_00_u03b1_158_, lean_object* v_msg_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0(v_00_u03b1_158_, v_msg_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(lean_object* v_msg_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_ref_172_; lean_object* v___x_173_; lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_182_; 
v_ref_172_ = lean_ctor_get(v___y_169_, 5);
v___x_173_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(v_msg_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_182_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_180_; 
lean_inc(v_ref_172_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v_ref_172_);
lean_ctor_set(v___x_178_, 1, v_a_174_);
if (v_isShared_177_ == 0)
{
lean_ctor_set_tag(v___x_176_, 1);
lean_ctor_set(v___x_176_, 0, v___x_178_);
v___x_180_ = v___x_176_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg___boxed(lean_object* v_msg_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(v_msg_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
return v_res_189_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_box(0);
v___x_191_ = l_Lean_mkSort(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0);
v___x_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__7));
v___x_215_ = l_Lean_stringToMessageData(v___x_214_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__9));
v___x_218_ = l_Lean_stringToMessageData(v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(lean_object* v_goal_219_, lean_object* v_hyp_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v___x_230_; uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_230_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1);
v___x_231_ = 0;
v___x_232_ = lean_box(0);
v___x_233_ = l_Lean_Meta_mkFreshExprMVar(v___x_230_, v___x_231_, v___x_232_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_293_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_293_ == 0)
{
v___x_236_ = v___x_233_;
v_isShared_237_ = v_isSharedCheck_293_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_293_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
lean_inc(v_a_234_);
if (v_isShared_237_ == 0)
{
lean_ctor_set_tag(v___x_236_, 1);
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_292_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
uint8_t v___x_240_; lean_object* v___x_241_; 
v___x_240_ = 0;
lean_inc(v_hyp_220_);
v___x_241_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v_hyp_220_, v___x_239_, v___x_240_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_291_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_291_ == 0)
{
v___x_244_ = v___x_241_;
v_isShared_245_ = v_isSharedCheck_291_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_241_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_291_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v_u_246_; lean_object* v_00_u03c3s_247_; lean_object* v_hyps_248_; lean_object* v_target_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v_u_246_ = lean_ctor_get(v_goal_219_, 0);
lean_inc(v_u_246_);
v_00_u03c3s_247_ = lean_ctor_get(v_goal_219_, 1);
lean_inc_ref_n(v_00_u03c3s_247_, 2);
v_hyps_248_ = lean_ctor_get(v_goal_219_, 2);
lean_inc_ref(v_hyps_248_);
v_target_249_ = lean_ctor_get(v_goal_219_, 3);
lean_inc_ref(v_target_249_);
lean_dec_ref(v_goal_219_);
v___x_250_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2));
v___x_251_ = lean_box(0);
v___x_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_252_, 0, v_u_246_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
lean_inc_ref(v___x_252_);
v___x_253_ = l_Lean_mkConst(v___x_250_, v___x_252_);
v___x_254_ = l_Lean_Expr_app___override(v___x_253_, v_00_u03c3s_247_);
if (v_isShared_245_ == 0)
{
lean_ctor_set_tag(v___x_244_, 1);
lean_ctor_set(v___x_244_, 0, v___x_254_);
v___x_256_ = v___x_244_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_290_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Meta_mkFreshExprMVar(v___x_256_, v___x_231_, v___x_232_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref_known(v___x_257_, 1);
v___x_259_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4));
lean_inc_ref(v___x_252_);
v___x_260_ = l_Lean_mkConst(v___x_259_, v___x_252_);
lean_inc_ref(v_00_u03c3s_247_);
lean_inc(v_a_234_);
v___x_261_ = l_Lean_mkApp3(v___x_260_, v_a_234_, v_00_u03c3s_247_, v_a_258_);
v___x_262_ = lean_box(0);
v___x_263_ = l_Lean_Meta_synthInstance_x3f(v___x_261_, v___x_262_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_281_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_281_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_281_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_281_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
if (lean_obj_tag(v_a_264_) == 1)
{
lean_object* v_val_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
lean_dec(v_hyp_220_);
v_val_268_ = lean_ctor_get(v_a_264_, 0);
lean_inc(v_val_268_);
lean_dec_ref_known(v_a_264_, 1);
v___x_269_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6));
v___x_270_ = l_Lean_mkConst(v___x_269_, v___x_252_);
v___x_271_ = l_Lean_mkApp6(v___x_270_, v_00_u03c3s_247_, v_a_234_, v_hyps_248_, v_target_249_, v_val_268_, v_a_242_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_271_);
v___x_273_ = v___x_266_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
else
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
lean_del_object(v___x_266_);
lean_dec(v_a_264_);
lean_dec_ref_known(v___x_252_, 2);
lean_dec_ref(v_target_249_);
lean_dec_ref(v_hyps_248_);
lean_dec_ref(v_00_u03c3s_247_);
lean_dec(v_a_242_);
lean_dec(v_a_234_);
v___x_275_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8);
v___x_276_ = l_Lean_MessageData_ofSyntax(v_hyp_220_);
v___x_277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10);
v___x_279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(v___x_279_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
return v___x_280_;
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
lean_dec_ref_known(v___x_252_, 2);
lean_dec_ref(v_target_249_);
lean_dec_ref(v_hyps_248_);
lean_dec_ref(v_00_u03c3s_247_);
lean_dec(v_a_242_);
lean_dec(v_a_234_);
lean_dec(v_hyp_220_);
v_a_282_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_263_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_263_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_252_, 2);
lean_dec_ref(v_target_249_);
lean_dec_ref(v_hyps_248_);
lean_dec_ref(v_00_u03c3s_247_);
lean_dec(v_a_242_);
lean_dec(v_a_234_);
lean_dec(v_hyp_220_);
return v___x_257_;
}
}
}
}
else
{
lean_dec(v_a_234_);
lean_dec(v_hyp_220_);
lean_dec_ref(v_goal_219_);
return v___x_241_;
}
}
}
}
else
{
lean_dec(v_hyp_220_);
lean_dec_ref(v_goal_219_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___boxed(lean_object* v_goal_294_, lean_object* v_hyp_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(v_goal_294_, v_hyp_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0(lean_object* v_00_u03b1_306_, lean_object* v_msg_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(v_msg_307_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___boxed(lean_object* v_00_u03b1_318_, lean_object* v_msg_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0(v_00_u03b1_318_, v_msg_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_329_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = lean_box(0);
v___x_331_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg(){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0);
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___boxed(lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg();
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0(lean_object* v_00_u03b1_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg();
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___boxed(lean_object* v_00_u03b1_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0(v_00_u03b1_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(lean_object* v_e_360_, lean_object* v___y_361_){
_start:
{
uint8_t v___x_363_; uint8_t v___x_364_; 
v___x_363_ = l_Lean_Expr_hasMVar(v_e_360_);
v___x_364_ = lean_bool_not(v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v_mctx_366_; lean_object* v___x_367_; lean_object* v_fst_368_; lean_object* v_snd_369_; lean_object* v___x_370_; lean_object* v_cache_371_; lean_object* v_zetaDeltaFVarIds_372_; lean_object* v_postponed_373_; lean_object* v_diag_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_383_; 
v___x_365_ = lean_st_ref_get(v___y_361_);
v_mctx_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc_ref(v_mctx_366_);
lean_dec(v___x_365_);
v___x_367_ = l_Lean_instantiateMVarsCore(v_mctx_366_, v_e_360_);
v_fst_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_fst_368_);
v_snd_369_ = lean_ctor_get(v___x_367_, 1);
lean_inc(v_snd_369_);
lean_dec_ref(v___x_367_);
v___x_370_ = lean_st_ref_take(v___y_361_);
v_cache_371_ = lean_ctor_get(v___x_370_, 1);
v_zetaDeltaFVarIds_372_ = lean_ctor_get(v___x_370_, 2);
v_postponed_373_ = lean_ctor_get(v___x_370_, 3);
v_diag_374_ = lean_ctor_get(v___x_370_, 4);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v___x_370_, 0);
lean_dec(v_unused_384_);
v___x_376_ = v___x_370_;
v_isShared_377_ = v_isSharedCheck_383_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_diag_374_);
lean_inc(v_postponed_373_);
lean_inc(v_zetaDeltaFVarIds_372_);
lean_inc(v_cache_371_);
lean_dec(v___x_370_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_383_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v_snd_369_);
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_snd_369_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_cache_371_);
lean_ctor_set(v_reuseFailAlloc_382_, 2, v_zetaDeltaFVarIds_372_);
lean_ctor_set(v_reuseFailAlloc_382_, 3, v_postponed_373_);
lean_ctor_set(v_reuseFailAlloc_382_, 4, v_diag_374_);
v___x_379_ = v_reuseFailAlloc_382_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_st_ref_set(v___y_361_, v___x_379_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v_fst_368_);
return v___x_381_;
}
}
}
else
{
lean_object* v___x_385_; 
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v_e_360_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg___boxed(lean_object* v_e_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(v_e_386_, v___y_387_);
lean_dec(v___y_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1(lean_object* v_e_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(v_e_390_, v___y_396_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___boxed(lean_object* v_e_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1(v_e_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0(lean_object* v_x_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; 
lean_inc(v___y_416_);
lean_inc_ref(v___y_415_);
lean_inc(v___y_414_);
lean_inc_ref(v___y_413_);
v___x_422_ = lean_apply_9(v_x_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, lean_box(0));
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0___boxed(lean_object* v_x_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0(v_x_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(lean_object* v_mvarId_434_, lean_object* v_x_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___f_445_; lean_object* v___x_446_; 
lean_inc(v___y_439_);
lean_inc_ref(v___y_438_);
lean_inc(v___y_437_);
lean_inc_ref(v___y_436_);
v___f_445_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_445_, 0, v_x_435_);
lean_closure_set(v___f_445_, 1, v___y_436_);
lean_closure_set(v___f_445_, 2, v___y_437_);
lean_closure_set(v___f_445_, 3, v___y_438_);
lean_closure_set(v___f_445_, 4, v___y_439_);
v___x_446_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_434_, v___f_445_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
if (lean_obj_tag(v___x_446_) == 0)
{
return v___x_446_;
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___boxed(lean_object* v_mvarId_455_, lean_object* v_x_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(v_mvarId_455_, v_x_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3(lean_object* v_00_u03b1_467_, lean_object* v_mvarId_468_, lean_object* v_x_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(v_mvarId_468_, v_x_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___boxed(lean_object* v_00_u03b1_480_, lean_object* v_mvarId_481_, lean_object* v_x_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3(v_00_u03b1_480_, v_mvarId_481_, v_x_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_493_, lean_object* v_x_494_, lean_object* v_x_495_, lean_object* v_x_496_){
_start:
{
lean_object* v_ks_497_; lean_object* v_vs_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_522_; 
v_ks_497_ = lean_ctor_get(v_x_493_, 0);
v_vs_498_ = lean_ctor_get(v_x_493_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_x_493_);
if (v_isSharedCheck_522_ == 0)
{
v___x_500_ = v_x_493_;
v_isShared_501_ = v_isSharedCheck_522_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_vs_498_);
lean_inc(v_ks_497_);
lean_dec(v_x_493_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_522_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = lean_array_get_size(v_ks_497_);
v___x_503_ = lean_nat_dec_lt(v_x_494_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
lean_dec(v_x_494_);
v___x_504_ = lean_array_push(v_ks_497_, v_x_495_);
v___x_505_ = lean_array_push(v_vs_498_, v_x_496_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v___x_505_);
lean_ctor_set(v___x_500_, 0, v___x_504_);
v___x_507_ = v___x_500_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v___x_505_);
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
lean_object* v_k_x27_509_; uint8_t v___x_510_; 
v_k_x27_509_ = lean_array_fget_borrowed(v_ks_497_, v_x_494_);
v___x_510_ = l_Lean_instBEqMVarId_beq(v_x_495_, v_k_x27_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_512_; 
if (v_isShared_501_ == 0)
{
v___x_512_ = v___x_500_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_ks_497_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_vs_498_);
v___x_512_ = v_reuseFailAlloc_516_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_nat_add(v_x_494_, v___x_513_);
lean_dec(v_x_494_);
v_x_493_ = v___x_512_;
v_x_494_ = v___x_514_;
goto _start;
}
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_517_ = lean_array_fset(v_ks_497_, v_x_494_, v_x_495_);
v___x_518_ = lean_array_fset(v_vs_498_, v_x_494_, v_x_496_);
lean_dec(v_x_494_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v___x_518_);
lean_ctor_set(v___x_500_, 0, v___x_517_);
v___x_520_ = v___x_500_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5___redArg(lean_object* v_n_523_, lean_object* v_k_524_, lean_object* v_v_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(v_n_523_, v___x_526_, v_k_524_, v_v_525_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(lean_object* v_x_529_, size_t v_x_530_, size_t v_x_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
if (lean_obj_tag(v_x_529_) == 0)
{
lean_object* v_es_534_; size_t v___x_535_; size_t v___x_536_; lean_object* v_j_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_es_534_ = lean_ctor_get(v_x_529_, 0);
v___x_535_ = ((size_t)31ULL);
v___x_536_ = lean_usize_land(v_x_530_, v___x_535_);
v_j_537_ = lean_usize_to_nat(v___x_536_);
v___x_538_ = lean_array_get_size(v_es_534_);
v___x_539_ = lean_nat_dec_lt(v_j_537_, v___x_538_);
if (v___x_539_ == 0)
{
lean_dec(v_j_537_);
lean_dec(v_x_533_);
lean_dec(v_x_532_);
return v_x_529_;
}
else
{
lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_578_; 
lean_inc_ref(v_es_534_);
v_isSharedCheck_578_ = !lean_is_exclusive(v_x_529_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v_x_529_, 0);
lean_dec(v_unused_579_);
v___x_541_ = v_x_529_;
v_isShared_542_ = v_isSharedCheck_578_;
goto v_resetjp_540_;
}
else
{
lean_dec(v_x_529_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_578_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_v_543_; lean_object* v___x_544_; lean_object* v_xs_x27_545_; lean_object* v___y_547_; 
v_v_543_ = lean_array_fget(v_es_534_, v_j_537_);
v___x_544_ = lean_box(0);
v_xs_x27_545_ = lean_array_fset(v_es_534_, v_j_537_, v___x_544_);
switch(lean_obj_tag(v_v_543_))
{
case 0:
{
lean_object* v_key_552_; lean_object* v_val_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_563_; 
v_key_552_ = lean_ctor_get(v_v_543_, 0);
v_val_553_ = lean_ctor_get(v_v_543_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_v_543_);
if (v_isSharedCheck_563_ == 0)
{
v___x_555_ = v_v_543_;
v_isShared_556_ = v_isSharedCheck_563_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_val_553_);
lean_inc(v_key_552_);
lean_dec(v_v_543_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_563_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
uint8_t v___x_557_; 
v___x_557_ = l_Lean_instBEqMVarId_beq(v_x_532_, v_key_552_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_del_object(v___x_555_);
v___x_558_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_552_, v_val_553_, v_x_532_, v_x_533_);
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
v___y_547_ = v___x_559_;
goto v___jp_546_;
}
else
{
lean_object* v___x_561_; 
lean_dec(v_val_553_);
lean_dec(v_key_552_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v_x_533_);
lean_ctor_set(v___x_555_, 0, v_x_532_);
v___x_561_ = v___x_555_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_x_532_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_x_533_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
v___y_547_ = v___x_561_;
goto v___jp_546_;
}
}
}
}
case 1:
{
lean_object* v_node_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_576_; 
v_node_564_ = lean_ctor_get(v_v_543_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v_v_543_);
if (v_isSharedCheck_576_ == 0)
{
v___x_566_ = v_v_543_;
v_isShared_567_ = v_isSharedCheck_576_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_node_564_);
lean_dec(v_v_543_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_576_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
size_t v___x_568_; size_t v___x_569_; size_t v___x_570_; size_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_568_ = ((size_t)5ULL);
v___x_569_ = lean_usize_shift_right(v_x_530_, v___x_568_);
v___x_570_ = ((size_t)1ULL);
v___x_571_ = lean_usize_add(v_x_531_, v___x_570_);
v___x_572_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_node_564_, v___x_569_, v___x_571_, v_x_532_, v_x_533_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_572_);
v___x_574_ = v___x_566_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
v___y_547_ = v___x_574_;
goto v___jp_546_;
}
}
}
default: 
{
lean_object* v___x_577_; 
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v_x_532_);
lean_ctor_set(v___x_577_, 1, v_x_533_);
v___y_547_ = v___x_577_;
goto v___jp_546_;
}
}
v___jp_546_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = lean_array_fset(v_xs_x27_545_, v_j_537_, v___y_547_);
lean_dec(v_j_537_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_548_);
v___x_550_ = v___x_541_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
else
{
lean_object* v_ks_580_; lean_object* v_vs_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_601_; 
v_ks_580_ = lean_ctor_get(v_x_529_, 0);
v_vs_581_ = lean_ctor_get(v_x_529_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v_x_529_);
if (v_isSharedCheck_601_ == 0)
{
v___x_583_ = v_x_529_;
v_isShared_584_ = v_isSharedCheck_601_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_vs_581_);
lean_inc(v_ks_580_);
lean_dec(v_x_529_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_601_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_ks_580_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_vs_581_);
v___x_586_ = v_reuseFailAlloc_600_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v_newNode_587_; uint8_t v___y_589_; size_t v___x_595_; uint8_t v___x_596_; 
v_newNode_587_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5___redArg(v___x_586_, v_x_532_, v_x_533_);
v___x_595_ = ((size_t)7ULL);
v___x_596_ = lean_usize_dec_le(v___x_595_, v_x_531_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_597_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_587_);
v___x_598_ = lean_unsigned_to_nat(4u);
v___x_599_ = lean_nat_dec_lt(v___x_597_, v___x_598_);
lean_dec(v___x_597_);
v___y_589_ = v___x_599_;
goto v___jp_588_;
}
else
{
v___y_589_ = v___x_596_;
goto v___jp_588_;
}
v___jp_588_:
{
if (v___y_589_ == 0)
{
lean_object* v_ks_590_; lean_object* v_vs_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_ks_590_ = lean_ctor_get(v_newNode_587_, 0);
lean_inc_ref(v_ks_590_);
v_vs_591_ = lean_ctor_get(v_newNode_587_, 1);
lean_inc_ref(v_vs_591_);
lean_dec_ref(v_newNode_587_);
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_594_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg(v_x_531_, v_ks_590_, v_vs_591_, v___x_592_, v___x_593_);
lean_dec_ref(v_vs_591_);
lean_dec_ref(v_ks_590_);
return v___x_594_;
}
else
{
return v_newNode_587_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg(size_t v_depth_602_, lean_object* v_keys_603_, lean_object* v_vals_604_, lean_object* v_i_605_, lean_object* v_entries_606_){
_start:
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = lean_array_get_size(v_keys_603_);
v___x_608_ = lean_nat_dec_lt(v_i_605_, v___x_607_);
if (v___x_608_ == 0)
{
lean_dec(v_i_605_);
return v_entries_606_;
}
else
{
lean_object* v_k_609_; lean_object* v_v_610_; uint64_t v___x_611_; size_t v_h_612_; size_t v___x_613_; lean_object* v___x_614_; size_t v___x_615_; size_t v___x_616_; size_t v___x_617_; size_t v_h_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_k_609_ = lean_array_fget_borrowed(v_keys_603_, v_i_605_);
v_v_610_ = lean_array_fget_borrowed(v_vals_604_, v_i_605_);
v___x_611_ = l_Lean_instHashableMVarId_hash(v_k_609_);
v_h_612_ = lean_uint64_to_usize(v___x_611_);
v___x_613_ = ((size_t)5ULL);
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = ((size_t)1ULL);
v___x_616_ = lean_usize_sub(v_depth_602_, v___x_615_);
v___x_617_ = lean_usize_mul(v___x_613_, v___x_616_);
v_h_618_ = lean_usize_shift_right(v_h_612_, v___x_617_);
v___x_619_ = lean_nat_add(v_i_605_, v___x_614_);
lean_dec(v_i_605_);
lean_inc(v_v_610_);
lean_inc(v_k_609_);
v___x_620_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_entries_606_, v_h_618_, v_depth_602_, v_k_609_, v_v_610_);
v_i_605_ = v___x_619_;
v_entries_606_ = v___x_620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_depth_622_, lean_object* v_keys_623_, lean_object* v_vals_624_, lean_object* v_i_625_, lean_object* v_entries_626_){
_start:
{
size_t v_depth_boxed_627_; lean_object* v_res_628_; 
v_depth_boxed_627_ = lean_unbox_usize(v_depth_622_);
lean_dec(v_depth_622_);
v_res_628_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg(v_depth_boxed_627_, v_keys_623_, v_vals_624_, v_i_625_, v_entries_626_);
lean_dec_ref(v_vals_624_);
lean_dec_ref(v_keys_623_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
size_t v_x_5104__boxed_634_; size_t v_x_5105__boxed_635_; lean_object* v_res_636_; 
v_x_5104__boxed_634_ = lean_unbox_usize(v_x_630_);
lean_dec(v_x_630_);
v_x_5105__boxed_635_ = lean_unbox_usize(v_x_631_);
lean_dec(v_x_631_);
v_res_636_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_x_629_, v_x_5104__boxed_634_, v_x_5105__boxed_635_, v_x_632_, v_x_633_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2___redArg(lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
uint64_t v___x_640_; size_t v___x_641_; size_t v___x_642_; lean_object* v___x_643_; 
v___x_640_ = l_Lean_instHashableMVarId_hash(v_x_638_);
v___x_641_ = lean_uint64_to_usize(v___x_640_);
v___x_642_ = ((size_t)1ULL);
v___x_643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_x_637_, v___x_641_, v___x_642_, v_x_638_, v_x_639_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(lean_object* v_mvarId_644_, lean_object* v_val_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; lean_object* v_mctx_649_; lean_object* v_cache_650_; lean_object* v_zetaDeltaFVarIds_651_; lean_object* v_postponed_652_; lean_object* v_diag_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_681_; 
v___x_648_ = lean_st_ref_take(v___y_646_);
v_mctx_649_ = lean_ctor_get(v___x_648_, 0);
v_cache_650_ = lean_ctor_get(v___x_648_, 1);
v_zetaDeltaFVarIds_651_ = lean_ctor_get(v___x_648_, 2);
v_postponed_652_ = lean_ctor_get(v___x_648_, 3);
v_diag_653_ = lean_ctor_get(v___x_648_, 4);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_681_ == 0)
{
v___x_655_ = v___x_648_;
v_isShared_656_ = v_isSharedCheck_681_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_diag_653_);
lean_inc(v_postponed_652_);
lean_inc(v_zetaDeltaFVarIds_651_);
lean_inc(v_cache_650_);
lean_inc(v_mctx_649_);
lean_dec(v___x_648_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_681_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v_depth_657_; lean_object* v_levelAssignDepth_658_; lean_object* v_lmvarCounter_659_; lean_object* v_mvarCounter_660_; lean_object* v_lDecls_661_; lean_object* v_decls_662_; lean_object* v_userNames_663_; lean_object* v_lAssignment_664_; lean_object* v_eAssignment_665_; lean_object* v_dAssignment_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_680_; 
v_depth_657_ = lean_ctor_get(v_mctx_649_, 0);
v_levelAssignDepth_658_ = lean_ctor_get(v_mctx_649_, 1);
v_lmvarCounter_659_ = lean_ctor_get(v_mctx_649_, 2);
v_mvarCounter_660_ = lean_ctor_get(v_mctx_649_, 3);
v_lDecls_661_ = lean_ctor_get(v_mctx_649_, 4);
v_decls_662_ = lean_ctor_get(v_mctx_649_, 5);
v_userNames_663_ = lean_ctor_get(v_mctx_649_, 6);
v_lAssignment_664_ = lean_ctor_get(v_mctx_649_, 7);
v_eAssignment_665_ = lean_ctor_get(v_mctx_649_, 8);
v_dAssignment_666_ = lean_ctor_get(v_mctx_649_, 9);
v_isSharedCheck_680_ = !lean_is_exclusive(v_mctx_649_);
if (v_isSharedCheck_680_ == 0)
{
v___x_668_ = v_mctx_649_;
v_isShared_669_ = v_isSharedCheck_680_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_dAssignment_666_);
lean_inc(v_eAssignment_665_);
lean_inc(v_lAssignment_664_);
lean_inc(v_userNames_663_);
lean_inc(v_decls_662_);
lean_inc(v_lDecls_661_);
lean_inc(v_mvarCounter_660_);
lean_inc(v_lmvarCounter_659_);
lean_inc(v_levelAssignDepth_658_);
lean_inc(v_depth_657_);
lean_dec(v_mctx_649_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_680_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2___redArg(v_eAssignment_665_, v_mvarId_644_, v_val_645_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 8, v___x_670_);
v___x_672_ = v___x_668_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_depth_657_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_levelAssignDepth_658_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_lmvarCounter_659_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v_mvarCounter_660_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v_lDecls_661_);
lean_ctor_set(v_reuseFailAlloc_679_, 5, v_decls_662_);
lean_ctor_set(v_reuseFailAlloc_679_, 6, v_userNames_663_);
lean_ctor_set(v_reuseFailAlloc_679_, 7, v_lAssignment_664_);
lean_ctor_set(v_reuseFailAlloc_679_, 8, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_679_, 9, v_dAssignment_666_);
v___x_672_ = v_reuseFailAlloc_679_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_674_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_672_);
v___x_674_ = v___x_655_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_cache_650_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_zetaDeltaFVarIds_651_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v_postponed_652_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v_diag_653_);
v___x_674_ = v_reuseFailAlloc_678_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_st_ref_set(v___y_646_, v___x_674_);
v___x_676_ = lean_box(0);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg___boxed(lean_object* v_mvarId_682_, lean_object* v_val_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(v_mvarId_682_, v_val_683_, v___y_684_);
lean_dec(v___y_684_);
return v_res_686_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__0));
v___x_689_ = l_Lean_stringToMessageData(v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0(lean_object* v_a_690_, lean_object* v___x_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___x_709_; 
lean_inc(v_a_690_);
v___x_709_ = l_Lean_MVarId_getType(v_a_690_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v_a_712_; lean_object* v___x_713_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(v_a_710_, v___y_697_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref(v___x_711_);
v___x_713_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_712_);
lean_dec(v_a_712_);
if (lean_obj_tag(v___x_713_) == 1)
{
lean_object* v_val_714_; lean_object* v___x_715_; 
v_val_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc_n(v_val_714_, 2);
lean_dec_ref_known(v___x_713_, 1);
lean_inc(v___x_691_);
v___x_715_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(v_val_714_, v___x_691_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v___x_715_, 1);
if (lean_obj_tag(v_a_716_) == 1)
{
lean_object* v_val_717_; lean_object* v___x_718_; 
lean_dec(v_val_714_);
lean_dec(v___x_691_);
v_val_717_ = lean_ctor_get(v_a_716_, 0);
lean_inc(v_val_717_);
lean_dec_ref_known(v_a_716_, 1);
v___x_718_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(v_a_690_, v_val_717_, v___y_697_);
lean_dec_ref(v___x_718_);
v___y_702_ = v___y_693_;
v___y_703_ = v___y_696_;
v___y_704_ = v___y_697_;
v___y_705_ = v___y_698_;
v___y_706_ = v___y_699_;
goto v___jp_701_;
}
else
{
lean_object* v___x_719_; 
lean_dec(v_a_716_);
v___x_719_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(v_val_714_, v___x_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_721_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_719_, 1);
v___x_721_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(v_a_690_, v_a_720_, v___y_697_);
lean_dec_ref(v___x_721_);
v___y_702_ = v___y_693_;
v___y_703_ = v___y_696_;
v___y_704_ = v___y_697_;
v___y_705_ = v___y_698_;
v___y_706_ = v___y_699_;
goto v___jp_701_;
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_a_690_);
v_a_722_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_719_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_719_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec(v_val_714_);
lean_dec(v___x_691_);
lean_dec(v_a_690_);
v_a_730_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_715_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_715_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec(v___x_713_);
lean_dec(v___x_691_);
lean_dec(v_a_690_);
v___x_738_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1);
v___x_739_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(v___x_738_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
return v___x_739_;
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v___x_691_);
lean_dec(v_a_690_);
v_a_740_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_709_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_709_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
v___jp_701_:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_box(0);
v___x_708_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_707_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___boxed(lean_object* v_a_748_, lean_object* v___x_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0(v_a_748_, v___x_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact(lean_object* v_x_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3));
lean_inc(v_x_768_);
v___x_779_ = l_Lean_Syntax_isOfKind(v_x_768_, v___x_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; 
lean_dec(v_x_768_);
v___x_780_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg();
return v___x_780_;
}
else
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_770_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___f_785_; lean_object* v___x_786_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc_n(v_a_782_, 2);
lean_dec_ref_known(v___x_781_, 1);
v___x_783_ = lean_unsigned_to_nat(1u);
v___x_784_ = l_Lean_Syntax_getArg(v_x_768_, v___x_783_);
lean_dec(v_x_768_);
v___f_785_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___boxed), 11, 2);
lean_closure_set(v___f_785_, 0, v_a_782_);
lean_closure_set(v___f_785_, 1, v___x_784_);
v___x_786_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(v_a_782_, v___f_785_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
return v___x_786_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_x_768_);
v_a_787_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_781_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_781_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___boxed(lean_object* v_x_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact(v_x_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2(lean_object* v_mvarId_806_, lean_object* v_val_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(v_mvarId_806_, v_val_807_, v___y_813_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___boxed(lean_object* v_mvarId_818_, lean_object* v_val_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2(v_mvarId_818_, v_val_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2(lean_object* v_00_u03b2_830_, lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2___redArg(v_x_831_, v_x_832_, v_x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_835_, lean_object* v_x_836_, size_t v_x_837_, size_t v_x_838_, lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_x_836_, v_x_837_, v_x_838_, v_x_839_, v_x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v_x_847_){
_start:
{
size_t v_x_5561__boxed_848_; size_t v_x_5562__boxed_849_; lean_object* v_res_850_; 
v_x_5561__boxed_848_ = lean_unbox_usize(v_x_844_);
lean_dec(v_x_844_);
v_x_5562__boxed_849_ = lean_unbox_usize(v_x_845_);
lean_dec(v_x_845_);
v_res_850_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4(v_00_u03b2_842_, v_x_843_, v_x_5561__boxed_848_, v_x_5562__boxed_849_, v_x_846_, v_x_847_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_851_, lean_object* v_n_852_, lean_object* v_k_853_, lean_object* v_v_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5___redArg(v_n_852_, v_k_853_, v_v_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_856_, size_t v_depth_857_, lean_object* v_keys_858_, lean_object* v_vals_859_, lean_object* v_heq_860_, lean_object* v_i_861_, lean_object* v_entries_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg(v_depth_857_, v_keys_858_, v_vals_859_, v_i_861_, v_entries_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_864_, lean_object* v_depth_865_, lean_object* v_keys_866_, lean_object* v_vals_867_, lean_object* v_heq_868_, lean_object* v_i_869_, lean_object* v_entries_870_){
_start:
{
size_t v_depth_boxed_871_; lean_object* v_res_872_; 
v_depth_boxed_871_ = lean_unbox_usize(v_depth_865_);
lean_dec(v_depth_865_);
v_res_872_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6(v_00_u03b2_864_, v_depth_boxed_871_, v_keys_866_, v_vals_867_, v_heq_868_, v_i_869_, v_entries_870_);
lean_dec_ref(v_vals_867_);
lean_dec_ref(v_keys_866_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(v_x_874_, v_x_875_, v_x_876_, v_x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1(){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_890_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_891_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3));
v___x_892_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3));
v___x_893_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___boxed), 10, 0);
v___x_894_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_890_, v___x_891_, v___x_892_, v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___boxed(lean_object* v_a_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1();
return v_res_896_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(builtin);
}
#ifdef __cplusplus
}
#endif
