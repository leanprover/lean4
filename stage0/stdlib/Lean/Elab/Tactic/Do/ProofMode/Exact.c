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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
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
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_7_; lean_object* v_env_8_; uint8_t v___x_9_; lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toCold_12_; lean_object* v_mctx_13_; lean_object* v_lctx_14_; lean_object* v_options_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = 0;
v_env_10_ = l_Lean_Environment_setRecordingDeps(v_env_8_, v___x_9_);
v___x_11_ = lean_st_ref_get(v___y_3_);
v_toCold_12_ = lean_ctor_get(v___y_4_, 0);
v_mctx_13_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_mctx_13_);
lean_dec(v___x_11_);
v_lctx_14_ = lean_ctor_get(v___y_2_, 2);
v_options_15_ = lean_ctor_get(v_toCold_12_, 2);
lean_inc_ref(v_options_15_);
lean_inc_ref(v_lctx_14_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_env_10_);
lean_ctor_set(v___x_16_, 1, v_mctx_13_);
lean_ctor_set(v___x_16_, 2, v_lctx_14_);
lean_ctor_set(v___x_16_, 3, v_options_15_);
v___x_17_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_msgData_1_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0___boxed(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(v_msgData_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(lean_object* v_msg_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_ref_32_; lean_object* v___x_33_; lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
v_ref_32_ = lean_ctor_get(v___y_29_, 2);
v___x_33_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(v_msg_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_ref_32_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v_ref_32_);
lean_ctor_set(v___x_38_, 1, v_a_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 1);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg___boxed(lean_object* v_msg_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(v_msg_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__7));
v___x_65_ = l_Lean_stringToMessageData(v___x_64_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__9));
v___x_68_ = l_Lean_stringToMessageData(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(lean_object* v_goal_69_, lean_object* v_hyp_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = l_Lean_Syntax_getId(v_hyp_70_);
lean_inc_ref(v_goal_69_);
v___x_77_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(v_goal_69_, v___x_76_);
lean_dec(v___x_76_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec(v_hyp_70_);
lean_dec_ref(v_goal_69_);
v___x_78_ = lean_box(0);
v___x_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
return v___x_79_;
}
else
{
lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_143_; 
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; 
v_unused_144_ = lean_ctor_get(v___x_77_, 0);
lean_dec(v_unused_144_);
v___x_81_ = v___x_77_;
v_isShared_82_ = v_isSharedCheck_143_;
goto v_resetjp_80_;
}
else
{
lean_dec(v___x_77_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_143_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; 
lean_inc(v_hyp_70_);
lean_inc_ref(v_goal_69_);
v___x_83_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_goal_69_, v_hyp_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_134_; 
v_a_84_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_134_ == 0)
{
v___x_86_ = v___x_83_;
v_isShared_87_ = v_isSharedCheck_134_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_134_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v_u_88_; lean_object* v_00_u03c3s_89_; lean_object* v_hyps_90_; lean_object* v_target_91_; lean_object* v_focusHyp_92_; lean_object* v_restHyps_93_; lean_object* v_proof_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_107_; 
v_u_88_ = lean_ctor_get(v_goal_69_, 0);
lean_inc(v_u_88_);
v_00_u03c3s_89_ = lean_ctor_get(v_goal_69_, 1);
lean_inc_ref(v_00_u03c3s_89_);
v_hyps_90_ = lean_ctor_get(v_goal_69_, 2);
lean_inc_ref(v_hyps_90_);
v_target_91_ = lean_ctor_get(v_goal_69_, 3);
lean_inc_ref_n(v_target_91_, 3);
lean_dec_ref(v_goal_69_);
v_focusHyp_92_ = lean_ctor_get(v_a_84_, 0);
lean_inc_ref(v_focusHyp_92_);
v_restHyps_93_ = lean_ctor_get(v_a_84_, 1);
lean_inc_ref(v_restHyps_93_);
v_proof_94_ = lean_ctor_get(v_a_84_, 2);
lean_inc_ref(v_proof_94_);
lean_dec(v_a_84_);
v___x_95_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6));
v___x_96_ = lean_box(0);
v___x_97_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_97_, 0, v_u_88_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = l_Lean_mkConst(v___x_95_, v___x_97_);
v___x_99_ = l_Lean_mkApp5(v___x_98_, v_00_u03c3s_89_, v_hyps_90_, v_restHyps_93_, v_target_91_, v_proof_94_);
v___x_107_ = l_Lean_Meta_isExprDefEq(v_focusHyp_92_, v_target_91_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; uint8_t v___x_109_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_a_108_);
lean_dec_ref_known(v___x_107_, 1);
v___x_109_ = lean_unbox(v_a_108_);
lean_dec(v_a_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
lean_dec_ref(v___x_99_);
lean_del_object(v___x_86_);
lean_del_object(v___x_81_);
v___x_110_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8);
v___x_111_ = l_Lean_MessageData_ofSyntax(v_hyp_70_);
v___x_112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_110_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10);
v___x_114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_112_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = l_Lean_MessageData_ofExpr(v_target_91_);
v___x_116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(v___x_116_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
v_a_118_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_117_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
else
{
lean_dec_ref(v_target_91_);
lean_dec(v_hyp_70_);
goto v___jp_100_;
}
}
else
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_133_; 
lean_dec_ref(v___x_99_);
lean_dec_ref(v_target_91_);
lean_del_object(v___x_86_);
lean_del_object(v___x_81_);
lean_dec(v_hyp_70_);
v_a_126_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_133_ == 0)
{
v___x_128_ = v___x_107_;
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_107_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_126_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
v___jp_100_:
{
lean_object* v___x_102_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v___x_99_);
v___x_102_ = v___x_81_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_99_);
v___x_102_ = v_reuseFailAlloc_106_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_104_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_102_);
v___x_104_ = v___x_86_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
}
else
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
lean_del_object(v___x_81_);
lean_dec(v_hyp_70_);
lean_dec_ref(v_goal_69_);
v_a_135_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_142_ == 0)
{
v___x_137_ = v___x_83_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_83_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_135_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___boxed(lean_object* v_goal_145_, lean_object* v_hyp_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(v_goal_145_, v_hyp_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0(lean_object* v_00_u03b1_153_, lean_object* v_msg_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(v_msg_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___boxed(lean_object* v_00_u03b1_161_, lean_object* v_msg_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0(v_00_u03b1_161_, v_msg_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(lean_object* v_msg_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_ref_175_; lean_object* v___x_176_; lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_185_; 
v_ref_175_ = lean_ctor_get(v___y_172_, 2);
v___x_176_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(v_msg_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
v_a_177_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_185_ == 0)
{
v___x_179_ = v___x_176_;
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_183_; 
lean_inc(v_ref_175_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v_ref_175_);
lean_ctor_set(v___x_181_, 1, v_a_177_);
if (v_isShared_180_ == 0)
{
lean_ctor_set_tag(v___x_179_, 1);
lean_ctor_set(v___x_179_, 0, v___x_181_);
v___x_183_ = v___x_179_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg___boxed(lean_object* v_msg_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(v_msg_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_192_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_box(0);
v___x_194_ = l_Lean_mkSort(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0);
v___x_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__7));
v___x_218_ = l_Lean_stringToMessageData(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__9));
v___x_221_ = l_Lean_stringToMessageData(v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(lean_object* v_goal_222_, lean_object* v_hyp_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_233_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1);
v___x_234_ = 0;
v___x_235_ = lean_box(0);
v___x_236_ = l_Lean_Meta_mkFreshExprMVar(v___x_233_, v___x_234_, v___x_235_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_296_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_296_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_296_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_296_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
lean_inc(v_a_237_);
if (v_isShared_240_ == 0)
{
lean_ctor_set_tag(v___x_239_, 1);
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_295_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
uint8_t v___x_243_; lean_object* v___x_244_; 
v___x_243_ = 0;
lean_inc(v_hyp_223_);
v___x_244_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v_hyp_223_, v___x_242_, v___x_243_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_294_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_294_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_294_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_294_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v_u_249_; lean_object* v_00_u03c3s_250_; lean_object* v_hyps_251_; lean_object* v_target_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v_u_249_ = lean_ctor_get(v_goal_222_, 0);
lean_inc(v_u_249_);
v_00_u03c3s_250_ = lean_ctor_get(v_goal_222_, 1);
lean_inc_ref_n(v_00_u03c3s_250_, 2);
v_hyps_251_ = lean_ctor_get(v_goal_222_, 2);
lean_inc_ref(v_hyps_251_);
v_target_252_ = lean_ctor_get(v_goal_222_, 3);
lean_inc_ref(v_target_252_);
lean_dec_ref(v_goal_222_);
v___x_253_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2));
v___x_254_ = lean_box(0);
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v_u_249_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
lean_inc_ref(v___x_255_);
v___x_256_ = l_Lean_mkConst(v___x_253_, v___x_255_);
v___x_257_ = l_Lean_Expr_app___override(v___x_256_, v_00_u03c3s_250_);
if (v_isShared_248_ == 0)
{
lean_ctor_set_tag(v___x_247_, 1);
lean_ctor_set(v___x_247_, 0, v___x_257_);
v___x_259_ = v___x_247_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_293_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Meta_mkFreshExprMVar(v___x_259_, v___x_234_, v___x_235_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_260_, 1);
v___x_262_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4));
lean_inc_ref(v___x_255_);
v___x_263_ = l_Lean_mkConst(v___x_262_, v___x_255_);
lean_inc_ref(v_00_u03c3s_250_);
lean_inc(v_a_237_);
v___x_264_ = l_Lean_mkApp3(v___x_263_, v_a_237_, v_00_u03c3s_250_, v_a_261_);
v___x_265_ = lean_box(0);
v___x_266_ = l_Lean_Meta_synthInstance_x3f(v___x_264_, v___x_265_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_284_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_284_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_284_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_284_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
if (lean_obj_tag(v_a_267_) == 1)
{
lean_object* v_val_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
lean_dec(v_hyp_223_);
v_val_271_ = lean_ctor_get(v_a_267_, 0);
lean_inc(v_val_271_);
lean_dec_ref_known(v_a_267_, 1);
v___x_272_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6));
v___x_273_ = l_Lean_mkConst(v___x_272_, v___x_255_);
v___x_274_ = l_Lean_mkApp6(v___x_273_, v_00_u03c3s_250_, v_a_237_, v_hyps_251_, v_target_252_, v_val_271_, v_a_245_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_274_);
v___x_276_ = v___x_269_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
lean_del_object(v___x_269_);
lean_dec(v_a_267_);
lean_dec_ref_known(v___x_255_, 2);
lean_dec_ref(v_target_252_);
lean_dec_ref(v_hyps_251_);
lean_dec_ref(v_00_u03c3s_250_);
lean_dec(v_a_245_);
lean_dec(v_a_237_);
v___x_278_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8);
v___x_279_ = l_Lean_MessageData_ofSyntax(v_hyp_223_);
v___x_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10);
v___x_282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(v___x_282_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
return v___x_283_;
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec_ref_known(v___x_255_, 2);
lean_dec_ref(v_target_252_);
lean_dec_ref(v_hyps_251_);
lean_dec_ref(v_00_u03c3s_250_);
lean_dec(v_a_245_);
lean_dec(v_a_237_);
lean_dec(v_hyp_223_);
v_a_285_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_266_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_266_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
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
else
{
lean_dec_ref_known(v___x_255_, 2);
lean_dec_ref(v_target_252_);
lean_dec_ref(v_hyps_251_);
lean_dec_ref(v_00_u03c3s_250_);
lean_dec(v_a_245_);
lean_dec(v_a_237_);
lean_dec(v_hyp_223_);
return v___x_260_;
}
}
}
}
else
{
lean_dec(v_a_237_);
lean_dec(v_hyp_223_);
lean_dec_ref(v_goal_222_);
return v___x_244_;
}
}
}
}
else
{
lean_dec(v_hyp_223_);
lean_dec_ref(v_goal_222_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___boxed(lean_object* v_goal_297_, lean_object* v_hyp_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(v_goal_297_, v_hyp_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0(lean_object* v_00_u03b1_309_, lean_object* v_msg_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(v_msg_310_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___boxed(lean_object* v_00_u03b1_321_, lean_object* v_msg_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0(v_00_u03b1_321_, v_msg_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
return v_res_332_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = lean_box(0);
v___x_334_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_333_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg(){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0);
v___x_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___boxed(lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg();
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0(lean_object* v_00_u03b1_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg();
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___boxed(lean_object* v_00_u03b1_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0(v_00_u03b1_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(lean_object* v_e_363_, lean_object* v___y_364_){
_start:
{
uint8_t v___x_366_; 
v___x_366_ = l_Lean_Expr_hasMVar(v_e_363_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; 
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v_e_363_);
return v___x_367_;
}
else
{
lean_object* v___x_368_; lean_object* v_mctx_369_; lean_object* v___x_370_; lean_object* v_fst_371_; lean_object* v_snd_372_; lean_object* v___x_373_; lean_object* v_cache_374_; lean_object* v_zetaDeltaFVarIds_375_; lean_object* v_postponed_376_; lean_object* v_diag_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_386_; 
v___x_368_ = lean_st_ref_get(v___y_364_);
v_mctx_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc_ref(v_mctx_369_);
lean_dec(v___x_368_);
v___x_370_ = l_Lean_instantiateMVarsCore(v_mctx_369_, v_e_363_);
v_fst_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_fst_371_);
v_snd_372_ = lean_ctor_get(v___x_370_, 1);
lean_inc(v_snd_372_);
lean_dec_ref(v___x_370_);
v___x_373_ = lean_st_ref_take(v___y_364_);
v_cache_374_ = lean_ctor_get(v___x_373_, 1);
v_zetaDeltaFVarIds_375_ = lean_ctor_get(v___x_373_, 2);
v_postponed_376_ = lean_ctor_get(v___x_373_, 3);
v_diag_377_ = lean_ctor_get(v___x_373_, 4);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; 
v_unused_387_ = lean_ctor_get(v___x_373_, 0);
lean_dec(v_unused_387_);
v___x_379_ = v___x_373_;
v_isShared_380_ = v_isSharedCheck_386_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_diag_377_);
lean_inc(v_postponed_376_);
lean_inc(v_zetaDeltaFVarIds_375_);
lean_inc(v_cache_374_);
lean_dec(v___x_373_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_386_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v_snd_372_);
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_snd_372_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_cache_374_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v_zetaDeltaFVarIds_375_);
lean_ctor_set(v_reuseFailAlloc_385_, 3, v_postponed_376_);
lean_ctor_set(v_reuseFailAlloc_385_, 4, v_diag_377_);
v___x_382_ = v_reuseFailAlloc_385_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_st_ref_put(v___y_364_, v___x_382_);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v_fst_371_);
return v___x_384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg___boxed(lean_object* v_e_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(v_e_388_, v___y_389_);
lean_dec(v___y_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1(lean_object* v_e_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(v_e_392_, v___y_398_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___boxed(lean_object* v_e_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1(v_e_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0(lean_object* v_x_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v___x_424_; 
lean_inc(v___y_418_);
lean_inc_ref(v___y_417_);
lean_inc(v___y_416_);
lean_inc_ref(v___y_415_);
v___x_424_ = lean_apply_9(v_x_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, lean_box(0));
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0___boxed(lean_object* v_x_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0(v_x_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(lean_object* v_mvarId_436_, lean_object* v_x_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___f_447_; lean_object* v___x_448_; 
lean_inc(v___y_441_);
lean_inc_ref(v___y_440_);
lean_inc(v___y_439_);
lean_inc_ref(v___y_438_);
v___f_447_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_447_, 0, v_x_437_);
lean_closure_set(v___f_447_, 1, v___y_438_);
lean_closure_set(v___f_447_, 2, v___y_439_);
lean_closure_set(v___f_447_, 3, v___y_440_);
lean_closure_set(v___f_447_, 4, v___y_441_);
v___x_448_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_436_, v___f_447_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
if (lean_obj_tag(v___x_448_) == 0)
{
return v___x_448_;
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___boxed(lean_object* v_mvarId_457_, lean_object* v_x_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(v_mvarId_457_, v_x_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3(lean_object* v_00_u03b1_469_, lean_object* v_mvarId_470_, lean_object* v_x_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(v_mvarId_470_, v_x_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___boxed(lean_object* v_00_u03b1_482_, lean_object* v_mvarId_483_, lean_object* v_x_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3(v_00_u03b1_482_, v_mvarId_483_, v_x_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_495_, lean_object* v_x_496_, lean_object* v_x_497_, lean_object* v_x_498_){
_start:
{
lean_object* v_ks_499_; lean_object* v_vs_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_524_; 
v_ks_499_ = lean_ctor_get(v_x_495_, 0);
v_vs_500_ = lean_ctor_get(v_x_495_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_524_ == 0)
{
v___x_502_ = v_x_495_;
v_isShared_503_ = v_isSharedCheck_524_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_vs_500_);
lean_inc(v_ks_499_);
lean_dec(v_x_495_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_524_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = lean_array_get_size(v_ks_499_);
v___x_505_ = lean_nat_dec_lt(v_x_496_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_509_; 
lean_dec(v_x_496_);
v___x_506_ = lean_array_push(v_ks_499_, v_x_497_);
v___x_507_ = lean_array_push(v_vs_500_, v_x_498_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 1, v___x_507_);
lean_ctor_set(v___x_502_, 0, v___x_506_);
v___x_509_ = v___x_502_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
else
{
lean_object* v_k_x27_511_; uint8_t v___x_512_; 
v_k_x27_511_ = lean_array_fget_borrowed(v_ks_499_, v_x_496_);
v___x_512_ = l_Lean_instBEqMVarId_beq(v_x_497_, v_k_x27_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_514_; 
if (v_isShared_503_ == 0)
{
v___x_514_ = v___x_502_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_ks_499_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_vs_500_);
v___x_514_ = v_reuseFailAlloc_518_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_nat_add(v_x_496_, v___x_515_);
lean_dec(v_x_496_);
v_x_495_ = v___x_514_;
v_x_496_ = v___x_516_;
goto _start;
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_519_ = lean_array_fset(v_ks_499_, v_x_496_, v_x_497_);
v___x_520_ = lean_array_fset(v_vs_500_, v_x_496_, v_x_498_);
lean_dec(v_x_496_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 1, v___x_520_);
lean_ctor_set(v___x_502_, 0, v___x_519_);
v___x_522_ = v___x_502_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5___redArg(lean_object* v_n_525_, lean_object* v_k_526_, lean_object* v_v_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(v_n_525_, v___x_528_, v_k_526_, v_v_527_);
return v___x_529_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(lean_object* v_x_531_, size_t v_x_532_, size_t v_x_533_, lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
lean_object* v_es_536_; size_t v___x_537_; size_t v___x_538_; lean_object* v_j_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_es_536_ = lean_ctor_get(v_x_531_, 0);
v___x_537_ = ((size_t)31ULL);
v___x_538_ = lean_usize_land(v_x_532_, v___x_537_);
v_j_539_ = lean_usize_to_nat(v___x_538_);
v___x_540_ = lean_array_get_size(v_es_536_);
v___x_541_ = lean_nat_dec_lt(v_j_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_dec(v_j_539_);
lean_dec(v_x_535_);
lean_dec(v_x_534_);
return v_x_531_;
}
else
{
lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_580_; 
lean_inc_ref(v_es_536_);
v_isSharedCheck_580_ = !lean_is_exclusive(v_x_531_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v_x_531_, 0);
lean_dec(v_unused_581_);
v___x_543_ = v_x_531_;
v_isShared_544_ = v_isSharedCheck_580_;
goto v_resetjp_542_;
}
else
{
lean_dec(v_x_531_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_580_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v_v_545_; lean_object* v___x_546_; lean_object* v_xs_x27_547_; lean_object* v___y_549_; 
v_v_545_ = lean_array_fget(v_es_536_, v_j_539_);
v___x_546_ = lean_box(0);
v_xs_x27_547_ = lean_array_fset(v_es_536_, v_j_539_, v___x_546_);
switch(lean_obj_tag(v_v_545_))
{
case 0:
{
lean_object* v_key_554_; lean_object* v_val_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_565_; 
v_key_554_ = lean_ctor_get(v_v_545_, 0);
v_val_555_ = lean_ctor_get(v_v_545_, 1);
v_isSharedCheck_565_ = !lean_is_exclusive(v_v_545_);
if (v_isSharedCheck_565_ == 0)
{
v___x_557_ = v_v_545_;
v_isShared_558_ = v_isSharedCheck_565_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_val_555_);
lean_inc(v_key_554_);
lean_dec(v_v_545_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_565_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
uint8_t v___x_559_; 
v___x_559_ = l_Lean_instBEqMVarId_beq(v_x_534_, v_key_554_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_del_object(v___x_557_);
v___x_560_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_554_, v_val_555_, v_x_534_, v_x_535_);
v___x_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
v___y_549_ = v___x_561_;
goto v___jp_548_;
}
else
{
lean_object* v___x_563_; 
lean_dec(v_val_555_);
lean_dec(v_key_554_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v_x_535_);
lean_ctor_set(v___x_557_, 0, v_x_534_);
v___x_563_ = v___x_557_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_x_534_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_x_535_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
v___y_549_ = v___x_563_;
goto v___jp_548_;
}
}
}
}
case 1:
{
lean_object* v_node_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_578_; 
v_node_566_ = lean_ctor_get(v_v_545_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v_v_545_);
if (v_isSharedCheck_578_ == 0)
{
v___x_568_ = v_v_545_;
v_isShared_569_ = v_isSharedCheck_578_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_node_566_);
lean_dec(v_v_545_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_578_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
size_t v___x_570_; size_t v___x_571_; size_t v___x_572_; size_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_570_ = ((size_t)5ULL);
v___x_571_ = lean_usize_shift_right(v_x_532_, v___x_570_);
v___x_572_ = ((size_t)1ULL);
v___x_573_ = lean_usize_add(v_x_533_, v___x_572_);
v___x_574_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_node_566_, v___x_571_, v___x_573_, v_x_534_, v_x_535_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_574_);
v___x_576_ = v___x_568_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
v___y_549_ = v___x_576_;
goto v___jp_548_;
}
}
}
default: 
{
lean_object* v___x_579_; 
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_x_534_);
lean_ctor_set(v___x_579_, 1, v_x_535_);
v___y_549_ = v___x_579_;
goto v___jp_548_;
}
}
v___jp_548_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = lean_array_fset(v_xs_x27_547_, v_j_539_, v___y_549_);
lean_dec(v_j_539_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_550_);
v___x_552_ = v___x_543_;
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
else
{
lean_object* v_ks_582_; lean_object* v_vs_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_601_; 
v_ks_582_ = lean_ctor_get(v_x_531_, 0);
v_vs_583_ = lean_ctor_get(v_x_531_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v_x_531_);
if (v_isSharedCheck_601_ == 0)
{
v___x_585_ = v_x_531_;
v_isShared_586_ = v_isSharedCheck_601_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_vs_583_);
lean_inc(v_ks_582_);
lean_dec(v_x_531_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_601_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_ks_582_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_vs_583_);
v___x_588_ = v_reuseFailAlloc_600_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v_newNode_589_; size_t v___x_590_; uint8_t v___x_591_; 
v_newNode_589_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5___redArg(v___x_588_, v_x_534_, v_x_535_);
v___x_590_ = ((size_t)7ULL);
v___x_591_ = lean_usize_dec_le(v___x_590_, v_x_533_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_592_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_589_);
v___x_593_ = lean_unsigned_to_nat(4u);
v___x_594_ = lean_nat_dec_lt(v___x_592_, v___x_593_);
lean_dec(v___x_592_);
if (v___x_594_ == 0)
{
lean_object* v_ks_595_; lean_object* v_vs_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_ks_595_ = lean_ctor_get(v_newNode_589_, 0);
lean_inc_ref(v_ks_595_);
v_vs_596_ = lean_ctor_get(v_newNode_589_, 1);
lean_inc_ref(v_vs_596_);
lean_dec_ref(v_newNode_589_);
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_599_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg(v_x_533_, v_ks_595_, v_vs_596_, v___x_597_, v___x_598_);
lean_dec_ref(v_vs_596_);
lean_dec_ref(v_ks_595_);
return v___x_599_;
}
else
{
return v_newNode_589_;
}
}
else
{
return v_newNode_589_;
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
size_t v_x_4631__boxed_634_; size_t v_x_4632__boxed_635_; lean_object* v_res_636_; 
v_x_4631__boxed_634_ = lean_unbox_usize(v_x_630_);
lean_dec(v_x_630_);
v_x_4632__boxed_635_ = lean_unbox_usize(v_x_631_);
lean_dec(v_x_631_);
v_res_636_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_x_629_, v_x_4631__boxed_634_, v_x_4632__boxed_635_, v_x_632_, v_x_633_);
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
lean_object* v___x_648_; lean_object* v_mctx_649_; lean_object* v_cache_650_; lean_object* v_zetaDeltaFVarIds_651_; lean_object* v_postponed_652_; lean_object* v_diag_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_683_; 
v___x_648_ = lean_st_ref_take(v___y_646_);
v_mctx_649_ = lean_ctor_get(v___x_648_, 0);
v_cache_650_ = lean_ctor_get(v___x_648_, 1);
v_zetaDeltaFVarIds_651_ = lean_ctor_get(v___x_648_, 2);
v_postponed_652_ = lean_ctor_get(v___x_648_, 3);
v_diag_653_ = lean_ctor_get(v___x_648_, 4);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_683_ == 0)
{
v___x_655_ = v___x_648_;
v_isShared_656_ = v_isSharedCheck_683_;
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
v_isShared_656_ = v_isSharedCheck_683_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v_depth_657_; lean_object* v_levelAssignDepth_658_; lean_object* v_lmvarCounter_659_; lean_object* v_mvarCounter_660_; lean_object* v_lDecls_661_; lean_object* v_decls_662_; lean_object* v_userNames_663_; lean_object* v_lAssignment_664_; lean_object* v_eAssignment_665_; lean_object* v_dAssignment_666_; lean_object* v_instanceTypedMVars_667_; lean_object* v_synthNormMemo_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_682_; 
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
v_instanceTypedMVars_667_ = lean_ctor_get(v_mctx_649_, 10);
v_synthNormMemo_668_ = lean_ctor_get(v_mctx_649_, 11);
v_isSharedCheck_682_ = !lean_is_exclusive(v_mctx_649_);
if (v_isSharedCheck_682_ == 0)
{
v___x_670_ = v_mctx_649_;
v_isShared_671_ = v_isSharedCheck_682_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_synthNormMemo_668_);
lean_inc(v_instanceTypedMVars_667_);
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
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_682_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_672_ = lean_box(0);
v___x_673_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2___redArg(v_eAssignment_665_, v_mvarId_644_, v_val_645_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 8, v___x_673_);
v___x_675_ = v___x_670_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_depth_657_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_levelAssignDepth_658_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_lmvarCounter_659_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v_mvarCounter_660_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v_lDecls_661_);
lean_ctor_set(v_reuseFailAlloc_681_, 5, v_decls_662_);
lean_ctor_set(v_reuseFailAlloc_681_, 6, v_userNames_663_);
lean_ctor_set(v_reuseFailAlloc_681_, 7, v_lAssignment_664_);
lean_ctor_set(v_reuseFailAlloc_681_, 8, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_681_, 9, v_dAssignment_666_);
lean_ctor_set(v_reuseFailAlloc_681_, 10, v_instanceTypedMVars_667_);
lean_ctor_set(v_reuseFailAlloc_681_, 11, v_synthNormMemo_668_);
v___x_675_ = v_reuseFailAlloc_681_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_677_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_675_);
v___x_677_ = v___x_655_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_cache_650_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_zetaDeltaFVarIds_651_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_postponed_652_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_diag_653_);
v___x_677_ = v_reuseFailAlloc_680_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_st_ref_put(v___y_646_, v___x_677_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_672_);
return v___x_679_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg___boxed(lean_object* v_mvarId_684_, lean_object* v_val_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(v_mvarId_684_, v_val_685_, v___y_686_);
lean_dec(v___y_686_);
return v_res_688_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__0));
v___x_691_ = l_Lean_stringToMessageData(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0(lean_object* v_a_692_, lean_object* v___x_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_706_; 
lean_inc(v_a_692_);
v___x_706_ = l_Lean_MVarId_getType(v_a_692_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_708_; lean_object* v_a_709_; lean_object* v___x_710_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(v_a_707_, v___y_699_);
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref(v___x_708_);
v___x_710_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_709_);
lean_dec(v_a_709_);
if (lean_obj_tag(v___x_710_) == 1)
{
lean_object* v_val_711_; lean_object* v___x_712_; 
v_val_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc_n(v_val_711_, 2);
lean_dec_ref_known(v___x_710_, 1);
lean_inc(v___x_693_);
v___x_712_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(v_val_711_, v___x_693_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_712_, 1);
if (lean_obj_tag(v_a_713_) == 1)
{
lean_object* v_val_714_; lean_object* v___x_715_; 
lean_dec(v_val_711_);
lean_dec(v___x_693_);
v_val_714_ = lean_ctor_get(v_a_713_, 0);
lean_inc(v_val_714_);
lean_dec_ref_known(v_a_713_, 1);
v___x_715_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(v_a_692_, v_val_714_, v___y_699_);
lean_dec_ref(v___x_715_);
goto v___jp_703_;
}
else
{
lean_object* v___x_716_; 
lean_dec(v_a_713_);
v___x_716_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(v_val_711_, v___x_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_718_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
v___x_718_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(v_a_692_, v_a_717_, v___y_699_);
lean_dec_ref(v___x_718_);
goto v___jp_703_;
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_a_692_);
v_a_719_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_716_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_716_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec(v_val_711_);
lean_dec(v___x_693_);
lean_dec(v_a_692_);
v_a_727_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_712_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_712_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec(v___x_710_);
lean_dec(v___x_693_);
lean_dec(v_a_692_);
v___x_735_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1);
v___x_736_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(v___x_735_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
return v___x_736_;
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v___x_693_);
lean_dec(v_a_692_);
v_a_737_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_706_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_706_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
v___jp_703_:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_box(0);
v___x_705_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_704_, v___y_695_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___boxed(lean_object* v_a_745_, lean_object* v___x_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0(v_a_745_, v___x_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact(lean_object* v_x_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3));
lean_inc(v_x_765_);
v___x_776_ = l_Lean_Syntax_isOfKind(v_x_765_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; 
lean_dec(v_x_765_);
v___x_777_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg();
return v___x_777_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_778_ = lean_unsigned_to_nat(1u);
v___x_779_ = l_Lean_Syntax_getArg(v_x_765_, v___x_778_);
lean_dec(v_x_765_);
v___x_780_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_767_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___f_782_; lean_object* v___x_783_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc_n(v_a_781_, 2);
lean_dec_ref_known(v___x_780_, 1);
v___f_782_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___boxed), 11, 2);
lean_closure_set(v___f_782_, 0, v_a_781_);
lean_closure_set(v___f_782_, 1, v___x_779_);
v___x_783_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(v_a_781_, v___f_782_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
return v___x_783_;
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec(v___x_779_);
v_a_784_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_780_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_780_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___boxed(lean_object* v_x_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact(v_x_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2(lean_object* v_mvarId_803_, lean_object* v_val_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(v_mvarId_803_, v_val_804_, v___y_810_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___boxed(lean_object* v_mvarId_815_, lean_object* v_val_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2(v_mvarId_815_, v_val_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2(lean_object* v_00_u03b2_827_, lean_object* v_x_828_, lean_object* v_x_829_, lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2___redArg(v_x_828_, v_x_829_, v_x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_832_, lean_object* v_x_833_, size_t v_x_834_, size_t v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_x_833_, v_x_834_, v_x_835_, v_x_836_, v_x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_839_, lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
size_t v_x_5074__boxed_845_; size_t v_x_5075__boxed_846_; lean_object* v_res_847_; 
v_x_5074__boxed_845_ = lean_unbox_usize(v_x_841_);
lean_dec(v_x_841_);
v_x_5075__boxed_846_ = lean_unbox_usize(v_x_842_);
lean_dec(v_x_842_);
v_res_847_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4(v_00_u03b2_839_, v_x_840_, v_x_5074__boxed_845_, v_x_5075__boxed_846_, v_x_843_, v_x_844_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_848_, lean_object* v_n_849_, lean_object* v_k_850_, lean_object* v_v_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5___redArg(v_n_849_, v_k_850_, v_v_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_853_, size_t v_depth_854_, lean_object* v_keys_855_, lean_object* v_vals_856_, lean_object* v_heq_857_, lean_object* v_i_858_, lean_object* v_entries_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg(v_depth_854_, v_keys_855_, v_vals_856_, v_i_858_, v_entries_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_861_, lean_object* v_depth_862_, lean_object* v_keys_863_, lean_object* v_vals_864_, lean_object* v_heq_865_, lean_object* v_i_866_, lean_object* v_entries_867_){
_start:
{
size_t v_depth_boxed_868_; lean_object* v_res_869_; 
v_depth_boxed_868_ = lean_unbox_usize(v_depth_862_);
lean_dec(v_depth_862_);
v_res_869_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6(v_00_u03b2_861_, v_depth_boxed_868_, v_keys_863_, v_vals_864_, v_heq_865_, v_i_866_, v_entries_867_);
lean_dec_ref(v_vals_864_);
lean_dec_ref(v_keys_863_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(v_x_871_, v_x_872_, v_x_873_, v_x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1(){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_887_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_888_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3));
v___x_889_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3));
v___x_890_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___boxed), 10, 0);
v___x_891_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_887_, v___x_888_, v___x_889_, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___boxed(lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1();
return v_res_893_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
