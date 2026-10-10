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
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
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
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(v_msgData_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0___boxed(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(v_msgData_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_26_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(lean_object* v_msg_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_ref_33_; lean_object* v___x_34_; lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_43_; 
v_ref_33_ = lean_ctor_get(v___y_30_, 2);
v___x_34_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
v_a_35_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_43_ == 0)
{
v___x_37_ = v___x_34_;
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_41_; 
lean_inc(v_ref_33_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v_ref_33_);
lean_ctor_set(v___x_39_, 1, v_a_35_);
if (v_isShared_38_ == 0)
{
lean_ctor_set_tag(v___x_37_, 1);
lean_ctor_set(v___x_37_, 0, v___x_39_);
v___x_41_ = v___x_37_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_27_ = stack[0].m_obj;
lean_object* v___y_28_ = stack[1].m_obj;
lean_object* v___y_29_ = stack[2].m_obj;
lean_object* v___y_30_ = stack[3].m_obj;
lean_object* v___y_31_ = stack[4].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg___boxed(lean_object* v_msg_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(v_msg_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
return v_res_51_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__7));
v___x_67_ = l_Lean_stringToMessageData(v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__9));
v___x_70_ = l_Lean_stringToMessageData(v___x_69_);
return v___x_70_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(lean_object* v_goal_71_, lean_object* v_hyp_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = l_Lean_Syntax_getId(v_hyp_72_);
lean_inc_ref(v_goal_71_);
v___x_79_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(v_goal_71_, v___x_78_);
lean_dec(v___x_78_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v_hyp_72_);
lean_dec_ref(v_goal_71_);
v___x_80_ = lean_box(0);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
else
{
lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_145_; 
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v___x_79_, 0);
lean_dec(v_unused_146_);
v___x_83_ = v___x_79_;
v_isShared_84_ = v_isSharedCheck_145_;
goto v_resetjp_82_;
}
else
{
lean_dec(v___x_79_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_145_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; 
lean_inc(v_hyp_72_);
lean_inc_ref(v_goal_71_);
v___x_85_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_goal_71_, v_hyp_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_136_; 
v_a_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_136_ == 0)
{
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_136_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_136_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v_u_90_; lean_object* v_00_u03c3s_91_; lean_object* v_hyps_92_; lean_object* v_target_93_; lean_object* v_focusHyp_94_; lean_object* v_restHyps_95_; lean_object* v_proof_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_109_; 
v_u_90_ = lean_ctor_get(v_goal_71_, 0);
lean_inc(v_u_90_);
v_00_u03c3s_91_ = lean_ctor_get(v_goal_71_, 1);
lean_inc_ref(v_00_u03c3s_91_);
v_hyps_92_ = lean_ctor_get(v_goal_71_, 2);
lean_inc_ref(v_hyps_92_);
v_target_93_ = lean_ctor_get(v_goal_71_, 3);
lean_inc_ref_n(v_target_93_, 3);
lean_dec_ref(v_goal_71_);
v_focusHyp_94_ = lean_ctor_get(v_a_86_, 0);
lean_inc_ref(v_focusHyp_94_);
v_restHyps_95_ = lean_ctor_get(v_a_86_, 1);
lean_inc_ref(v_restHyps_95_);
v_proof_96_ = lean_ctor_get(v_a_86_, 2);
lean_inc_ref(v_proof_96_);
lean_dec(v_a_86_);
v___x_97_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6));
v___x_98_ = lean_box(0);
v___x_99_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_99_, 0, v_u_90_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = l_Lean_mkConst(v___x_97_, v___x_99_);
v___x_101_ = l_Lean_mkApp5(v___x_100_, v_00_u03c3s_91_, v_hyps_92_, v_restHyps_95_, v_target_93_, v_proof_96_);
v___x_109_ = l_Lean_Meta_isExprDefEq(v_focusHyp_94_, v_target_93_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; uint8_t v___x_111_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_a_110_);
lean_dec_ref_known(v___x_109_, 1);
v___x_111_ = lean_unbox(v_a_110_);
lean_dec(v_a_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_dec_ref(v___x_101_);
lean_del_object(v___x_88_);
lean_del_object(v___x_83_);
v___x_112_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8);
v___x_113_ = l_Lean_MessageData_ofSyntax(v_hyp_72_);
v___x_114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_112_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10);
v___x_116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = l_Lean_MessageData_ofExpr(v_target_93_);
v___x_118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(v___x_118_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
v_a_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
else
{
lean_dec_ref(v_target_93_);
lean_dec(v_hyp_72_);
goto v___jp_102_;
}
}
else
{
lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_135_; 
lean_dec_ref(v___x_101_);
lean_dec_ref(v_target_93_);
lean_del_object(v___x_88_);
lean_del_object(v___x_83_);
lean_dec(v_hyp_72_);
v_a_128_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_135_ == 0)
{
v___x_130_ = v___x_109_;
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_dec(v___x_109_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_128_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
v___jp_102_:
{
lean_object* v___x_104_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_101_);
v___x_104_ = v___x_83_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_101_);
v___x_104_ = v_reuseFailAlloc_108_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_106_; 
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_104_);
v___x_106_ = v___x_88_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_del_object(v___x_83_);
lean_dec(v_hyp_72_);
lean_dec_ref(v_goal_71_);
v_a_137_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_85_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_85_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_71_ = stack[0].m_obj;
lean_object* v_hyp_72_ = stack[1].m_obj;
lean_object* v_a_73_ = stack[2].m_obj;
lean_object* v_a_74_ = stack[3].m_obj;
lean_object* v_a_75_ = stack[4].m_obj;
lean_object* v_a_76_ = stack[5].m_obj;
lean_object* v_res_147_;
v_res_147_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(v_goal_71_, v_hyp_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
stack->m_obj
 = v_res_147_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___boxed(lean_object* v_goal_148_, lean_object* v_hyp_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(v_goal_148_, v_hyp_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
return v_res_155_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0(lean_object* v_00_u03b1_156_, lean_object* v_msg_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(v_msg_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
return v___x_163_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_157_ = stack[1].m_obj;
lean_object* v___y_158_ = stack[2].m_obj;
lean_object* v___y_159_ = stack[3].m_obj;
lean_object* v___y_160_ = stack[4].m_obj;
lean_object* v___y_161_ = stack[5].m_obj;
lean_object* v_res_164_;
v_res_164_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0(lean_box(0), v_msg_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
stack->m_obj
 = v_res_164_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___boxed(lean_object* v_00_u03b1_165_, lean_object* v_msg_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0(v_00_u03b1_165_, v_msg_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
return v_res_172_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(lean_object* v_msg_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_ref_179_; lean_object* v___x_180_; lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_189_; 
v_ref_179_ = lean_ctor_get(v___y_176_, 2);
v___x_180_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(v_msg_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_189_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_189_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_189_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_187_; 
lean_inc(v_ref_179_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v_ref_179_);
lean_ctor_set(v___x_185_, 1, v_a_181_);
if (v_isShared_184_ == 0)
{
lean_ctor_set_tag(v___x_183_, 1);
lean_ctor_set(v___x_183_, 0, v___x_185_);
v___x_187_ = v___x_183_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_173_ = stack[0].m_obj;
lean_object* v___y_174_ = stack[1].m_obj;
lean_object* v___y_175_ = stack[2].m_obj;
lean_object* v___y_176_ = stack[3].m_obj;
lean_object* v___y_177_ = stack[4].m_obj;
lean_object* v_res_190_;
v_res_190_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(v_msg_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
stack->m_obj
 = v_res_190_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg___boxed(lean_object* v_msg_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(v_msg_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_197_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_box(0);
v___x_199_ = l_Lean_mkSort(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0);
v___x_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__7));
v___x_223_ = l_Lean_stringToMessageData(v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__9));
v___x_226_ = l_Lean_stringToMessageData(v___x_225_);
return v___x_226_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(lean_object* v_goal_227_, lean_object* v_hyp_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_238_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1);
v___x_239_ = 0;
v___x_240_ = lean_box(0);
v___x_241_ = l_Lean_Meta_mkFreshExprMVar(v___x_238_, v___x_239_, v___x_240_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_301_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_301_ == 0)
{
v___x_244_ = v___x_241_;
v_isShared_245_ = v_isSharedCheck_301_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_241_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_301_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
lean_inc(v_a_242_);
if (v_isShared_245_ == 0)
{
lean_ctor_set_tag(v___x_244_, 1);
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_300_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
uint8_t v___x_248_; lean_object* v___x_249_; 
v___x_248_ = 0;
lean_inc(v_hyp_228_);
v___x_249_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v_hyp_228_, v___x_247_, v___x_248_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_299_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_299_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_299_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_299_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v_u_254_; lean_object* v_00_u03c3s_255_; lean_object* v_hyps_256_; lean_object* v_target_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v_u_254_ = lean_ctor_get(v_goal_227_, 0);
lean_inc(v_u_254_);
v_00_u03c3s_255_ = lean_ctor_get(v_goal_227_, 1);
lean_inc_ref_n(v_00_u03c3s_255_, 2);
v_hyps_256_ = lean_ctor_get(v_goal_227_, 2);
lean_inc_ref(v_hyps_256_);
v_target_257_ = lean_ctor_get(v_goal_227_, 3);
lean_inc_ref(v_target_257_);
lean_dec_ref(v_goal_227_);
v___x_258_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2));
v___x_259_ = lean_box(0);
v___x_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_260_, 0, v_u_254_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
lean_inc_ref(v___x_260_);
v___x_261_ = l_Lean_mkConst(v___x_258_, v___x_260_);
v___x_262_ = l_Lean_Expr_app___override(v___x_261_, v_00_u03c3s_255_);
if (v_isShared_253_ == 0)
{
lean_ctor_set_tag(v___x_252_, 1);
lean_ctor_set(v___x_252_, 0, v___x_262_);
v___x_264_ = v___x_252_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_298_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_Meta_mkFreshExprMVar(v___x_264_, v___x_239_, v___x_240_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
lean_dec_ref_known(v___x_265_, 1);
v___x_267_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4));
lean_inc_ref(v___x_260_);
v___x_268_ = l_Lean_mkConst(v___x_267_, v___x_260_);
lean_inc_ref(v_00_u03c3s_255_);
lean_inc(v_a_242_);
v___x_269_ = l_Lean_mkApp3(v___x_268_, v_a_242_, v_00_u03c3s_255_, v_a_266_);
v___x_270_ = lean_box(0);
v___x_271_ = l_Lean_Meta_synthInstance_x3f(v___x_269_, v___x_270_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_289_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_289_ == 0)
{
v___x_274_ = v___x_271_;
v_isShared_275_ = v_isSharedCheck_289_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_271_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_289_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
if (lean_obj_tag(v_a_272_) == 1)
{
lean_object* v_val_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
lean_dec(v_hyp_228_);
v_val_276_ = lean_ctor_get(v_a_272_, 0);
lean_inc(v_val_276_);
lean_dec_ref_known(v_a_272_, 1);
v___x_277_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6));
v___x_278_ = l_Lean_mkConst(v___x_277_, v___x_260_);
v___x_279_ = l_Lean_mkApp6(v___x_278_, v_00_u03c3s_255_, v_a_242_, v_hyps_256_, v_target_257_, v_val_276_, v_a_250_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_279_);
v___x_281_ = v___x_274_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
lean_del_object(v___x_274_);
lean_dec(v_a_272_);
lean_dec_ref_known(v___x_260_, 2);
lean_dec_ref(v_target_257_);
lean_dec_ref(v_hyps_256_);
lean_dec_ref(v_00_u03c3s_255_);
lean_dec(v_a_250_);
lean_dec(v_a_242_);
v___x_283_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8);
v___x_284_ = l_Lean_MessageData_ofSyntax(v_hyp_228_);
v___x_285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10);
v___x_287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(v___x_287_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
return v___x_288_;
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec_ref_known(v___x_260_, 2);
lean_dec_ref(v_target_257_);
lean_dec_ref(v_hyps_256_);
lean_dec_ref(v_00_u03c3s_255_);
lean_dec(v_a_250_);
lean_dec(v_a_242_);
lean_dec(v_hyp_228_);
v_a_290_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_271_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_271_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_260_, 2);
lean_dec_ref(v_target_257_);
lean_dec_ref(v_hyps_256_);
lean_dec_ref(v_00_u03c3s_255_);
lean_dec(v_a_250_);
lean_dec(v_a_242_);
lean_dec(v_hyp_228_);
return v___x_265_;
}
}
}
}
else
{
lean_dec(v_a_242_);
lean_dec(v_hyp_228_);
lean_dec_ref(v_goal_227_);
return v___x_249_;
}
}
}
}
else
{
lean_dec(v_hyp_228_);
lean_dec_ref(v_goal_227_);
return v___x_241_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_227_ = stack[0].m_obj;
lean_object* v_hyp_228_ = stack[1].m_obj;
lean_object* v_a_229_ = stack[2].m_obj;
lean_object* v_a_230_ = stack[3].m_obj;
lean_object* v_a_231_ = stack[4].m_obj;
lean_object* v_a_232_ = stack[5].m_obj;
lean_object* v_a_233_ = stack[6].m_obj;
lean_object* v_a_234_ = stack[7].m_obj;
lean_object* v_a_235_ = stack[8].m_obj;
lean_object* v_a_236_ = stack[9].m_obj;
lean_object* v_res_302_;
v_res_302_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(v_goal_227_, v_hyp_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
stack->m_obj
 = v_res_302_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___boxed(lean_object* v_goal_303_, lean_object* v_hyp_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(v_goal_303_, v_hyp_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
return v_res_314_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0(lean_object* v_00_u03b1_315_, lean_object* v_msg_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(v_msg_316_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
return v___x_326_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_316_ = stack[1].m_obj;
lean_object* v___y_317_ = stack[2].m_obj;
lean_object* v___y_318_ = stack[3].m_obj;
lean_object* v___y_319_ = stack[4].m_obj;
lean_object* v___y_320_ = stack[5].m_obj;
lean_object* v___y_321_ = stack[6].m_obj;
lean_object* v___y_322_ = stack[7].m_obj;
lean_object* v___y_323_ = stack[8].m_obj;
lean_object* v___y_324_ = stack[9].m_obj;
lean_object* v_res_327_;
v_res_327_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0(lean_box(0), v_msg_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___boxed(lean_object* v_00_u03b1_328_, lean_object* v_msg_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0(v_00_u03b1_328_, v_msg_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
return v_res_339_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_box(0);
v___x_341_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
return v___x_342_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg(){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0);
v___x_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_346_;
v_res_346_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg();
stack->m_obj
 = v_res_346_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___boxed(lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg();
return v_res_348_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0(lean_object* v_00_u03b1_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg();
return v___x_359_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_350_ = stack[1].m_obj;
lean_object* v___y_351_ = stack[2].m_obj;
lean_object* v___y_352_ = stack[3].m_obj;
lean_object* v___y_353_ = stack[4].m_obj;
lean_object* v___y_354_ = stack[5].m_obj;
lean_object* v___y_355_ = stack[6].m_obj;
lean_object* v___y_356_ = stack[7].m_obj;
lean_object* v___y_357_ = stack[8].m_obj;
lean_object* v_res_360_;
v_res_360_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0(lean_box(0), v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
stack->m_obj
 = v_res_360_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___boxed(lean_object* v_00_u03b1_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0(v_00_u03b1_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
return v_res_371_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(lean_object* v_e_372_, lean_object* v___y_373_){
_start:
{
uint8_t v___x_375_; 
v___x_375_ = l_Lean_Expr_hasMVar(v_e_372_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v_e_372_);
return v___x_376_;
}
else
{
lean_object* v___x_377_; lean_object* v_mctx_378_; lean_object* v___x_379_; lean_object* v_fst_380_; lean_object* v_snd_381_; lean_object* v___x_382_; lean_object* v_cache_383_; lean_object* v_zetaDeltaFVarIds_384_; lean_object* v_postponed_385_; lean_object* v_diag_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_395_; 
v___x_377_ = lean_st_ref_get(v___y_373_);
v_mctx_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc_ref(v_mctx_378_);
lean_dec(v___x_377_);
v___x_379_ = l_Lean_instantiateMVarsCore(v_mctx_378_, v_e_372_);
v_fst_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_fst_380_);
v_snd_381_ = lean_ctor_get(v___x_379_, 1);
lean_inc(v_snd_381_);
lean_dec_ref(v___x_379_);
v___x_382_ = lean_st_ref_take(v___y_373_);
v_cache_383_ = lean_ctor_get(v___x_382_, 1);
v_zetaDeltaFVarIds_384_ = lean_ctor_get(v___x_382_, 2);
v_postponed_385_ = lean_ctor_get(v___x_382_, 3);
v_diag_386_ = lean_ctor_get(v___x_382_, 4);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; 
v_unused_396_ = lean_ctor_get(v___x_382_, 0);
lean_dec(v_unused_396_);
v___x_388_ = v___x_382_;
v_isShared_389_ = v_isSharedCheck_395_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_diag_386_);
lean_inc(v_postponed_385_);
lean_inc(v_zetaDeltaFVarIds_384_);
lean_inc(v_cache_383_);
lean_dec(v___x_382_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_395_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v_snd_381_);
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_snd_381_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_cache_383_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_zetaDeltaFVarIds_384_);
lean_ctor_set(v_reuseFailAlloc_394_, 3, v_postponed_385_);
lean_ctor_set(v_reuseFailAlloc_394_, 4, v_diag_386_);
v___x_391_ = v_reuseFailAlloc_394_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_st_ref_put(v___y_373_, v___x_391_);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v_fst_380_);
return v___x_393_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_372_ = stack[0].m_obj;
lean_object* v___y_373_ = stack[1].m_obj;
lean_object* v_res_397_;
v_res_397_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(v_e_372_, v___y_373_);
stack->m_obj
 = v_res_397_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg___boxed(lean_object* v_e_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(v_e_398_, v___y_399_);
lean_dec(v___y_399_);
return v_res_401_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1(lean_object* v_e_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(v_e_402_, v___y_408_);
return v___x_412_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_402_ = stack[0].m_obj;
lean_object* v___y_403_ = stack[1].m_obj;
lean_object* v___y_404_ = stack[2].m_obj;
lean_object* v___y_405_ = stack[3].m_obj;
lean_object* v___y_406_ = stack[4].m_obj;
lean_object* v___y_407_ = stack[5].m_obj;
lean_object* v___y_408_ = stack[6].m_obj;
lean_object* v___y_409_ = stack[7].m_obj;
lean_object* v___y_410_ = stack[8].m_obj;
lean_object* v_res_413_;
v_res_413_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1(v_e_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
stack->m_obj
 = v_res_413_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___boxed(lean_object* v_e_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1(v_e_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_424_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0(lean_object* v_x_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
lean_inc(v___y_429_);
lean_inc_ref(v___y_428_);
lean_inc(v___y_427_);
lean_inc_ref(v___y_426_);
v___x_435_ = lean_apply_9(v_x_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, lean_box(0));
return v___x_435_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_425_ = stack[0].m_obj;
lean_object* v___y_426_ = stack[1].m_obj;
lean_object* v___y_427_ = stack[2].m_obj;
lean_object* v___y_428_ = stack[3].m_obj;
lean_object* v___y_429_ = stack[4].m_obj;
lean_object* v___y_430_ = stack[5].m_obj;
lean_object* v___y_431_ = stack[6].m_obj;
lean_object* v___y_432_ = stack[7].m_obj;
lean_object* v___y_433_ = stack[8].m_obj;
lean_object* v_res_436_;
v_res_436_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0(v_x_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
stack->m_obj
 = v_res_436_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0___boxed(lean_object* v_x_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0(v_x_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_447_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(lean_object* v_mvarId_448_, lean_object* v_x_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___f_459_; lean_object* v___x_460_; 
lean_inc(v___y_453_);
lean_inc_ref(v___y_452_);
lean_inc(v___y_451_);
lean_inc_ref(v___y_450_);
v___f_459_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_459_, 0, v_x_449_);
lean_closure_set(v___f_459_, 1, v___y_450_);
lean_closure_set(v___f_459_, 2, v___y_451_);
lean_closure_set(v___f_459_, 3, v___y_452_);
lean_closure_set(v___f_459_, 4, v___y_453_);
v___x_460_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_448_, v___f_459_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
if (lean_obj_tag(v___x_460_) == 0)
{
return v___x_460_;
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_448_ = stack[0].m_obj;
lean_object* v_x_449_ = stack[1].m_obj;
lean_object* v___y_450_ = stack[2].m_obj;
lean_object* v___y_451_ = stack[3].m_obj;
lean_object* v___y_452_ = stack[4].m_obj;
lean_object* v___y_453_ = stack[5].m_obj;
lean_object* v___y_454_ = stack[6].m_obj;
lean_object* v___y_455_ = stack[7].m_obj;
lean_object* v___y_456_ = stack[8].m_obj;
lean_object* v___y_457_ = stack[9].m_obj;
lean_object* v_res_469_;
v_res_469_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(v_mvarId_448_, v_x_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
stack->m_obj
 = v_res_469_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___boxed(lean_object* v_mvarId_470_, lean_object* v_x_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(v_mvarId_470_, v_x_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
return v_res_481_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3(lean_object* v_00_u03b1_482_, lean_object* v_mvarId_483_, lean_object* v_x_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(v_mvarId_483_, v_x_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
return v___x_494_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_483_ = stack[1].m_obj;
lean_object* v_x_484_ = stack[2].m_obj;
lean_object* v___y_485_ = stack[3].m_obj;
lean_object* v___y_486_ = stack[4].m_obj;
lean_object* v___y_487_ = stack[5].m_obj;
lean_object* v___y_488_ = stack[6].m_obj;
lean_object* v___y_489_ = stack[7].m_obj;
lean_object* v___y_490_ = stack[8].m_obj;
lean_object* v___y_491_ = stack[9].m_obj;
lean_object* v___y_492_ = stack[10].m_obj;
lean_object* v_res_495_;
v_res_495_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3(lean_box(0), v_mvarId_483_, v_x_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
stack->m_obj
 = v_res_495_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___boxed(lean_object* v_00_u03b1_496_, lean_object* v_mvarId_497_, lean_object* v_x_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3(v_00_u03b1_496_, v_mvarId_497_, v_x_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_509_, lean_object* v_x_510_, lean_object* v_x_511_, lean_object* v_x_512_){
_start:
{
lean_object* v_ks_513_; lean_object* v_vs_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_538_; 
v_ks_513_ = lean_ctor_get(v_x_509_, 0);
v_vs_514_ = lean_ctor_get(v_x_509_, 1);
v_isSharedCheck_538_ = !lean_is_exclusive(v_x_509_);
if (v_isSharedCheck_538_ == 0)
{
v___x_516_ = v_x_509_;
v_isShared_517_ = v_isSharedCheck_538_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_vs_514_);
lean_inc(v_ks_513_);
lean_dec(v_x_509_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_538_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_array_get_size(v_ks_513_);
v___x_519_ = lean_nat_dec_lt(v_x_510_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
lean_dec(v_x_510_);
v___x_520_ = lean_array_push(v_ks_513_, v_x_511_);
v___x_521_ = lean_array_push(v_vs_514_, v_x_512_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_521_);
lean_ctor_set(v___x_516_, 0, v___x_520_);
v___x_523_ = v___x_516_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
else
{
lean_object* v_k_x27_525_; uint8_t v___x_526_; 
v_k_x27_525_ = lean_array_fget_borrowed(v_ks_513_, v_x_510_);
v___x_526_ = l_Lean_instBEqMVarId_beq(v_x_511_, v_k_x27_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_528_; 
if (v_isShared_517_ == 0)
{
v___x_528_ = v___x_516_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_ks_513_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_vs_514_);
v___x_528_ = v_reuseFailAlloc_532_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(1u);
v___x_530_ = lean_nat_add(v_x_510_, v___x_529_);
lean_dec(v_x_510_);
v_x_509_ = v___x_528_;
v_x_510_ = v___x_530_;
goto _start;
}
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_533_ = lean_array_fset(v_ks_513_, v_x_510_, v_x_511_);
v___x_534_ = lean_array_fset(v_vs_514_, v_x_510_, v_x_512_);
lean_dec(v_x_510_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_534_);
lean_ctor_set(v___x_516_, 0, v___x_533_);
v___x_536_ = v___x_516_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5___redArg(lean_object* v_n_539_, lean_object* v_k_540_, lean_object* v_v_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(v_n_539_, v___x_542_, v_k_540_, v_v_541_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_544_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(lean_object* v_x_545_, size_t v_x_546_, size_t v_x_547_, lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
if (lean_obj_tag(v_x_545_) == 0)
{
lean_object* v_es_550_; size_t v___x_551_; size_t v___x_552_; lean_object* v_j_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_es_550_ = lean_ctor_get(v_x_545_, 0);
v___x_551_ = ((size_t)31ULL);
v___x_552_ = lean_usize_land(v_x_546_, v___x_551_);
v_j_553_ = lean_usize_to_nat(v___x_552_);
v___x_554_ = lean_array_get_size(v_es_550_);
v___x_555_ = lean_nat_dec_lt(v_j_553_, v___x_554_);
if (v___x_555_ == 0)
{
lean_dec(v_j_553_);
lean_dec(v_x_549_);
lean_dec(v_x_548_);
return v_x_545_;
}
else
{
lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_594_; 
lean_inc_ref(v_es_550_);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_545_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v_x_545_, 0);
lean_dec(v_unused_595_);
v___x_557_ = v_x_545_;
v_isShared_558_ = v_isSharedCheck_594_;
goto v_resetjp_556_;
}
else
{
lean_dec(v_x_545_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_594_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_v_559_; lean_object* v___x_560_; lean_object* v_xs_x27_561_; lean_object* v___y_563_; 
v_v_559_ = lean_array_fget(v_es_550_, v_j_553_);
v___x_560_ = lean_box(0);
v_xs_x27_561_ = lean_array_fset(v_es_550_, v_j_553_, v___x_560_);
switch(lean_obj_tag(v_v_559_))
{
case 0:
{
lean_object* v_key_568_; lean_object* v_val_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_579_; 
v_key_568_ = lean_ctor_get(v_v_559_, 0);
v_val_569_ = lean_ctor_get(v_v_559_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_v_559_);
if (v_isSharedCheck_579_ == 0)
{
v___x_571_ = v_v_559_;
v_isShared_572_ = v_isSharedCheck_579_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_val_569_);
lean_inc(v_key_568_);
lean_dec(v_v_559_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_579_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
uint8_t v___x_573_; 
v___x_573_ = l_Lean_instBEqMVarId_beq(v_x_548_, v_key_568_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_del_object(v___x_571_);
v___x_574_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_568_, v_val_569_, v_x_548_, v_x_549_);
v___x_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
v___y_563_ = v___x_575_;
goto v___jp_562_;
}
else
{
lean_object* v___x_577_; 
lean_dec(v_val_569_);
lean_dec(v_key_568_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 1, v_x_549_);
lean_ctor_set(v___x_571_, 0, v_x_548_);
v___x_577_ = v___x_571_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_x_548_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_x_549_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
v___y_563_ = v___x_577_;
goto v___jp_562_;
}
}
}
}
case 1:
{
lean_object* v_node_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_592_; 
v_node_580_ = lean_ctor_get(v_v_559_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v_v_559_);
if (v_isSharedCheck_592_ == 0)
{
v___x_582_ = v_v_559_;
v_isShared_583_ = v_isSharedCheck_592_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_node_580_);
lean_dec(v_v_559_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_592_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
size_t v___x_584_; size_t v___x_585_; size_t v___x_586_; size_t v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_584_ = ((size_t)5ULL);
v___x_585_ = lean_usize_shift_right(v_x_546_, v___x_584_);
v___x_586_ = ((size_t)1ULL);
v___x_587_ = lean_usize_add(v_x_547_, v___x_586_);
v___x_588_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_node_580_, v___x_585_, v___x_587_, v_x_548_, v_x_549_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_588_);
v___x_590_ = v___x_582_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
v___y_563_ = v___x_590_;
goto v___jp_562_;
}
}
}
default: 
{
lean_object* v___x_593_; 
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v_x_548_);
lean_ctor_set(v___x_593_, 1, v_x_549_);
v___y_563_ = v___x_593_;
goto v___jp_562_;
}
}
v___jp_562_:
{
lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_564_ = lean_array_fset(v_xs_x27_561_, v_j_553_, v___y_563_);
lean_dec(v_j_553_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_564_);
v___x_566_ = v___x_557_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
else
{
lean_object* v_ks_596_; lean_object* v_vs_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_615_; 
v_ks_596_ = lean_ctor_get(v_x_545_, 0);
v_vs_597_ = lean_ctor_get(v_x_545_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_x_545_);
if (v_isSharedCheck_615_ == 0)
{
v___x_599_ = v_x_545_;
v_isShared_600_ = v_isSharedCheck_615_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_vs_597_);
lean_inc(v_ks_596_);
lean_dec(v_x_545_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_615_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_ks_596_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_vs_597_);
v___x_602_ = v_reuseFailAlloc_614_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v_newNode_603_; size_t v___x_604_; uint8_t v___x_605_; 
v_newNode_603_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5___redArg(v___x_602_, v_x_548_, v_x_549_);
v___x_604_ = ((size_t)7ULL);
v___x_605_ = lean_usize_dec_le(v___x_604_, v_x_547_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_606_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_603_);
v___x_607_ = lean_unsigned_to_nat(4u);
v___x_608_ = lean_nat_dec_lt(v___x_606_, v___x_607_);
lean_dec(v___x_606_);
if (v___x_608_ == 0)
{
lean_object* v_ks_609_; lean_object* v_vs_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_ks_609_ = lean_ctor_get(v_newNode_603_, 0);
lean_inc_ref(v_ks_609_);
v_vs_610_ = lean_ctor_get(v_newNode_603_, 1);
lean_inc_ref(v_vs_610_);
lean_dec_ref(v_newNode_603_);
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_613_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg(v_x_547_, v_ks_609_, v_vs_610_, v___x_611_, v___x_612_);
lean_dec_ref(v_vs_610_);
lean_dec_ref(v_ks_609_);
return v___x_613_;
}
else
{
return v_newNode_603_;
}
}
else
{
return v_newNode_603_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_545_ = stack[0].m_obj;
size_t v_x_546_ = stack[1].m_num;
size_t v_x_547_ = stack[2].m_num;
lean_object* v_x_548_ = stack[3].m_obj;
lean_object* v_x_549_ = stack[4].m_obj;
lean_object* v_res_616_;
v_res_616_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_x_545_, v_x_546_, v_x_547_, v_x_548_, v_x_549_);
stack->m_obj
 = v_res_616_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg(size_t v_depth_617_, lean_object* v_keys_618_, lean_object* v_vals_619_, lean_object* v_i_620_, lean_object* v_entries_621_){
_start:
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_array_get_size(v_keys_618_);
v___x_623_ = lean_nat_dec_lt(v_i_620_, v___x_622_);
if (v___x_623_ == 0)
{
lean_dec(v_i_620_);
return v_entries_621_;
}
else
{
lean_object* v_k_624_; lean_object* v_v_625_; uint64_t v___x_626_; size_t v_h_627_; size_t v___x_628_; lean_object* v___x_629_; size_t v___x_630_; size_t v___x_631_; size_t v___x_632_; size_t v_h_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_k_624_ = lean_array_fget_borrowed(v_keys_618_, v_i_620_);
v_v_625_ = lean_array_fget_borrowed(v_vals_619_, v_i_620_);
v___x_626_ = l_Lean_instHashableMVarId_hash(v_k_624_);
v_h_627_ = lean_uint64_to_usize(v___x_626_);
v___x_628_ = ((size_t)5ULL);
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = ((size_t)1ULL);
v___x_631_ = lean_usize_sub(v_depth_617_, v___x_630_);
v___x_632_ = lean_usize_mul(v___x_628_, v___x_631_);
v_h_633_ = lean_usize_shift_right(v_h_627_, v___x_632_);
v___x_634_ = lean_nat_add(v_i_620_, v___x_629_);
lean_dec(v_i_620_);
lean_inc(v_v_625_);
lean_inc(v_k_624_);
v___x_635_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_entries_621_, v_h_633_, v_depth_617_, v_k_624_, v_v_625_);
v_i_620_ = v___x_634_;
v_entries_621_ = v___x_635_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_617_ = stack[0].m_num;
lean_object* v_keys_618_ = stack[1].m_obj;
lean_object* v_vals_619_ = stack[2].m_obj;
lean_object* v_i_620_ = stack[3].m_obj;
lean_object* v_entries_621_ = stack[4].m_obj;
lean_object* v_res_637_;
v_res_637_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg(v_depth_617_, v_keys_618_, v_vals_619_, v_i_620_, v_entries_621_);
stack->m_obj
 = v_res_637_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_depth_638_, lean_object* v_keys_639_, lean_object* v_vals_640_, lean_object* v_i_641_, lean_object* v_entries_642_){
_start:
{
size_t v_depth_boxed_643_; lean_object* v_res_644_; 
v_depth_boxed_643_ = lean_unbox_usize(v_depth_638_);
lean_dec(v_depth_638_);
v_res_644_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg(v_depth_boxed_643_, v_keys_639_, v_vals_640_, v_i_641_, v_entries_642_);
lean_dec_ref(v_vals_640_);
lean_dec_ref(v_keys_639_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_645_, lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
size_t v_x_4794__boxed_650_; size_t v_x_4795__boxed_651_; lean_object* v_res_652_; 
v_x_4794__boxed_650_ = lean_unbox_usize(v_x_646_);
lean_dec(v_x_646_);
v_x_4795__boxed_651_ = lean_unbox_usize(v_x_647_);
lean_dec(v_x_647_);
v_res_652_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_x_645_, v_x_4794__boxed_650_, v_x_4795__boxed_651_, v_x_648_, v_x_649_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2___redArg(lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
uint64_t v___x_656_; size_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; 
v___x_656_ = l_Lean_instHashableMVarId_hash(v_x_654_);
v___x_657_ = lean_uint64_to_usize(v___x_656_);
v___x_658_ = ((size_t)1ULL);
v___x_659_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_x_653_, v___x_657_, v___x_658_, v_x_654_, v_x_655_);
return v___x_659_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(lean_object* v_mvarId_660_, lean_object* v_val_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___x_664_; lean_object* v_mctx_665_; lean_object* v_cache_666_; lean_object* v_zetaDeltaFVarIds_667_; lean_object* v_postponed_668_; lean_object* v_diag_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_699_; 
v___x_664_ = lean_st_ref_take(v___y_662_);
v_mctx_665_ = lean_ctor_get(v___x_664_, 0);
v_cache_666_ = lean_ctor_get(v___x_664_, 1);
v_zetaDeltaFVarIds_667_ = lean_ctor_get(v___x_664_, 2);
v_postponed_668_ = lean_ctor_get(v___x_664_, 3);
v_diag_669_ = lean_ctor_get(v___x_664_, 4);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_699_ == 0)
{
v___x_671_ = v___x_664_;
v_isShared_672_ = v_isSharedCheck_699_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_diag_669_);
lean_inc(v_postponed_668_);
lean_inc(v_zetaDeltaFVarIds_667_);
lean_inc(v_cache_666_);
lean_inc(v_mctx_665_);
lean_dec(v___x_664_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_699_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v_depth_673_; lean_object* v_levelAssignDepth_674_; lean_object* v_lmvarCounter_675_; lean_object* v_mvarCounter_676_; lean_object* v_lDecls_677_; lean_object* v_decls_678_; lean_object* v_userNames_679_; lean_object* v_lAssignment_680_; lean_object* v_eAssignment_681_; lean_object* v_dAssignment_682_; lean_object* v_instanceTypedMVars_683_; lean_object* v_synthNormMemo_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_698_; 
v_depth_673_ = lean_ctor_get(v_mctx_665_, 0);
v_levelAssignDepth_674_ = lean_ctor_get(v_mctx_665_, 1);
v_lmvarCounter_675_ = lean_ctor_get(v_mctx_665_, 2);
v_mvarCounter_676_ = lean_ctor_get(v_mctx_665_, 3);
v_lDecls_677_ = lean_ctor_get(v_mctx_665_, 4);
v_decls_678_ = lean_ctor_get(v_mctx_665_, 5);
v_userNames_679_ = lean_ctor_get(v_mctx_665_, 6);
v_lAssignment_680_ = lean_ctor_get(v_mctx_665_, 7);
v_eAssignment_681_ = lean_ctor_get(v_mctx_665_, 8);
v_dAssignment_682_ = lean_ctor_get(v_mctx_665_, 9);
v_instanceTypedMVars_683_ = lean_ctor_get(v_mctx_665_, 10);
v_synthNormMemo_684_ = lean_ctor_get(v_mctx_665_, 11);
v_isSharedCheck_698_ = !lean_is_exclusive(v_mctx_665_);
if (v_isSharedCheck_698_ == 0)
{
v___x_686_ = v_mctx_665_;
v_isShared_687_ = v_isSharedCheck_698_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_synthNormMemo_684_);
lean_inc(v_instanceTypedMVars_683_);
lean_inc(v_dAssignment_682_);
lean_inc(v_eAssignment_681_);
lean_inc(v_lAssignment_680_);
lean_inc(v_userNames_679_);
lean_inc(v_decls_678_);
lean_inc(v_lDecls_677_);
lean_inc(v_mvarCounter_676_);
lean_inc(v_lmvarCounter_675_);
lean_inc(v_levelAssignDepth_674_);
lean_inc(v_depth_673_);
lean_dec(v_mctx_665_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_698_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_688_ = lean_box(0);
v___x_689_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2___redArg(v_eAssignment_681_, v_mvarId_660_, v_val_661_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 8, v___x_689_);
v___x_691_ = v___x_686_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_depth_673_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_levelAssignDepth_674_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_lmvarCounter_675_);
lean_ctor_set(v_reuseFailAlloc_697_, 3, v_mvarCounter_676_);
lean_ctor_set(v_reuseFailAlloc_697_, 4, v_lDecls_677_);
lean_ctor_set(v_reuseFailAlloc_697_, 5, v_decls_678_);
lean_ctor_set(v_reuseFailAlloc_697_, 6, v_userNames_679_);
lean_ctor_set(v_reuseFailAlloc_697_, 7, v_lAssignment_680_);
lean_ctor_set(v_reuseFailAlloc_697_, 8, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_697_, 9, v_dAssignment_682_);
lean_ctor_set(v_reuseFailAlloc_697_, 10, v_instanceTypedMVars_683_);
lean_ctor_set(v_reuseFailAlloc_697_, 11, v_synthNormMemo_684_);
v___x_691_ = v_reuseFailAlloc_697_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_691_);
v___x_693_ = v___x_671_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_cache_666_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_zetaDeltaFVarIds_667_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v_postponed_668_);
lean_ctor_set(v_reuseFailAlloc_696_, 4, v_diag_669_);
v___x_693_ = v_reuseFailAlloc_696_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_st_ref_put(v___y_662_, v___x_693_);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_688_);
return v___x_695_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_660_ = stack[0].m_obj;
lean_object* v_val_661_ = stack[1].m_obj;
lean_object* v___y_662_ = stack[2].m_obj;
lean_object* v_res_700_;
v_res_700_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(v_mvarId_660_, v_val_661_, v___y_662_);
stack->m_obj
 = v_res_700_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg___boxed(lean_object* v_mvarId_701_, lean_object* v_val_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(v_mvarId_701_, v_val_702_, v___y_703_);
lean_dec(v___y_703_);
return v_res_705_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__0));
v___x_708_ = l_Lean_stringToMessageData(v___x_707_);
return v___x_708_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0(lean_object* v_a_709_, lean_object* v___x_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_723_; 
lean_inc(v_a_709_);
v___x_723_ = l_Lean_MVarId_getType(v_a_709_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; lean_object* v_a_726_; lean_object* v___x_727_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
v___x_725_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(v_a_724_, v___y_716_);
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref(v___x_725_);
v___x_727_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_726_);
lean_dec(v_a_726_);
if (lean_obj_tag(v___x_727_) == 1)
{
lean_object* v_val_728_; lean_object* v___x_729_; 
v_val_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc_n(v_val_728_, 2);
lean_dec_ref_known(v___x_727_, 1);
lean_inc(v___x_710_);
v___x_729_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(v_val_728_, v___x_710_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
if (lean_obj_tag(v_a_730_) == 1)
{
lean_object* v_val_731_; lean_object* v___x_732_; 
lean_dec(v_val_728_);
lean_dec(v___x_710_);
v_val_731_ = lean_ctor_get(v_a_730_, 0);
lean_inc(v_val_731_);
lean_dec_ref_known(v_a_730_, 1);
v___x_732_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(v_a_709_, v_val_731_, v___y_716_);
lean_dec_ref(v___x_732_);
goto v___jp_720_;
}
else
{
lean_object* v___x_733_; 
lean_dec(v_a_730_);
v___x_733_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(v_val_728_, v___x_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(v_a_709_, v_a_734_, v___y_716_);
lean_dec_ref(v___x_735_);
goto v___jp_720_;
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v_a_709_);
v_a_736_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_733_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_733_);
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
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_val_728_);
lean_dec(v___x_710_);
lean_dec(v_a_709_);
v_a_744_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_729_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_729_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec(v___x_727_);
lean_dec(v___x_710_);
lean_dec(v_a_709_);
v___x_752_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1);
v___x_753_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(v___x_752_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
return v___x_753_;
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v___x_710_);
lean_dec(v_a_709_);
v_a_754_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_723_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_723_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
v___jp_720_:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_box(0);
v___x_722_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_721_, v___y_712_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
return v___x_722_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_709_ = stack[0].m_obj;
lean_object* v___x_710_ = stack[1].m_obj;
lean_object* v___y_711_ = stack[2].m_obj;
lean_object* v___y_712_ = stack[3].m_obj;
lean_object* v___y_713_ = stack[4].m_obj;
lean_object* v___y_714_ = stack[5].m_obj;
lean_object* v___y_715_ = stack[6].m_obj;
lean_object* v___y_716_ = stack[7].m_obj;
lean_object* v___y_717_ = stack[8].m_obj;
lean_object* v___y_718_ = stack[9].m_obj;
lean_object* v_res_762_;
v_res_762_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0(v_a_709_, v___x_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
stack->m_obj
 = v_res_762_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___boxed(lean_object* v_a_763_, lean_object* v___x_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0(v_a_763_, v___x_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_774_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact(lean_object* v_x_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3));
lean_inc(v_x_783_);
v___x_794_ = l_Lean_Syntax_isOfKind(v_x_783_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
lean_dec(v_x_783_);
v___x_795_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg();
return v___x_795_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_796_ = lean_unsigned_to_nat(1u);
v___x_797_ = l_Lean_Syntax_getArg(v_x_783_, v___x_796_);
lean_dec(v_x_783_);
v___x_798_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_785_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___f_800_; lean_object* v___x_801_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc_n(v_a_799_, 2);
lean_dec_ref_known(v___x_798_, 1);
v___f_800_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___boxed), 11, 2);
lean_closure_set(v___f_800_, 0, v_a_799_);
lean_closure_set(v___f_800_, 1, v___x_797_);
v___x_801_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(v_a_799_, v___f_800_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
return v___x_801_;
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec(v___x_797_);
v_a_802_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_798_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_798_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMExact_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_783_ = stack[0].m_obj;
lean_object* v_a_784_ = stack[1].m_obj;
lean_object* v_a_785_ = stack[2].m_obj;
lean_object* v_a_786_ = stack[3].m_obj;
lean_object* v_a_787_ = stack[4].m_obj;
lean_object* v_a_788_ = stack[5].m_obj;
lean_object* v_a_789_ = stack[6].m_obj;
lean_object* v_a_790_ = stack[7].m_obj;
lean_object* v_a_791_ = stack[8].m_obj;
lean_object* v_res_810_;
v_res_810_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact(v_x_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
stack->m_obj
 = v_res_810_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___boxed(lean_object* v_x_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact(v_x_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
return v_res_821_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2(lean_object* v_mvarId_822_, lean_object* v_val_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(v_mvarId_822_, v_val_823_, v___y_829_);
return v___x_833_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_822_ = stack[0].m_obj;
lean_object* v_val_823_ = stack[1].m_obj;
lean_object* v___y_824_ = stack[2].m_obj;
lean_object* v___y_825_ = stack[3].m_obj;
lean_object* v___y_826_ = stack[4].m_obj;
lean_object* v___y_827_ = stack[5].m_obj;
lean_object* v___y_828_ = stack[6].m_obj;
lean_object* v___y_829_ = stack[7].m_obj;
lean_object* v___y_830_ = stack[8].m_obj;
lean_object* v___y_831_ = stack[9].m_obj;
lean_object* v_res_834_;
v_res_834_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2(v_mvarId_822_, v_val_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
stack->m_obj
 = v_res_834_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___boxed(lean_object* v_mvarId_835_, lean_object* v_val_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2(v_mvarId_835_, v_val_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2(lean_object* v_00_u03b2_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2___redArg(v_x_848_, v_x_849_, v_x_850_);
return v___x_851_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_852_, lean_object* v_x_853_, size_t v_x_854_, size_t v_x_855_, lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_x_853_, v_x_854_, v_x_855_, v_x_856_, v_x_857_);
return v___x_858_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_853_ = stack[1].m_obj;
size_t v_x_854_ = stack[2].m_num;
size_t v_x_855_ = stack[3].m_num;
lean_object* v_x_856_ = stack[4].m_obj;
lean_object* v_x_857_ = stack[5].m_obj;
lean_object* v_res_859_;
v_res_859_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4(lean_box(0), v_x_853_, v_x_854_, v_x_855_, v_x_856_, v_x_857_);
stack->m_obj
 = v_res_859_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
size_t v_x_5470__boxed_866_; size_t v_x_5471__boxed_867_; lean_object* v_res_868_; 
v_x_5470__boxed_866_ = lean_unbox_usize(v_x_862_);
lean_dec(v_x_862_);
v_x_5471__boxed_867_ = lean_unbox_usize(v_x_863_);
lean_dec(v_x_863_);
v_res_868_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4(v_00_u03b2_860_, v_x_861_, v_x_5470__boxed_866_, v_x_5471__boxed_867_, v_x_864_, v_x_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_869_, lean_object* v_n_870_, lean_object* v_k_871_, lean_object* v_v_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5___redArg(v_n_870_, v_k_871_, v_v_872_);
return v___x_873_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_874_, size_t v_depth_875_, lean_object* v_keys_876_, lean_object* v_vals_877_, lean_object* v_heq_878_, lean_object* v_i_879_, lean_object* v_entries_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg(v_depth_875_, v_keys_876_, v_vals_877_, v_i_879_, v_entries_880_);
return v___x_881_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_depth_875_ = stack[1].m_num;
lean_object* v_keys_876_ = stack[2].m_obj;
lean_object* v_vals_877_ = stack[3].m_obj;
lean_object* v_i_879_ = stack[5].m_obj;
lean_object* v_entries_880_ = stack[6].m_obj;
lean_object* v_res_882_;
v_res_882_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6(lean_box(0), v_depth_875_, v_keys_876_, v_vals_877_, lean_box(0), v_i_879_, v_entries_880_);
stack->m_obj
 = v_res_882_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_883_, lean_object* v_depth_884_, lean_object* v_keys_885_, lean_object* v_vals_886_, lean_object* v_heq_887_, lean_object* v_i_888_, lean_object* v_entries_889_){
_start:
{
size_t v_depth_boxed_890_; lean_object* v_res_891_; 
v_depth_boxed_890_ = lean_unbox_usize(v_depth_884_);
lean_dec(v_depth_884_);
v_res_891_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6(v_00_u03b2_883_, v_depth_boxed_890_, v_keys_885_, v_vals_886_, v_heq_887_, v_i_888_, v_entries_889_);
lean_dec_ref(v_vals_886_);
lean_dec_ref(v_keys_885_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_892_, lean_object* v_x_893_, lean_object* v_x_894_, lean_object* v_x_895_, lean_object* v_x_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(v_x_893_, v_x_894_, v_x_895_, v_x_896_);
return v___x_897_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1(){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_909_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_910_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3));
v___x_911_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3));
v___x_912_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___boxed), 10, 0);
v___x_913_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_909_, v___x_910_, v___x_911_, v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_914_;
v_res_914_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1();
stack->m_obj
 = v_res_914_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___boxed(lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1();
return v_res_916_;
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
