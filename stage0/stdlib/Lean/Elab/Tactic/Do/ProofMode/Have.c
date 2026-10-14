// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Have
// Imports: public import Std.Tactic.Do.Syntax public import Lean.Elab.Tactic.Basic import Lean.Elab.Tactic.Do.ProofMode.Focus import Lean.Elab.Tactic.ElabTerm
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_mkApp10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Have"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dup"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Hypothesis "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " not found"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mdup"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__3_value),LEAN_SCALAR_PTR_LITERAL(81, 112, 88, 152, 42, 238, 157, 119)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabMDup"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 237, 91, 55, 155, 74, 73, 223)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "have"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mhave"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 47, 33, 106, 233, 48, 163, 59)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabMHave"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 11, 27, 98, 145, 254, 24, 229)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "replace"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mreplace"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 100, 86, 218, 99, 164, 72, 83)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabMReplace"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 34, 48, 214, 220, 188, 132, 60)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___boxed(lean_object* v_00_u03b1_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0(v_00_u03b1_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(lean_object* v___y_31_){
_start:
{
lean_object* v___x_33_; lean_object* v_ngen_34_; lean_object* v_namePrefix_35_; lean_object* v_idx_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_66_; 
v___x_33_ = lean_st_ref_get(v___y_31_);
v_ngen_34_ = lean_ctor_get(v___x_33_, 2);
lean_inc_ref(v_ngen_34_);
lean_dec(v___x_33_);
v_namePrefix_35_ = lean_ctor_get(v_ngen_34_, 0);
v_idx_36_ = lean_ctor_get(v_ngen_34_, 1);
v_isSharedCheck_66_ = !lean_is_exclusive(v_ngen_34_);
if (v_isSharedCheck_66_ == 0)
{
v___x_38_ = v_ngen_34_;
v_isShared_39_ = v_isSharedCheck_66_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_idx_36_);
lean_inc(v_namePrefix_35_);
lean_dec(v_ngen_34_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_66_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v_r_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_44_; 
lean_inc(v_idx_36_);
lean_inc(v_namePrefix_35_);
v_r_40_ = l_Lean_Name_num___override(v_namePrefix_35_, v_idx_36_);
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = lean_nat_add(v_idx_36_, v___x_41_);
lean_dec(v_idx_36_);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 1, v___x_42_);
v___x_44_ = v___x_38_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_namePrefix_35_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v___x_42_);
v___x_44_ = v_reuseFailAlloc_65_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
lean_object* v___x_45_; lean_object* v_env_46_; lean_object* v_nextMacroScope_47_; lean_object* v_auxDeclNGen_48_; lean_object* v_traceState_49_; lean_object* v_cache_50_; lean_object* v_recordedDeps_51_; lean_object* v_messages_52_; lean_object* v_infoState_53_; lean_object* v_snapshotTasks_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_63_; 
v___x_45_ = lean_st_ref_take(v___y_31_);
v_env_46_ = lean_ctor_get(v___x_45_, 0);
v_nextMacroScope_47_ = lean_ctor_get(v___x_45_, 1);
v_auxDeclNGen_48_ = lean_ctor_get(v___x_45_, 3);
v_traceState_49_ = lean_ctor_get(v___x_45_, 4);
v_cache_50_ = lean_ctor_get(v___x_45_, 5);
v_recordedDeps_51_ = lean_ctor_get(v___x_45_, 6);
v_messages_52_ = lean_ctor_get(v___x_45_, 7);
v_infoState_53_ = lean_ctor_get(v___x_45_, 8);
v_snapshotTasks_54_ = lean_ctor_get(v___x_45_, 9);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_63_ == 0)
{
lean_object* v_unused_64_; 
v_unused_64_ = lean_ctor_get(v___x_45_, 2);
lean_dec(v_unused_64_);
v___x_56_ = v___x_45_;
v_isShared_57_ = v_isSharedCheck_63_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_snapshotTasks_54_);
lean_inc(v_infoState_53_);
lean_inc(v_messages_52_);
lean_inc(v_recordedDeps_51_);
lean_inc(v_cache_50_);
lean_inc(v_traceState_49_);
lean_inc(v_auxDeclNGen_48_);
lean_inc(v_nextMacroScope_47_);
lean_inc(v_env_46_);
lean_dec(v___x_45_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_63_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 2, v___x_44_);
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_env_46_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v_nextMacroScope_47_);
lean_ctor_set(v_reuseFailAlloc_62_, 2, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_62_, 3, v_auxDeclNGen_48_);
lean_ctor_set(v_reuseFailAlloc_62_, 4, v_traceState_49_);
lean_ctor_set(v_reuseFailAlloc_62_, 5, v_cache_50_);
lean_ctor_set(v_reuseFailAlloc_62_, 6, v_recordedDeps_51_);
lean_ctor_set(v_reuseFailAlloc_62_, 7, v_messages_52_);
lean_ctor_set(v_reuseFailAlloc_62_, 8, v_infoState_53_);
lean_ctor_set(v_reuseFailAlloc_62_, 9, v_snapshotTasks_54_);
v___x_59_ = v_reuseFailAlloc_62_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_st_ref_put(v___y_31_, v___x_59_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_r_40_);
return v___x_61_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg___boxed(lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_67_);
lean_dec(v___y_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1(lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___boxed(lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1(v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0(lean_object* v_x_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___x_100_; 
lean_inc(v___y_94_);
lean_inc_ref(v___y_93_);
lean_inc(v___y_92_);
lean_inc_ref(v___y_91_);
v___x_100_ = lean_apply_9(v_x_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, lean_box(0));
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0___boxed(lean_object* v_x_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0(v_x_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(lean_object* v_mvarId_112_, lean_object* v_x_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v___f_123_; lean_object* v___x_124_; 
lean_inc(v___y_117_);
lean_inc_ref(v___y_116_);
lean_inc(v___y_115_);
lean_inc_ref(v___y_114_);
v___f_123_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_123_, 0, v_x_113_);
lean_closure_set(v___f_123_, 1, v___y_114_);
lean_closure_set(v___f_123_, 2, v___y_115_);
lean_closure_set(v___f_123_, 3, v___y_116_);
lean_closure_set(v___f_123_, 4, v___y_117_);
v___x_124_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_112_, v___f_123_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
if (lean_obj_tag(v___x_124_) == 0)
{
return v___x_124_;
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___boxed(lean_object* v_mvarId_133_, lean_object* v_x_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_mvarId_133_, v_x_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4(lean_object* v_00_u03b1_145_, lean_object* v_mvarId_146_, lean_object* v_x_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_mvarId_146_, v_x_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___boxed(lean_object* v_00_u03b1_158_, lean_object* v_mvarId_159_, lean_object* v_x_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4(v_00_u03b1_158_, v_mvarId_159_, v_x_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_x_171_, lean_object* v_x_172_, lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
lean_object* v_ks_175_; lean_object* v_vs_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_200_; 
v_ks_175_ = lean_ctor_get(v_x_171_, 0);
v_vs_176_ = lean_ctor_get(v_x_171_, 1);
v_isSharedCheck_200_ = !lean_is_exclusive(v_x_171_);
if (v_isSharedCheck_200_ == 0)
{
v___x_178_ = v_x_171_;
v_isShared_179_ = v_isSharedCheck_200_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_vs_176_);
lean_inc(v_ks_175_);
lean_dec(v_x_171_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_200_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = lean_array_get_size(v_ks_175_);
v___x_181_ = lean_nat_dec_lt(v_x_172_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
lean_dec(v_x_172_);
v___x_182_ = lean_array_push(v_ks_175_, v_x_173_);
v___x_183_ = lean_array_push(v_vs_176_, v_x_174_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___x_183_);
lean_ctor_set(v___x_178_, 0, v___x_182_);
v___x_185_ = v___x_178_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
else
{
lean_object* v_k_x27_187_; uint8_t v___x_188_; 
v_k_x27_187_ = lean_array_fget_borrowed(v_ks_175_, v_x_172_);
v___x_188_ = l_Lean_instBEqMVarId_beq(v_x_173_, v_k_x27_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_190_; 
if (v_isShared_179_ == 0)
{
v___x_190_ = v___x_178_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_ks_175_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_vs_176_);
v___x_190_ = v_reuseFailAlloc_194_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = lean_nat_add(v_x_172_, v___x_191_);
lean_dec(v_x_172_);
v_x_171_ = v___x_190_;
v_x_172_ = v___x_192_;
goto _start;
}
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_195_ = lean_array_fset(v_ks_175_, v_x_172_, v_x_173_);
v___x_196_ = lean_array_fset(v_vs_176_, v_x_172_, v_x_174_);
lean_dec(v_x_172_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___x_196_);
lean_ctor_set(v___x_178_, 0, v___x_195_);
v___x_198_ = v___x_178_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(lean_object* v_n_201_, lean_object* v_k_202_, lean_object* v_v_203_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_n_201_, v___x_204_, v_k_202_, v_v_203_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(lean_object* v_x_207_, size_t v_x_208_, size_t v_x_209_, lean_object* v_x_210_, lean_object* v_x_211_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
lean_object* v_es_212_; size_t v___x_213_; size_t v___x_214_; lean_object* v_j_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_es_212_ = lean_ctor_get(v_x_207_, 0);
v___x_213_ = ((size_t)31ULL);
v___x_214_ = lean_usize_land(v_x_208_, v___x_213_);
v_j_215_ = lean_usize_to_nat(v___x_214_);
v___x_216_ = lean_array_get_size(v_es_212_);
v___x_217_ = lean_nat_dec_lt(v_j_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_dec(v_j_215_);
lean_dec(v_x_211_);
lean_dec(v_x_210_);
return v_x_207_;
}
else
{
lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_256_; 
lean_inc_ref(v_es_212_);
v_isSharedCheck_256_ = !lean_is_exclusive(v_x_207_);
if (v_isSharedCheck_256_ == 0)
{
lean_object* v_unused_257_; 
v_unused_257_ = lean_ctor_get(v_x_207_, 0);
lean_dec(v_unused_257_);
v___x_219_ = v_x_207_;
v_isShared_220_ = v_isSharedCheck_256_;
goto v_resetjp_218_;
}
else
{
lean_dec(v_x_207_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_256_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_v_221_; lean_object* v___x_222_; lean_object* v_xs_x27_223_; lean_object* v___y_225_; 
v_v_221_ = lean_array_fget(v_es_212_, v_j_215_);
v___x_222_ = lean_box(0);
v_xs_x27_223_ = lean_array_fset(v_es_212_, v_j_215_, v___x_222_);
switch(lean_obj_tag(v_v_221_))
{
case 0:
{
lean_object* v_key_230_; lean_object* v_val_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_241_; 
v_key_230_ = lean_ctor_get(v_v_221_, 0);
v_val_231_ = lean_ctor_get(v_v_221_, 1);
v_isSharedCheck_241_ = !lean_is_exclusive(v_v_221_);
if (v_isSharedCheck_241_ == 0)
{
v___x_233_ = v_v_221_;
v_isShared_234_ = v_isSharedCheck_241_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_val_231_);
lean_inc(v_key_230_);
lean_dec(v_v_221_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_241_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
uint8_t v___x_235_; 
v___x_235_ = l_Lean_instBEqMVarId_beq(v_x_210_, v_key_230_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_del_object(v___x_233_);
v___x_236_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_230_, v_val_231_, v_x_210_, v_x_211_);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
v___y_225_ = v___x_237_;
goto v___jp_224_;
}
else
{
lean_object* v___x_239_; 
lean_dec(v_val_231_);
lean_dec(v_key_230_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v_x_211_);
lean_ctor_set(v___x_233_, 0, v_x_210_);
v___x_239_ = v___x_233_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_x_210_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_x_211_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
v___y_225_ = v___x_239_;
goto v___jp_224_;
}
}
}
}
case 1:
{
lean_object* v_node_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_254_; 
v_node_242_ = lean_ctor_get(v_v_221_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v_v_221_);
if (v_isSharedCheck_254_ == 0)
{
v___x_244_ = v_v_221_;
v_isShared_245_ = v_isSharedCheck_254_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_node_242_);
lean_dec(v_v_221_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_254_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_246_ = ((size_t)5ULL);
v___x_247_ = lean_usize_shift_right(v_x_208_, v___x_246_);
v___x_248_ = ((size_t)1ULL);
v___x_249_ = lean_usize_add(v_x_209_, v___x_248_);
v___x_250_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_node_242_, v___x_247_, v___x_249_, v_x_210_, v_x_211_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_250_);
v___x_252_ = v___x_244_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
v___y_225_ = v___x_252_;
goto v___jp_224_;
}
}
}
default: 
{
lean_object* v___x_255_; 
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v_x_210_);
lean_ctor_set(v___x_255_, 1, v_x_211_);
v___y_225_ = v___x_255_;
goto v___jp_224_;
}
}
v___jp_224_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_array_fset(v_xs_x27_223_, v_j_215_, v___y_225_);
lean_dec(v_j_215_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_226_);
v___x_228_ = v___x_219_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
}
else
{
lean_object* v_ks_258_; lean_object* v_vs_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_277_; 
v_ks_258_ = lean_ctor_get(v_x_207_, 0);
v_vs_259_ = lean_ctor_get(v_x_207_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_207_);
if (v_isSharedCheck_277_ == 0)
{
v___x_261_ = v_x_207_;
v_isShared_262_ = v_isSharedCheck_277_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_vs_259_);
lean_inc(v_ks_258_);
lean_dec(v_x_207_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_277_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_ks_258_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_vs_259_);
v___x_264_ = v_reuseFailAlloc_276_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v_newNode_265_; size_t v___x_266_; uint8_t v___x_267_; 
v_newNode_265_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(v___x_264_, v_x_210_, v_x_211_);
v___x_266_ = ((size_t)7ULL);
v___x_267_ = lean_usize_dec_le(v___x_266_, v_x_209_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_268_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_265_);
v___x_269_ = lean_unsigned_to_nat(4u);
v___x_270_ = lean_nat_dec_lt(v___x_268_, v___x_269_);
lean_dec(v___x_268_);
if (v___x_270_ == 0)
{
lean_object* v_ks_271_; lean_object* v_vs_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v_ks_271_ = lean_ctor_get(v_newNode_265_, 0);
lean_inc_ref(v_ks_271_);
v_vs_272_ = lean_ctor_get(v_newNode_265_, 1);
lean_inc_ref(v_vs_272_);
lean_dec_ref(v_newNode_265_);
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_275_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_x_209_, v_ks_271_, v_vs_272_, v___x_273_, v___x_274_);
lean_dec_ref(v_vs_272_);
lean_dec_ref(v_ks_271_);
return v___x_275_;
}
else
{
return v_newNode_265_;
}
}
else
{
return v_newNode_265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(size_t v_depth_278_, lean_object* v_keys_279_, lean_object* v_vals_280_, lean_object* v_i_281_, lean_object* v_entries_282_){
_start:
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_array_get_size(v_keys_279_);
v___x_284_ = lean_nat_dec_lt(v_i_281_, v___x_283_);
if (v___x_284_ == 0)
{
lean_dec(v_i_281_);
return v_entries_282_;
}
else
{
lean_object* v_k_285_; lean_object* v_v_286_; uint64_t v___x_287_; size_t v_h_288_; size_t v___x_289_; lean_object* v___x_290_; size_t v___x_291_; size_t v___x_292_; size_t v___x_293_; size_t v_h_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_k_285_ = lean_array_fget_borrowed(v_keys_279_, v_i_281_);
v_v_286_ = lean_array_fget_borrowed(v_vals_280_, v_i_281_);
v___x_287_ = l_Lean_instHashableMVarId_hash(v_k_285_);
v_h_288_ = lean_uint64_to_usize(v___x_287_);
v___x_289_ = ((size_t)5ULL);
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = ((size_t)1ULL);
v___x_292_ = lean_usize_sub(v_depth_278_, v___x_291_);
v___x_293_ = lean_usize_mul(v___x_289_, v___x_292_);
v_h_294_ = lean_usize_shift_right(v_h_288_, v___x_293_);
v___x_295_ = lean_nat_add(v_i_281_, v___x_290_);
lean_dec(v_i_281_);
lean_inc(v_v_286_);
lean_inc(v_k_285_);
v___x_296_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_entries_282_, v_h_294_, v_depth_278_, v_k_285_, v_v_286_);
v_i_281_ = v___x_295_;
v_entries_282_ = v___x_296_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_298_, lean_object* v_keys_299_, lean_object* v_vals_300_, lean_object* v_i_301_, lean_object* v_entries_302_){
_start:
{
size_t v_depth_boxed_303_; lean_object* v_res_304_; 
v_depth_boxed_303_ = lean_unbox_usize(v_depth_298_);
lean_dec(v_depth_298_);
v_res_304_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_boxed_303_, v_keys_299_, v_vals_300_, v_i_301_, v_entries_302_);
lean_dec_ref(v_vals_300_);
lean_dec_ref(v_keys_299_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
size_t v_x_6783__boxed_310_; size_t v_x_6784__boxed_311_; lean_object* v_res_312_; 
v_x_6783__boxed_310_ = lean_unbox_usize(v_x_306_);
lean_dec(v_x_306_);
v_x_6784__boxed_311_ = lean_unbox_usize(v_x_307_);
lean_dec(v_x_307_);
v_res_312_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_305_, v_x_6783__boxed_310_, v_x_6784__boxed_311_, v_x_308_, v_x_309_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
uint64_t v___x_316_; size_t v___x_317_; size_t v___x_318_; lean_object* v___x_319_; 
v___x_316_ = l_Lean_instHashableMVarId_hash(v_x_314_);
v___x_317_ = lean_uint64_to_usize(v___x_316_);
v___x_318_ = ((size_t)1ULL);
v___x_319_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_313_, v___x_317_, v___x_318_, v_x_314_, v_x_315_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(lean_object* v_mvarId_320_, lean_object* v_val_321_, lean_object* v___y_322_){
_start:
{
lean_object* v___x_324_; lean_object* v_mctx_325_; lean_object* v_cache_326_; lean_object* v_zetaDeltaFVarIds_327_; lean_object* v_postponed_328_; lean_object* v_diag_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_359_; 
v___x_324_ = lean_st_ref_take(v___y_322_);
v_mctx_325_ = lean_ctor_get(v___x_324_, 0);
v_cache_326_ = lean_ctor_get(v___x_324_, 1);
v_zetaDeltaFVarIds_327_ = lean_ctor_get(v___x_324_, 2);
v_postponed_328_ = lean_ctor_get(v___x_324_, 3);
v_diag_329_ = lean_ctor_get(v___x_324_, 4);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_359_ == 0)
{
v___x_331_ = v___x_324_;
v_isShared_332_ = v_isSharedCheck_359_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_diag_329_);
lean_inc(v_postponed_328_);
lean_inc(v_zetaDeltaFVarIds_327_);
lean_inc(v_cache_326_);
lean_inc(v_mctx_325_);
lean_dec(v___x_324_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_359_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v_depth_333_; lean_object* v_levelAssignDepth_334_; lean_object* v_lmvarCounter_335_; lean_object* v_mvarCounter_336_; lean_object* v_lDecls_337_; lean_object* v_decls_338_; lean_object* v_userNames_339_; lean_object* v_lAssignment_340_; lean_object* v_eAssignment_341_; lean_object* v_dAssignment_342_; lean_object* v_instanceTypedMVars_343_; lean_object* v_synthNormMemo_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_358_; 
v_depth_333_ = lean_ctor_get(v_mctx_325_, 0);
v_levelAssignDepth_334_ = lean_ctor_get(v_mctx_325_, 1);
v_lmvarCounter_335_ = lean_ctor_get(v_mctx_325_, 2);
v_mvarCounter_336_ = lean_ctor_get(v_mctx_325_, 3);
v_lDecls_337_ = lean_ctor_get(v_mctx_325_, 4);
v_decls_338_ = lean_ctor_get(v_mctx_325_, 5);
v_userNames_339_ = lean_ctor_get(v_mctx_325_, 6);
v_lAssignment_340_ = lean_ctor_get(v_mctx_325_, 7);
v_eAssignment_341_ = lean_ctor_get(v_mctx_325_, 8);
v_dAssignment_342_ = lean_ctor_get(v_mctx_325_, 9);
v_instanceTypedMVars_343_ = lean_ctor_get(v_mctx_325_, 10);
v_synthNormMemo_344_ = lean_ctor_get(v_mctx_325_, 11);
v_isSharedCheck_358_ = !lean_is_exclusive(v_mctx_325_);
if (v_isSharedCheck_358_ == 0)
{
v___x_346_ = v_mctx_325_;
v_isShared_347_ = v_isSharedCheck_358_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_synthNormMemo_344_);
lean_inc(v_instanceTypedMVars_343_);
lean_inc(v_dAssignment_342_);
lean_inc(v_eAssignment_341_);
lean_inc(v_lAssignment_340_);
lean_inc(v_userNames_339_);
lean_inc(v_decls_338_);
lean_inc(v_lDecls_337_);
lean_inc(v_mvarCounter_336_);
lean_inc(v_lmvarCounter_335_);
lean_inc(v_levelAssignDepth_334_);
lean_inc(v_depth_333_);
lean_dec(v_mctx_325_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_358_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_348_ = lean_box(0);
v___x_349_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(v_eAssignment_341_, v_mvarId_320_, v_val_321_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 8, v___x_349_);
v___x_351_ = v___x_346_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_depth_333_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_levelAssignDepth_334_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_lmvarCounter_335_);
lean_ctor_set(v_reuseFailAlloc_357_, 3, v_mvarCounter_336_);
lean_ctor_set(v_reuseFailAlloc_357_, 4, v_lDecls_337_);
lean_ctor_set(v_reuseFailAlloc_357_, 5, v_decls_338_);
lean_ctor_set(v_reuseFailAlloc_357_, 6, v_userNames_339_);
lean_ctor_set(v_reuseFailAlloc_357_, 7, v_lAssignment_340_);
lean_ctor_set(v_reuseFailAlloc_357_, 8, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_357_, 9, v_dAssignment_342_);
lean_ctor_set(v_reuseFailAlloc_357_, 10, v_instanceTypedMVars_343_);
lean_ctor_set(v_reuseFailAlloc_357_, 11, v_synthNormMemo_344_);
v___x_351_ = v_reuseFailAlloc_357_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_353_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_351_);
v___x_353_ = v___x_331_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_cache_326_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_zetaDeltaFVarIds_327_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v_postponed_328_);
lean_ctor_set(v_reuseFailAlloc_356_, 4, v_diag_329_);
v___x_353_ = v_reuseFailAlloc_356_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_st_ref_put(v___y_322_, v___x_353_);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_348_);
return v___x_355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg___boxed(lean_object* v_mvarId_360_, lean_object* v_val_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_mvarId_360_, v_val_361_, v___y_362_);
lean_dec(v___y_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(lean_object* v_msgData_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; lean_object* v_env_372_; uint8_t v___x_373_; lean_object* v_env_374_; lean_object* v___x_375_; lean_object* v_toCold_376_; lean_object* v_mctx_377_; lean_object* v_lctx_378_; lean_object* v_options_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_371_ = lean_st_ref_get(v___y_369_);
v_env_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc_ref(v_env_372_);
lean_dec(v___x_371_);
v___x_373_ = 0;
v_env_374_ = l_Lean_Environment_setRecordingDeps(v_env_372_, v___x_373_);
v___x_375_ = lean_st_ref_get(v___y_367_);
v_toCold_376_ = lean_ctor_get(v___y_368_, 0);
v_mctx_377_ = lean_ctor_get(v___x_375_, 0);
lean_inc_ref(v_mctx_377_);
lean_dec(v___x_375_);
v_lctx_378_ = lean_ctor_get(v___y_366_, 2);
v_options_379_ = lean_ctor_get(v_toCold_376_, 2);
lean_inc_ref(v_options_379_);
lean_inc_ref(v_lctx_378_);
v___x_380_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_380_, 0, v_env_374_);
lean_ctor_set(v___x_380_, 1, v_mctx_377_);
lean_ctor_set(v___x_380_, 2, v_lctx_378_);
lean_ctor_set(v___x_380_, 3, v_options_379_);
v___x_381_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v_msgData_365_);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4___boxed(lean_object* v_msgData_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(v_msgData_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(lean_object* v_msg_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_ref_396_; lean_object* v___x_397_; lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_406_; 
v_ref_396_ = lean_ctor_get(v___y_393_, 2);
v___x_397_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(v_msg_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_406_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
lean_inc(v_ref_396_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_ref_396_);
lean_ctor_set(v___x_402_, 1, v_a_398_);
if (v_isShared_401_ == 0)
{
lean_ctor_set_tag(v___x_400_, 1);
lean_ctor_set(v___x_400_, 0, v___x_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg___boxed(lean_object* v_msg_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v_msg_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
return v_res_413_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__5));
v___x_421_ = l_Lean_stringToMessageData(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__7));
v___x_424_ = l_Lean_stringToMessageData(v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0(lean_object* v___x_425_, lean_object* v_snd_426_, lean_object* v___x_427_, lean_object* v___x_428_, uint8_t v___x_429_, lean_object* v___x_430_, lean_object* v_fst_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
if (lean_obj_tag(v___x_425_) == 1)
{
lean_object* v_val_441_; lean_object* v_u_442_; lean_object* v_00_u03c3s_443_; lean_object* v_hyps_444_; lean_object* v_target_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_495_; 
v_val_441_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_val_441_);
lean_dec_ref_known(v___x_425_, 1);
v_u_442_ = lean_ctor_get(v_snd_426_, 0);
v_00_u03c3s_443_ = lean_ctor_get(v_snd_426_, 1);
v_hyps_444_ = lean_ctor_get(v_snd_426_, 2);
v_target_445_ = lean_ctor_get(v_snd_426_, 3);
v_isSharedCheck_495_ = !lean_is_exclusive(v_snd_426_);
if (v_isSharedCheck_495_ == 0)
{
v___x_447_ = v_snd_426_;
v_isShared_448_ = v_isSharedCheck_495_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_target_445_);
lean_inc(v_hyps_444_);
lean_inc(v_00_u03c3s_443_);
lean_inc(v_u_442_);
lean_dec(v_snd_426_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_495_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v_focusHyp_449_; lean_object* v_restHyps_450_; lean_object* v_proof_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_494_; 
v_focusHyp_449_ = lean_ctor_get(v_val_441_, 0);
v_restHyps_450_ = lean_ctor_get(v_val_441_, 1);
v_proof_451_ = lean_ctor_get(v_val_441_, 2);
v_isSharedCheck_494_ = !lean_is_exclusive(v_val_441_);
if (v_isSharedCheck_494_ == 0)
{
v___x_453_ = v_val_441_;
v_isShared_454_ = v_isSharedCheck_494_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_proof_451_);
lean_inc(v_restHyps_450_);
lean_inc(v_focusHyp_449_);
lean_dec(v_val_441_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_494_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v_a_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_455_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_439_);
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref(v___x_455_);
v___x_457_ = l_Lean_Syntax_getId(v___x_427_);
v___x_458_ = l_Lean_Expr_consumeMData(v_focusHyp_449_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 2, v___x_458_);
lean_ctor_set(v___x_453_, 1, v_a_456_);
lean_ctor_set(v___x_453_, 0, v___x_457_);
v___x_460_ = v___x_453_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_a_456_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v___x_458_);
v___x_460_ = v_reuseFailAlloc_493_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; 
lean_inc_ref(v___x_460_);
lean_inc_ref(v_00_u03c3s_443_);
v___x_461_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v___x_428_, v_00_u03c3s_443_, v___x_460_, v___x_429_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
lean_dec_ref_known(v___x_461_, 1);
v___x_462_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_460_);
lean_inc_ref(v_hyps_444_);
lean_inc_ref_n(v_00_u03c3s_443_, 2);
lean_inc_n(v_u_442_, 2);
v___x_463_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_442_, v_00_u03c3s_443_, v_hyps_444_, v___x_462_);
lean_inc_ref(v_target_445_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 2, v___x_463_);
v___x_465_ = v___x_447_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_u_442_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_00_u03c3s_443_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v_target_445_);
v___x_465_ = v_reuseFailAlloc_492_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_465_);
v___x_467_ = lean_box(0);
v___x_468_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_466_, v___x_467_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc_n(v_a_469_, 2);
lean_dec_ref_known(v___x_468_, 1);
v___x_470_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0));
v___x_471_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1));
v___x_472_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2));
v___x_473_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3));
v___x_474_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__4));
v___x_475_ = l_Lean_Name_mkStr6(v___x_470_, v___x_471_, v___x_472_, v___x_430_, v___x_473_, v___x_474_);
v___x_476_ = lean_box(0);
v___x_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_477_, 0, v_u_442_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = l_Lean_mkConst(v___x_475_, v___x_477_);
v___x_479_ = l_Lean_mkApp7(v___x_478_, v_00_u03c3s_443_, v_hyps_444_, v_restHyps_450_, v_focusHyp_449_, v_target_445_, v_proof_451_, v_a_469_);
v___x_480_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_431_, v___x_479_, v___y_437_);
lean_dec_ref(v___x_480_);
v___x_481_ = l_Lean_Expr_mvarId_x21(v_a_469_);
lean_dec(v_a_469_);
v___x_482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v___x_476_);
v___x_483_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_482_, v___y_433_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
return v___x_483_;
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec_ref(v_proof_451_);
lean_dec_ref(v_restHyps_450_);
lean_dec_ref(v_focusHyp_449_);
lean_dec_ref(v_target_445_);
lean_dec_ref(v_hyps_444_);
lean_dec_ref(v_00_u03c3s_443_);
lean_dec(v_u_442_);
lean_dec(v_fst_431_);
lean_dec_ref(v___x_430_);
v_a_484_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_468_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_468_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_460_);
lean_dec_ref(v_proof_451_);
lean_dec_ref(v_restHyps_450_);
lean_dec_ref(v_focusHyp_449_);
lean_del_object(v___x_447_);
lean_dec_ref(v_target_445_);
lean_dec_ref(v_hyps_444_);
lean_dec_ref(v_00_u03c3s_443_);
lean_dec(v_u_442_);
lean_dec(v_fst_431_);
lean_dec_ref(v___x_430_);
return v___x_461_;
}
}
}
}
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec(v_fst_431_);
lean_dec_ref(v___x_430_);
lean_dec_ref(v_snd_426_);
lean_dec(v___x_425_);
v___x_496_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6);
v___x_497_ = l_Lean_MessageData_ofSyntax(v___x_428_);
v___x_498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8);
v___x_500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v___x_500_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___boxed(lean_object* v___x_502_, lean_object* v_snd_503_, lean_object* v___x_504_, lean_object* v___x_505_, lean_object* v___x_506_, lean_object* v___x_507_, lean_object* v_fst_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
uint8_t v___x_7081__boxed_518_; lean_object* v_res_519_; 
v___x_7081__boxed_518_ = lean_unbox(v___x_506_);
v_res_519_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0(v___x_502_, v_snd_503_, v___x_504_, v___x_505_, v___x_7081__boxed_518_, v___x_507_, v_fst_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___x_504_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup(lean_object* v_x_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2));
v___x_543_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4));
lean_inc(v_x_532_);
v___x_544_ = l_Lean_Syntax_isOfKind(v_x_532_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; 
lean_dec(v_x_532_);
v___x_545_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_545_;
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_546_ = lean_unsigned_to_nat(1u);
v___x_547_ = l_Lean_Syntax_getArg(v_x_532_, v___x_546_);
v___x_548_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__6));
lean_inc(v___x_547_);
v___x_549_ = l_Lean_Syntax_isOfKind(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
lean_dec(v___x_547_);
lean_dec(v_x_532_);
v___x_550_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_550_;
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_551_ = lean_unsigned_to_nat(3u);
v___x_552_ = l_Lean_Syntax_getArg(v_x_532_, v___x_551_);
lean_dec(v_x_532_);
lean_inc(v___x_552_);
v___x_553_ = l_Lean_Syntax_isOfKind(v___x_552_, v___x_548_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
lean_dec(v___x_552_);
lean_dec(v___x_547_);
v___x_554_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_554_;
}
else
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v_fst_557_; lean_object* v_snd_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___y_562_; lean_object* v___x_563_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
lean_dec_ref_known(v___x_555_, 1);
v_fst_557_ = lean_ctor_get(v_a_556_, 0);
lean_inc_n(v_fst_557_, 2);
v_snd_558_ = lean_ctor_get(v_a_556_, 1);
lean_inc_n(v_snd_558_, 2);
lean_dec(v_a_556_);
v___x_559_ = l_Lean_Syntax_getId(v___x_547_);
v___x_560_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_558_, v___x_559_);
lean_dec(v___x_559_);
v___x_561_ = lean_box(v___x_553_);
v___y_562_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___boxed), 16, 7);
lean_closure_set(v___y_562_, 0, v___x_560_);
lean_closure_set(v___y_562_, 1, v_snd_558_);
lean_closure_set(v___y_562_, 2, v___x_552_);
lean_closure_set(v___y_562_, 3, v___x_547_);
lean_closure_set(v___y_562_, 4, v___x_561_);
lean_closure_set(v___y_562_, 5, v___x_542_);
lean_closure_set(v___y_562_, 6, v_fst_557_);
v___x_563_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_557_, v___y_562_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
return v___x_563_;
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec(v___x_552_);
lean_dec(v___x_547_);
v_a_564_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_555_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_555_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___boxed(lean_object* v_x_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup(v_x_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2(lean_object* v_mvarId_583_, lean_object* v_val_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_mvarId_583_, v_val_584_, v___y_590_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___boxed(lean_object* v_mvarId_595_, lean_object* v_val_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2(v_mvarId_595_, v_val_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3(lean_object* v_00_u03b1_607_, lean_object* v_msg_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v_msg_608_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___boxed(lean_object* v_00_u03b1_619_, lean_object* v_msg_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3(v_00_u03b1_619_, v_msg_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2(lean_object* v_00_u03b2_631_, lean_object* v_x_632_, lean_object* v_x_633_, lean_object* v_x_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(v_x_632_, v_x_633_, v_x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_636_, lean_object* v_x_637_, size_t v_x_638_, size_t v_x_639_, lean_object* v_x_640_, lean_object* v_x_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_637_, v_x_638_, v_x_639_, v_x_640_, v_x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_643_, lean_object* v_x_644_, lean_object* v_x_645_, lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
size_t v_x_7418__boxed_649_; size_t v_x_7419__boxed_650_; lean_object* v_res_651_; 
v_x_7418__boxed_649_ = lean_unbox_usize(v_x_645_);
lean_dec(v_x_645_);
v_x_7419__boxed_650_ = lean_unbox_usize(v_x_646_);
lean_dec(v_x_646_);
v_res_651_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4(v_00_u03b2_643_, v_x_644_, v_x_7418__boxed_649_, v_x_7419__boxed_650_, v_x_647_, v_x_648_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_652_, lean_object* v_n_653_, lean_object* v_k_654_, lean_object* v_v_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(v_n_653_, v_k_654_, v_v_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_657_, size_t v_depth_658_, lean_object* v_keys_659_, lean_object* v_vals_660_, lean_object* v_heq_661_, lean_object* v_i_662_, lean_object* v_entries_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_658_, v_keys_659_, v_vals_660_, v_i_662_, v_entries_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_665_, lean_object* v_depth_666_, lean_object* v_keys_667_, lean_object* v_vals_668_, lean_object* v_heq_669_, lean_object* v_i_670_, lean_object* v_entries_671_){
_start:
{
size_t v_depth_boxed_672_; lean_object* v_res_673_; 
v_depth_boxed_672_ = lean_unbox_usize(v_depth_666_);
lean_dec(v_depth_666_);
v_res_673_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_665_, v_depth_boxed_672_, v_keys_667_, v_vals_668_, v_heq_669_, v_i_670_, v_entries_671_);
lean_dec_ref(v_vals_668_);
lean_dec_ref(v_keys_667_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_674_, lean_object* v_x_675_, lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_675_, v_x_676_, v_x_677_, v_x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1(){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_691_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_692_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4));
v___x_693_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3));
v___x_694_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___boxed), 10, 0);
v___x_695_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_691_, v___x_692_, v___x_693_, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___boxed(lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1();
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0(lean_object* v___x_699_, lean_object* v_00_u03c3s_700_, uint8_t v___x_701_, lean_object* v_u_702_, lean_object* v_hyps_703_, lean_object* v___x_704_, lean_object* v_target_705_, lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v___x_708_, lean_object* v___x_709_, lean_object* v___x_710_, lean_object* v_fst_711_, lean_object* v_H_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; lean_object* v_a_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_722_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_720_);
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref(v___x_722_);
v___x_724_ = l_Lean_Syntax_getId(v___x_699_);
lean_inc_ref(v_H_712_);
v___x_725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v_a_723_);
lean_ctor_set(v___x_725_, 2, v_H_712_);
lean_inc_ref(v___x_725_);
lean_inc_ref(v_00_u03c3s_700_);
v___x_726_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v___x_699_, v_00_u03c3s_700_, v___x_725_, v___x_701_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_779_; 
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v___x_726_, 0);
lean_dec(v_unused_780_);
v___x_728_ = v___x_726_;
v_isShared_729_ = v_isSharedCheck_779_;
goto v_resetjp_727_;
}
else
{
lean_dec(v___x_726_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_779_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v_fst_732_; lean_object* v_snd_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_778_; 
v___x_730_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_725_);
lean_inc_ref(v___x_730_);
lean_inc_ref(v_hyps_703_);
lean_inc_ref(v_00_u03c3s_700_);
lean_inc(v_u_702_);
v___x_731_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_702_, v_00_u03c3s_700_, v_hyps_703_, v___x_730_);
v_fst_732_ = lean_ctor_get(v___x_731_, 0);
v_snd_733_ = lean_ctor_get(v___x_731_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_778_ == 0)
{
v___x_735_ = v___x_731_;
v_isShared_736_ = v_isSharedCheck_778_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_snd_733_);
lean_inc(v_fst_732_);
lean_dec(v___x_731_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_778_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
lean_inc_ref(v_hyps_703_);
lean_inc_ref(v_00_u03c3s_700_);
lean_inc(v_u_702_);
v___x_737_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_737_, 0, v_u_702_);
lean_ctor_set(v___x_737_, 1, v_00_u03c3s_700_);
lean_ctor_set(v___x_737_, 2, v_hyps_703_);
lean_ctor_set(v___x_737_, 3, v_H_712_);
v___x_738_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_737_);
if (v_isShared_729_ == 0)
{
lean_ctor_set_tag(v___x_728_, 1);
lean_ctor_set(v___x_728_, 0, v___x_738_);
v___x_740_ = v___x_728_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_777_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
uint8_t v___x_741_; lean_object* v___x_742_; 
v___x_741_ = 0;
v___x_742_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v___x_704_, v___x_740_, v___x_741_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
lean_inc_ref(v_target_705_);
lean_inc(v_fst_732_);
lean_inc_ref(v_00_u03c3s_700_);
v___x_744_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_744_, 0, v_u_702_);
lean_ctor_set(v___x_744_, 1, v_00_u03c3s_700_);
lean_ctor_set(v___x_744_, 2, v_fst_732_);
lean_ctor_set(v___x_744_, 3, v_target_705_);
v___x_745_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_744_);
v___x_746_ = lean_box(0);
v___x_747_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_745_, v___x_746_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc_n(v_a_748_, 2);
lean_dec_ref_known(v___x_747_, 1);
v___x_749_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3));
v___x_750_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___closed__0));
v___x_751_ = l_Lean_Name_mkStr6(v___x_706_, v___x_707_, v___x_708_, v___x_709_, v___x_749_, v___x_750_);
v___x_752_ = l_Lean_mkConst(v___x_751_, v___x_710_);
v___x_753_ = l_Lean_mkApp8(v___x_752_, v_00_u03c3s_700_, v_hyps_703_, v___x_730_, v_fst_732_, v_target_705_, v_snd_733_, v_a_743_, v_a_748_);
v___x_754_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_711_, v___x_753_, v___y_718_);
lean_dec_ref(v___x_754_);
v___x_755_ = l_Lean_Expr_mvarId_x21(v_a_748_);
lean_dec(v_a_748_);
v___x_756_ = lean_box(0);
if (v_isShared_736_ == 0)
{
lean_ctor_set_tag(v___x_735_, 1);
lean_ctor_set(v___x_735_, 1, v___x_756_);
lean_ctor_set(v___x_735_, 0, v___x_755_);
v___x_758_ = v___x_735_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___x_756_);
v___x_758_ = v_reuseFailAlloc_760_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_758_, v___y_714_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
return v___x_759_;
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v_a_743_);
lean_del_object(v___x_735_);
lean_dec(v_snd_733_);
lean_dec(v_fst_732_);
lean_dec_ref(v___x_730_);
lean_dec(v_fst_711_);
lean_dec(v___x_710_);
lean_dec_ref(v___x_709_);
lean_dec_ref(v___x_708_);
lean_dec_ref(v___x_707_);
lean_dec_ref(v___x_706_);
lean_dec_ref(v_target_705_);
lean_dec_ref(v_hyps_703_);
lean_dec_ref(v_00_u03c3s_700_);
v_a_761_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_747_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_747_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_del_object(v___x_735_);
lean_dec(v_snd_733_);
lean_dec(v_fst_732_);
lean_dec_ref(v___x_730_);
lean_dec(v_fst_711_);
lean_dec(v___x_710_);
lean_dec_ref(v___x_709_);
lean_dec_ref(v___x_708_);
lean_dec_ref(v___x_707_);
lean_dec_ref(v___x_706_);
lean_dec_ref(v_target_705_);
lean_dec_ref(v_hyps_703_);
lean_dec(v_u_702_);
lean_dec_ref(v_00_u03c3s_700_);
v_a_769_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_742_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_742_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_725_, 3);
lean_dec_ref(v_H_712_);
lean_dec(v_fst_711_);
lean_dec(v___x_710_);
lean_dec_ref(v___x_709_);
lean_dec_ref(v___x_708_);
lean_dec_ref(v___x_707_);
lean_dec_ref(v___x_706_);
lean_dec_ref(v_target_705_);
lean_dec(v___x_704_);
lean_dec_ref(v_hyps_703_);
lean_dec(v_u_702_);
lean_dec_ref(v_00_u03c3s_700_);
return v___x_726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___boxed(lean_object** _args){
lean_object* v___x_781_ = _args[0];
lean_object* v_00_u03c3s_782_ = _args[1];
lean_object* v___x_783_ = _args[2];
lean_object* v_u_784_ = _args[3];
lean_object* v_hyps_785_ = _args[4];
lean_object* v___x_786_ = _args[5];
lean_object* v_target_787_ = _args[6];
lean_object* v___x_788_ = _args[7];
lean_object* v___x_789_ = _args[8];
lean_object* v___x_790_ = _args[9];
lean_object* v___x_791_ = _args[10];
lean_object* v___x_792_ = _args[11];
lean_object* v_fst_793_ = _args[12];
lean_object* v_H_794_ = _args[13];
lean_object* v___y_795_ = _args[14];
lean_object* v___y_796_ = _args[15];
lean_object* v___y_797_ = _args[16];
lean_object* v___y_798_ = _args[17];
lean_object* v___y_799_ = _args[18];
lean_object* v___y_800_ = _args[19];
lean_object* v___y_801_ = _args[20];
lean_object* v___y_802_ = _args[21];
lean_object* v___y_803_ = _args[22];
_start:
{
uint8_t v___x_2162__boxed_804_; lean_object* v_res_805_; 
v___x_2162__boxed_804_ = lean_unbox(v___x_783_);
v_res_805_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0(v___x_781_, v_00_u03c3s_782_, v___x_2162__boxed_804_, v_u_784_, v_hyps_785_, v___x_786_, v_target_787_, v___x_788_, v___x_789_, v___x_790_, v___x_791_, v___x_792_, v_fst_793_, v_H_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1(lean_object* v_ty_x3f_806_, lean_object* v___x_807_, lean_object* v___f_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
if (lean_obj_tag(v_ty_x3f_806_) == 1)
{
lean_object* v_val_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_837_; 
v_val_818_ = lean_ctor_get(v_ty_x3f_806_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v_ty_x3f_806_);
if (v_isSharedCheck_837_ == 0)
{
v___x_820_ = v_ty_x3f_806_;
v_isShared_821_ = v_isSharedCheck_837_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_val_818_);
lean_dec(v_ty_x3f_806_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_837_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_807_);
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_807_);
v___x_823_ = v_reuseFailAlloc_836_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
uint8_t v___x_824_; lean_object* v___x_825_; 
v___x_824_ = 0;
v___x_825_ = l_Lean_Elab_Tactic_elabTerm(v_val_818_, v___x_823_, v___x_824_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_827_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v___x_825_, 1);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
v___x_827_ = lean_apply_10(v___f_808_, v_a_826_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, lean_box(0));
return v___x_827_;
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec_ref(v___f_808_);
v_a_828_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_825_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_825_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
}
else
{
lean_object* v___x_838_; uint8_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec(v_ty_x3f_806_);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_807_);
v___x_839_ = 0;
v___x_840_ = lean_box(0);
v___x_841_ = l_Lean_Meta_mkFreshExprMVar(v___x_838_, v___x_839_, v___x_840_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_843_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_841_, 1);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
v___x_843_ = lean_apply_10(v___f_808_, v_a_842_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, lean_box(0));
return v___x_843_;
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec_ref(v___f_808_);
v_a_844_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_841_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_841_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1___boxed(lean_object* v_ty_x3f_852_, lean_object* v___x_853_, lean_object* v___f_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1(v_ty_x3f_852_, v___x_853_, v___f_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave(lean_object* v_x_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_885_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2));
v___x_886_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1));
lean_inc(v_x_875_);
v___x_887_ = l_Lean_Syntax_isOfKind(v_x_875_, v___x_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; 
lean_dec(v_x_875_);
v___x_888_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_888_;
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v_ty_x3f_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_889_ = lean_unsigned_to_nat(1u);
v___x_890_ = l_Lean_Syntax_getArg(v_x_875_, v___x_889_);
v___x_937_ = lean_unsigned_to_nat(2u);
v___x_938_ = l_Lean_Syntax_getArg(v_x_875_, v___x_937_);
v___x_939_ = l_Lean_Syntax_isNone(v___x_938_);
if (v___x_939_ == 0)
{
uint8_t v___x_940_; 
lean_inc(v___x_938_);
v___x_940_ = l_Lean_Syntax_matchesNull(v___x_938_, v___x_937_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
lean_dec(v___x_938_);
lean_dec(v___x_890_);
lean_dec(v_x_875_);
v___x_941_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_941_;
}
else
{
lean_object* v_ty_x3f_942_; lean_object* v___x_943_; 
v_ty_x3f_942_ = l_Lean_Syntax_getArg(v___x_938_, v___x_889_);
lean_dec(v___x_938_);
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v_ty_x3f_942_);
v_ty_x3f_892_ = v___x_943_;
v___y_893_ = v_a_876_;
v___y_894_ = v_a_877_;
v___y_895_ = v_a_878_;
v___y_896_ = v_a_879_;
v___y_897_ = v_a_880_;
v___y_898_ = v_a_881_;
v___y_899_ = v_a_882_;
v___y_900_ = v_a_883_;
goto v___jp_891_;
}
}
else
{
lean_object* v___x_944_; 
lean_dec(v___x_938_);
v___x_944_ = lean_box(0);
v_ty_x3f_892_ = v___x_944_;
v___y_893_ = v_a_876_;
v___y_894_ = v_a_877_;
v___y_895_ = v_a_878_;
v___y_896_ = v_a_879_;
v___y_897_ = v_a_880_;
v___y_898_ = v_a_881_;
v___y_899_ = v_a_882_;
v___y_900_ = v_a_883_;
goto v___jp_891_;
}
v___jp_891_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_unsigned_to_nat(4u);
v___x_902_ = l_Lean_Syntax_getArg(v_x_875_, v___x_901_);
lean_dec(v_x_875_);
v___x_903_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v_snd_905_; lean_object* v_fst_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_928_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v___x_903_, 1);
v_snd_905_ = lean_ctor_get(v_a_904_, 1);
v_fst_906_ = lean_ctor_get(v_a_904_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v_a_904_);
if (v_isSharedCheck_928_ == 0)
{
v___x_908_ = v_a_904_;
v_isShared_909_ = v_isSharedCheck_928_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_snd_905_);
lean_inc(v_fst_906_);
lean_dec(v_a_904_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_928_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_u_910_; lean_object* v_00_u03c3s_911_; lean_object* v_hyps_912_; lean_object* v_target_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v_u_910_ = lean_ctor_get(v_snd_905_, 0);
lean_inc_n(v_u_910_, 2);
v_00_u03c3s_911_ = lean_ctor_get(v_snd_905_, 1);
lean_inc_ref(v_00_u03c3s_911_);
v_hyps_912_ = lean_ctor_get(v_snd_905_, 2);
lean_inc_ref(v_hyps_912_);
v_target_913_ = lean_ctor_get(v_snd_905_, 3);
lean_inc_ref(v_target_913_);
lean_dec(v_snd_905_);
v___x_914_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0));
v___x_915_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1));
v___x_916_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2));
v___x_917_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2));
v___x_918_ = lean_box(0);
if (v_isShared_909_ == 0)
{
lean_ctor_set_tag(v___x_908_, 1);
lean_ctor_set(v___x_908_, 1, v___x_918_);
lean_ctor_set(v___x_908_, 0, v_u_910_);
v___x_920_ = v___x_908_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_u_910_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v___x_918_);
v___x_920_ = v_reuseFailAlloc_927_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; lean_object* v___f_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___y_925_; lean_object* v___x_926_; 
v___x_921_ = lean_box(v___x_887_);
lean_inc(v_fst_906_);
lean_inc_ref(v___x_920_);
lean_inc_ref(v_00_u03c3s_911_);
v___f_922_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___boxed), 23, 13);
lean_closure_set(v___f_922_, 0, v___x_890_);
lean_closure_set(v___f_922_, 1, v_00_u03c3s_911_);
lean_closure_set(v___f_922_, 2, v___x_921_);
lean_closure_set(v___f_922_, 3, v_u_910_);
lean_closure_set(v___f_922_, 4, v_hyps_912_);
lean_closure_set(v___f_922_, 5, v___x_902_);
lean_closure_set(v___f_922_, 6, v_target_913_);
lean_closure_set(v___f_922_, 7, v___x_914_);
lean_closure_set(v___f_922_, 8, v___x_915_);
lean_closure_set(v___f_922_, 9, v___x_916_);
lean_closure_set(v___f_922_, 10, v___x_885_);
lean_closure_set(v___f_922_, 11, v___x_920_);
lean_closure_set(v___f_922_, 12, v_fst_906_);
v___x_923_ = l_Lean_mkConst(v___x_917_, v___x_920_);
v___x_924_ = l_Lean_Expr_app___override(v___x_923_, v_00_u03c3s_911_);
v___y_925_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1___boxed), 12, 3);
lean_closure_set(v___y_925_, 0, v_ty_x3f_892_);
lean_closure_set(v___y_925_, 1, v___x_924_);
lean_closure_set(v___y_925_, 2, v___f_922_);
v___x_926_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_906_, v___y_925_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
return v___x_926_;
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec(v___x_902_);
lean_dec(v_ty_x3f_892_);
lean_dec(v___x_890_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___boxed(lean_object* v_x_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave(v_x_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1(){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_965_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_966_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1));
v___x_967_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1));
v___x_968_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___boxed), 10, 0);
v___x_969_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_965_, v___x_966_, v___x_967_, v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___boxed(lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1();
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0(lean_object* v___x_973_, lean_object* v_u_974_, lean_object* v___x_975_, lean_object* v___x_976_, lean_object* v_00_u03c3s_977_, uint8_t v___x_978_, lean_object* v_hyps_979_, lean_object* v___x_980_, lean_object* v_target_981_, lean_object* v___x_982_, lean_object* v_fst_983_, lean_object* v_ty_x3f_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
if (lean_obj_tag(v___x_973_) == 1)
{
lean_object* v_val_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1110_; 
v_val_994_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_996_ = v___x_973_;
v_isShared_997_ = v_isSharedCheck_1110_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_val_994_);
lean_dec(v___x_973_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1110_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_focusHyp_998_; lean_object* v_restHyps_999_; lean_object* v_proof_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1109_; 
v_focusHyp_998_ = lean_ctor_get(v_val_994_, 0);
v_restHyps_999_ = lean_ctor_get(v_val_994_, 1);
v_proof_1000_ = lean_ctor_get(v_val_994_, 2);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_val_994_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1002_ = v_val_994_;
v_isShared_1003_ = v_isSharedCheck_1109_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_proof_1000_);
lean_inc(v_restHyps_999_);
lean_inc(v_focusHyp_998_);
lean_dec(v_val_994_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1109_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v_H_x27_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1004_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0));
v___x_1005_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1));
v___x_1006_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2));
v___x_1007_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2));
v___x_1008_ = lean_box(0);
lean_inc(v_u_974_);
v___x_1009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1009_, 0, v_u_974_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
lean_inc_ref(v___x_1009_);
v___x_1075_ = l_Lean_mkConst(v___x_1007_, v___x_1009_);
lean_inc_ref(v_00_u03c3s_977_);
v___x_1076_ = l_Lean_Expr_app___override(v___x_1075_, v_00_u03c3s_977_);
if (lean_obj_tag(v_ty_x3f_984_) == 1)
{
lean_object* v_val_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1095_; 
v_val_1077_ = lean_ctor_get(v_ty_x3f_984_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_ty_x3f_984_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1079_ = v_ty_x3f_984_;
v_isShared_1080_ = v_isSharedCheck_1095_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_val_1077_);
lean_dec(v_ty_x3f_984_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1095_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1076_);
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1076_);
v___x_1082_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
uint8_t v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = 0;
v___x_1084_ = l_Lean_Elab_Tactic_elabTerm(v_val_1077_, v___x_1082_, v___x_1083_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v_H_x27_1011_ = v_a_1085_;
v___y_1012_ = v___y_985_;
v___y_1013_ = v___y_986_;
v___y_1014_ = v___y_987_;
v___y_1015_ = v___y_988_;
v___y_1016_ = v___y_989_;
v___y_1017_ = v___y_990_;
v___y_1018_ = v___y_991_;
v___y_1019_ = v___y_992_;
goto v___jp_1010_;
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec_ref_known(v___x_1009_, 2);
lean_del_object(v___x_1002_);
lean_dec_ref(v_proof_1000_);
lean_dec_ref(v_restHyps_999_);
lean_dec_ref(v_focusHyp_998_);
lean_del_object(v___x_996_);
lean_dec(v_fst_983_);
lean_dec_ref(v___x_982_);
lean_dec_ref(v_target_981_);
lean_dec(v___x_980_);
lean_dec_ref(v_hyps_979_);
lean_dec_ref(v_00_u03c3s_977_);
lean_dec(v___x_976_);
lean_dec(v___x_975_);
lean_dec(v_u_974_);
v_a_1086_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1084_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1084_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
}
else
{
lean_object* v___x_1096_; uint8_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec(v_ty_x3f_984_);
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1076_);
v___x_1097_ = 0;
v___x_1098_ = lean_box(0);
v___x_1099_ = l_Lean_Meta_mkFreshExprMVar(v___x_1096_, v___x_1097_, v___x_1098_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 1);
v_H_x27_1011_ = v_a_1100_;
v___y_1012_ = v___y_985_;
v___y_1013_ = v___y_986_;
v___y_1014_ = v___y_987_;
v___y_1015_ = v___y_988_;
v___y_1016_ = v___y_989_;
v___y_1017_ = v___y_990_;
v___y_1018_ = v___y_991_;
v___y_1019_ = v___y_992_;
goto v___jp_1010_;
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec_ref_known(v___x_1009_, 2);
lean_del_object(v___x_1002_);
lean_dec_ref(v_proof_1000_);
lean_dec_ref(v_restHyps_999_);
lean_dec_ref(v_focusHyp_998_);
lean_del_object(v___x_996_);
lean_dec(v_fst_983_);
lean_dec_ref(v___x_982_);
lean_dec_ref(v_target_981_);
lean_dec(v___x_980_);
lean_dec_ref(v_hyps_979_);
lean_dec_ref(v_00_u03c3s_977_);
lean_dec(v___x_976_);
lean_dec(v___x_975_);
lean_dec(v_u_974_);
v_a_1101_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1099_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1099_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
v___jp_1010_:
{
lean_object* v___x_1020_; lean_object* v_a_1021_; lean_object* v___x_1023_; 
v___x_1020_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_1019_);
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref(v___x_1020_);
lean_inc_ref(v_H_x27_1011_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 2, v_H_x27_1011_);
lean_ctor_set(v___x_1002_, 1, v_a_1021_);
lean_ctor_set(v___x_1002_, 0, v___x_975_);
v___x_1023_ = v___x_1002_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_a_1021_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_H_x27_1011_);
v___x_1023_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; 
lean_inc_ref(v___x_1023_);
lean_inc_ref(v_00_u03c3s_977_);
v___x_1024_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v___x_976_, v_00_u03c3s_977_, v___x_1023_, v___x_978_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
lean_dec_ref_known(v___x_1024_, 1);
v___x_1025_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1023_);
lean_inc_ref(v_hyps_979_);
lean_inc_ref(v_00_u03c3s_977_);
lean_inc(v_u_974_);
v___x_1026_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1026_, 0, v_u_974_);
lean_ctor_set(v___x_1026_, 1, v_00_u03c3s_977_);
lean_ctor_set(v___x_1026_, 2, v_hyps_979_);
lean_ctor_set(v___x_1026_, 3, v_H_x27_1011_);
v___x_1027_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1026_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1027_);
v___x_1029_ = v___x_996_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
uint8_t v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = 0;
v___x_1031_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v___x_980_, v___x_1029_, v___x_1030_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1033_; lean_object* v_fst_1034_; lean_object* v_snd_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1064_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
lean_inc_ref(v___x_1025_);
lean_inc_ref(v_restHyps_999_);
lean_inc_ref(v_00_u03c3s_977_);
lean_inc(v_u_974_);
v___x_1033_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_974_, v_00_u03c3s_977_, v_restHyps_999_, v___x_1025_);
v_fst_1034_ = lean_ctor_get(v___x_1033_, 0);
v_snd_1035_ = lean_ctor_get(v___x_1033_, 1);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1037_ = v___x_1033_;
v_isShared_1038_ = v_isSharedCheck_1064_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_snd_1035_);
lean_inc(v_fst_1034_);
lean_dec(v___x_1033_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1064_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_inc_ref(v_target_981_);
lean_inc(v_fst_1034_);
lean_inc_ref(v_00_u03c3s_977_);
v___x_1039_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1039_, 0, v_u_974_);
lean_ctor_set(v___x_1039_, 1, v_00_u03c3s_977_);
lean_ctor_set(v___x_1039_, 2, v_fst_1034_);
lean_ctor_set(v___x_1039_, 3, v_target_981_);
v___x_1040_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1039_);
v___x_1041_ = lean_box(0);
v___x_1042_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1040_, v___x_1041_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc_n(v_a_1043_, 2);
lean_dec_ref_known(v___x_1042_, 1);
v___x_1044_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3));
v___x_1045_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___closed__0));
v___x_1046_ = l_Lean_Name_mkStr6(v___x_1004_, v___x_1005_, v___x_1006_, v___x_982_, v___x_1044_, v___x_1045_);
v___x_1047_ = l_Lean_mkConst(v___x_1046_, v___x_1009_);
v___x_1048_ = l_Lean_mkApp10(v___x_1047_, v_00_u03c3s_977_, v_restHyps_999_, v_focusHyp_998_, v___x_1025_, v_hyps_979_, v_fst_1034_, v_target_981_, v_proof_1000_, v_snd_1035_, v_a_1032_);
v___x_1049_ = l_Lean_Expr_app___override(v___x_1048_, v_a_1043_);
v___x_1050_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_983_, v___x_1049_, v___y_1017_);
lean_dec_ref(v___x_1050_);
v___x_1051_ = l_Lean_Expr_mvarId_x21(v_a_1043_);
lean_dec(v_a_1043_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 1);
lean_ctor_set(v___x_1037_, 1, v___x_1008_);
lean_ctor_set(v___x_1037_, 0, v___x_1051_);
v___x_1053_ = v___x_1037_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1008_);
v___x_1053_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1053_, v___y_1013_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
return v___x_1054_;
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_del_object(v___x_1037_);
lean_dec(v_snd_1035_);
lean_dec(v_fst_1034_);
lean_dec(v_a_1032_);
lean_dec_ref(v___x_1025_);
lean_dec_ref_known(v___x_1009_, 2);
lean_dec_ref(v_proof_1000_);
lean_dec_ref(v_restHyps_999_);
lean_dec_ref(v_focusHyp_998_);
lean_dec(v_fst_983_);
lean_dec_ref(v___x_982_);
lean_dec_ref(v_target_981_);
lean_dec_ref(v_hyps_979_);
lean_dec_ref(v_00_u03c3s_977_);
v_a_1056_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1042_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1042_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref(v___x_1025_);
lean_dec_ref_known(v___x_1009_, 2);
lean_dec_ref(v_proof_1000_);
lean_dec_ref(v_restHyps_999_);
lean_dec_ref(v_focusHyp_998_);
lean_dec(v_fst_983_);
lean_dec_ref(v___x_982_);
lean_dec_ref(v_target_981_);
lean_dec_ref(v_hyps_979_);
lean_dec_ref(v_00_u03c3s_977_);
lean_dec(v_u_974_);
v_a_1065_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1031_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1031_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1023_);
lean_dec_ref(v_H_x27_1011_);
lean_dec_ref_known(v___x_1009_, 2);
lean_dec_ref(v_proof_1000_);
lean_dec_ref(v_restHyps_999_);
lean_dec_ref(v_focusHyp_998_);
lean_del_object(v___x_996_);
lean_dec(v_fst_983_);
lean_dec_ref(v___x_982_);
lean_dec_ref(v_target_981_);
lean_dec(v___x_980_);
lean_dec_ref(v_hyps_979_);
lean_dec_ref(v_00_u03c3s_977_);
lean_dec(v_u_974_);
return v___x_1024_;
}
}
}
}
}
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v_ty_x3f_984_);
lean_dec(v_fst_983_);
lean_dec_ref(v___x_982_);
lean_dec_ref(v_target_981_);
lean_dec(v___x_980_);
lean_dec_ref(v_hyps_979_);
lean_dec_ref(v_00_u03c3s_977_);
lean_dec(v___x_975_);
lean_dec(v_u_974_);
lean_dec(v___x_973_);
v___x_1111_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6);
v___x_1112_ = l_Lean_MessageData_ofSyntax(v___x_976_);
v___x_1113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1111_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8);
v___x_1115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1113_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v___x_1115_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___boxed(lean_object** _args){
lean_object* v___x_1117_ = _args[0];
lean_object* v_u_1118_ = _args[1];
lean_object* v___x_1119_ = _args[2];
lean_object* v___x_1120_ = _args[3];
lean_object* v_00_u03c3s_1121_ = _args[4];
lean_object* v___x_1122_ = _args[5];
lean_object* v_hyps_1123_ = _args[6];
lean_object* v___x_1124_ = _args[7];
lean_object* v_target_1125_ = _args[8];
lean_object* v___x_1126_ = _args[9];
lean_object* v_fst_1127_ = _args[10];
lean_object* v_ty_x3f_1128_ = _args[11];
lean_object* v___y_1129_ = _args[12];
lean_object* v___y_1130_ = _args[13];
lean_object* v___y_1131_ = _args[14];
lean_object* v___y_1132_ = _args[15];
lean_object* v___y_1133_ = _args[16];
lean_object* v___y_1134_ = _args[17];
lean_object* v___y_1135_ = _args[18];
lean_object* v___y_1136_ = _args[19];
lean_object* v___y_1137_ = _args[20];
_start:
{
uint8_t v___x_2642__boxed_1138_; lean_object* v_res_1139_; 
v___x_2642__boxed_1138_ = lean_unbox(v___x_1122_);
v_res_1139_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0(v___x_1117_, v_u_1118_, v___x_1119_, v___x_1120_, v_00_u03c3s_1121_, v___x_2642__boxed_1138_, v_hyps_1123_, v___x_1124_, v_target_1125_, v___x_1126_, v_fst_1127_, v_ty_x3f_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace(lean_object* v_x_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1156_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2));
v___x_1157_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1));
lean_inc(v_x_1146_);
v___x_1158_ = l_Lean_Syntax_isOfKind(v_x_1146_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; 
lean_dec(v_x_1146_);
v___x_1159_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v_ty_x3f_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = l_Lean_Syntax_getArg(v_x_1146_, v___x_1160_);
v___x_1195_ = lean_unsigned_to_nat(2u);
v___x_1196_ = l_Lean_Syntax_getArg(v_x_1146_, v___x_1195_);
v___x_1197_ = l_Lean_Syntax_isNone(v___x_1196_);
if (v___x_1197_ == 0)
{
uint8_t v___x_1198_; 
lean_inc(v___x_1196_);
v___x_1198_ = l_Lean_Syntax_matchesNull(v___x_1196_, v___x_1195_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; 
lean_dec(v___x_1196_);
lean_dec(v___x_1161_);
lean_dec(v_x_1146_);
v___x_1199_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_1199_;
}
else
{
lean_object* v_ty_x3f_1200_; lean_object* v___x_1201_; 
v_ty_x3f_1200_ = l_Lean_Syntax_getArg(v___x_1196_, v___x_1160_);
lean_dec(v___x_1196_);
v___x_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1201_, 0, v_ty_x3f_1200_);
v_ty_x3f_1163_ = v___x_1201_;
v___y_1164_ = v_a_1147_;
v___y_1165_ = v_a_1148_;
v___y_1166_ = v_a_1149_;
v___y_1167_ = v_a_1150_;
v___y_1168_ = v_a_1151_;
v___y_1169_ = v_a_1152_;
v___y_1170_ = v_a_1153_;
v___y_1171_ = v_a_1154_;
goto v___jp_1162_;
}
}
else
{
lean_object* v___x_1202_; 
lean_dec(v___x_1196_);
v___x_1202_ = lean_box(0);
v_ty_x3f_1163_ = v___x_1202_;
v___y_1164_ = v_a_1147_;
v___y_1165_ = v_a_1148_;
v___y_1166_ = v_a_1149_;
v___y_1167_ = v_a_1150_;
v___y_1168_ = v_a_1151_;
v___y_1169_ = v_a_1152_;
v___y_1170_ = v_a_1153_;
v___y_1171_ = v_a_1154_;
goto v___jp_1162_;
}
v___jp_1162_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = lean_unsigned_to_nat(4u);
v___x_1173_ = l_Lean_Syntax_getArg(v_x_1146_, v___x_1172_);
lean_dec(v_x_1146_);
v___x_1174_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v_snd_1176_; lean_object* v_fst_1177_; lean_object* v_u_1178_; lean_object* v_00_u03c3s_1179_; lean_object* v_hyps_1180_; lean_object* v_target_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___y_1185_; lean_object* v___x_1186_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v_snd_1176_ = lean_ctor_get(v_a_1175_, 1);
lean_inc(v_snd_1176_);
v_fst_1177_ = lean_ctor_get(v_a_1175_, 0);
lean_inc_n(v_fst_1177_, 2);
lean_dec(v_a_1175_);
v_u_1178_ = lean_ctor_get(v_snd_1176_, 0);
lean_inc(v_u_1178_);
v_00_u03c3s_1179_ = lean_ctor_get(v_snd_1176_, 1);
lean_inc_ref(v_00_u03c3s_1179_);
v_hyps_1180_ = lean_ctor_get(v_snd_1176_, 2);
lean_inc_ref(v_hyps_1180_);
v_target_1181_ = lean_ctor_get(v_snd_1176_, 3);
lean_inc_ref(v_target_1181_);
v___x_1182_ = l_Lean_Syntax_getId(v___x_1161_);
v___x_1183_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_1176_, v___x_1182_);
v___x_1184_ = lean_box(v___x_1158_);
v___y_1185_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___boxed), 21, 12);
lean_closure_set(v___y_1185_, 0, v___x_1183_);
lean_closure_set(v___y_1185_, 1, v_u_1178_);
lean_closure_set(v___y_1185_, 2, v___x_1182_);
lean_closure_set(v___y_1185_, 3, v___x_1161_);
lean_closure_set(v___y_1185_, 4, v_00_u03c3s_1179_);
lean_closure_set(v___y_1185_, 5, v___x_1184_);
lean_closure_set(v___y_1185_, 6, v_hyps_1180_);
lean_closure_set(v___y_1185_, 7, v___x_1173_);
lean_closure_set(v___y_1185_, 8, v_target_1181_);
lean_closure_set(v___y_1185_, 9, v___x_1156_);
lean_closure_set(v___y_1185_, 10, v_fst_1177_);
lean_closure_set(v___y_1185_, 11, v_ty_x3f_1163_);
v___x_1186_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_1177_, v___y_1185_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
return v___x_1186_;
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec(v___x_1173_);
lean_dec(v_ty_x3f_1163_);
lean_dec(v___x_1161_);
v_a_1187_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1174_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1174_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___boxed(lean_object* v_x_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace(v_x_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1(){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1223_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1224_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1));
v___x_1225_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1));
v___x_1226_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___boxed), 10, 0);
v___x_1227_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1223_, v___x_1224_, v___x_1225_, v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___boxed(lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1();
return v_res_1229_;
}
}
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Have(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Have(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Have(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Have(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Have(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Have(builtin);
}
#ifdef __cplusplus
}
#endif
