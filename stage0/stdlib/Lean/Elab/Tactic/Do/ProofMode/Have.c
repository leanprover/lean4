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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_20_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v___y_13_ = stack[3].m_obj;
lean_object* v___y_14_ = stack[4].m_obj;
lean_object* v___y_15_ = stack[5].m_obj;
lean_object* v___y_16_ = stack[6].m_obj;
lean_object* v___y_17_ = stack[7].m_obj;
lean_object* v___y_18_ = stack[8].m_obj;
lean_object* v_res_21_;
v_res_21_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0(lean_box(0), v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___boxed(lean_object* v_00_u03b1_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0(v_00_u03b1_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
return v_res_32_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(lean_object* v___y_33_){
_start:
{
lean_object* v___x_35_; lean_object* v_ngen_36_; lean_object* v_namePrefix_37_; lean_object* v_idx_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_68_; 
v___x_35_ = lean_st_ref_get(v___y_33_);
v_ngen_36_ = lean_ctor_get(v___x_35_, 2);
lean_inc_ref(v_ngen_36_);
lean_dec(v___x_35_);
v_namePrefix_37_ = lean_ctor_get(v_ngen_36_, 0);
v_idx_38_ = lean_ctor_get(v_ngen_36_, 1);
v_isSharedCheck_68_ = !lean_is_exclusive(v_ngen_36_);
if (v_isSharedCheck_68_ == 0)
{
v___x_40_ = v_ngen_36_;
v_isShared_41_ = v_isSharedCheck_68_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_idx_38_);
lean_inc(v_namePrefix_37_);
lean_dec(v_ngen_36_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_68_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v_r_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
lean_inc(v_idx_38_);
lean_inc(v_namePrefix_37_);
v_r_42_ = l_Lean_Name_num___override(v_namePrefix_37_, v_idx_38_);
v___x_43_ = lean_unsigned_to_nat(1u);
v___x_44_ = lean_nat_add(v_idx_38_, v___x_43_);
lean_dec(v_idx_38_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 1, v___x_44_);
v___x_46_ = v___x_40_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_namePrefix_37_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v___x_44_);
v___x_46_ = v_reuseFailAlloc_67_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; lean_object* v_env_48_; lean_object* v_nextMacroScope_49_; lean_object* v_auxDeclNGen_50_; lean_object* v_traceState_51_; lean_object* v_cache_52_; lean_object* v_recordedDeps_53_; lean_object* v_messages_54_; lean_object* v_infoState_55_; lean_object* v_snapshotTasks_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_65_; 
v___x_47_ = lean_st_ref_take(v___y_33_);
v_env_48_ = lean_ctor_get(v___x_47_, 0);
v_nextMacroScope_49_ = lean_ctor_get(v___x_47_, 1);
v_auxDeclNGen_50_ = lean_ctor_get(v___x_47_, 3);
v_traceState_51_ = lean_ctor_get(v___x_47_, 4);
v_cache_52_ = lean_ctor_get(v___x_47_, 5);
v_recordedDeps_53_ = lean_ctor_get(v___x_47_, 6);
v_messages_54_ = lean_ctor_get(v___x_47_, 7);
v_infoState_55_ = lean_ctor_get(v___x_47_, 8);
v_snapshotTasks_56_ = lean_ctor_get(v___x_47_, 9);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_65_ == 0)
{
lean_object* v_unused_66_; 
v_unused_66_ = lean_ctor_get(v___x_47_, 2);
lean_dec(v_unused_66_);
v___x_58_ = v___x_47_;
v_isShared_59_ = v_isSharedCheck_65_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_snapshotTasks_56_);
lean_inc(v_infoState_55_);
lean_inc(v_messages_54_);
lean_inc(v_recordedDeps_53_);
lean_inc(v_cache_52_);
lean_inc(v_traceState_51_);
lean_inc(v_auxDeclNGen_50_);
lean_inc(v_nextMacroScope_49_);
lean_inc(v_env_48_);
lean_dec(v___x_47_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_65_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 2, v___x_46_);
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_env_48_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_nextMacroScope_49_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_64_, 3, v_auxDeclNGen_50_);
lean_ctor_set(v_reuseFailAlloc_64_, 4, v_traceState_51_);
lean_ctor_set(v_reuseFailAlloc_64_, 5, v_cache_52_);
lean_ctor_set(v_reuseFailAlloc_64_, 6, v_recordedDeps_53_);
lean_ctor_set(v_reuseFailAlloc_64_, 7, v_messages_54_);
lean_ctor_set(v_reuseFailAlloc_64_, 8, v_infoState_55_);
lean_ctor_set(v_reuseFailAlloc_64_, 9, v_snapshotTasks_56_);
v___x_61_ = v_reuseFailAlloc_64_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_st_ref_put(v___y_33_, v___x_61_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v_r_42_);
return v___x_63_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_33_ = stack[0].m_obj;
lean_object* v_res_69_;
v_res_69_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_33_);
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg___boxed(lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_70_);
lean_dec(v___y_70_);
return v_res_72_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1(lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_80_);
return v___x_82_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_73_ = stack[0].m_obj;
lean_object* v___y_74_ = stack[1].m_obj;
lean_object* v___y_75_ = stack[2].m_obj;
lean_object* v___y_76_ = stack[3].m_obj;
lean_object* v___y_77_ = stack[4].m_obj;
lean_object* v___y_78_ = stack[5].m_obj;
lean_object* v___y_79_ = stack[6].m_obj;
lean_object* v___y_80_ = stack[7].m_obj;
lean_object* v_res_83_;
v_res_83_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1(v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___boxed(lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1(v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
return v_res_93_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0(lean_object* v_x_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; 
lean_inc(v___y_98_);
lean_inc_ref(v___y_97_);
lean_inc(v___y_96_);
lean_inc_ref(v___y_95_);
v___x_104_ = lean_apply_9(v_x_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, lean_box(0));
return v___x_104_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_94_ = stack[0].m_obj;
lean_object* v___y_95_ = stack[1].m_obj;
lean_object* v___y_96_ = stack[2].m_obj;
lean_object* v___y_97_ = stack[3].m_obj;
lean_object* v___y_98_ = stack[4].m_obj;
lean_object* v___y_99_ = stack[5].m_obj;
lean_object* v___y_100_ = stack[6].m_obj;
lean_object* v___y_101_ = stack[7].m_obj;
lean_object* v___y_102_ = stack[8].m_obj;
lean_object* v_res_105_;
v_res_105_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0(v_x_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
stack->m_obj
 = v_res_105_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0___boxed(lean_object* v_x_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0(v_x_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_116_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(lean_object* v_mvarId_117_, lean_object* v_x_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v___f_128_; lean_object* v___x_129_; 
lean_inc(v___y_122_);
lean_inc_ref(v___y_121_);
lean_inc(v___y_120_);
lean_inc_ref(v___y_119_);
v___f_128_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_128_, 0, v_x_118_);
lean_closure_set(v___f_128_, 1, v___y_119_);
lean_closure_set(v___f_128_, 2, v___y_120_);
lean_closure_set(v___f_128_, 3, v___y_121_);
lean_closure_set(v___f_128_, 4, v___y_122_);
v___x_129_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_117_, v___f_128_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
if (lean_obj_tag(v___x_129_) == 0)
{
return v___x_129_;
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
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
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_117_ = stack[0].m_obj;
lean_object* v_x_118_ = stack[1].m_obj;
lean_object* v___y_119_ = stack[2].m_obj;
lean_object* v___y_120_ = stack[3].m_obj;
lean_object* v___y_121_ = stack[4].m_obj;
lean_object* v___y_122_ = stack[5].m_obj;
lean_object* v___y_123_ = stack[6].m_obj;
lean_object* v___y_124_ = stack[7].m_obj;
lean_object* v___y_125_ = stack[8].m_obj;
lean_object* v___y_126_ = stack[9].m_obj;
lean_object* v_res_138_;
v_res_138_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_mvarId_117_, v_x_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___boxed(lean_object* v_mvarId_139_, lean_object* v_x_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_mvarId_139_, v_x_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
return v_res_150_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4(lean_object* v_00_u03b1_151_, lean_object* v_mvarId_152_, lean_object* v_x_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_mvarId_152_, v_x_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
return v___x_163_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_152_ = stack[1].m_obj;
lean_object* v_x_153_ = stack[2].m_obj;
lean_object* v___y_154_ = stack[3].m_obj;
lean_object* v___y_155_ = stack[4].m_obj;
lean_object* v___y_156_ = stack[5].m_obj;
lean_object* v___y_157_ = stack[6].m_obj;
lean_object* v___y_158_ = stack[7].m_obj;
lean_object* v___y_159_ = stack[8].m_obj;
lean_object* v___y_160_ = stack[9].m_obj;
lean_object* v___y_161_ = stack[10].m_obj;
lean_object* v_res_164_;
v_res_164_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4(lean_box(0), v_mvarId_152_, v_x_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
stack->m_obj
 = v_res_164_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___boxed(lean_object* v_00_u03b1_165_, lean_object* v_mvarId_166_, lean_object* v_x_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4(v_00_u03b1_165_, v_mvarId_166_, v_x_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_x_178_, lean_object* v_x_179_, lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
lean_object* v_ks_182_; lean_object* v_vs_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_207_; 
v_ks_182_ = lean_ctor_get(v_x_178_, 0);
v_vs_183_ = lean_ctor_get(v_x_178_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v_x_178_);
if (v_isSharedCheck_207_ == 0)
{
v___x_185_ = v_x_178_;
v_isShared_186_ = v_isSharedCheck_207_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_vs_183_);
lean_inc(v_ks_182_);
lean_dec(v_x_178_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_207_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = lean_array_get_size(v_ks_182_);
v___x_188_ = lean_nat_dec_lt(v_x_179_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
lean_dec(v_x_179_);
v___x_189_ = lean_array_push(v_ks_182_, v_x_180_);
v___x_190_ = lean_array_push(v_vs_183_, v_x_181_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v___x_190_);
lean_ctor_set(v___x_185_, 0, v___x_189_);
v___x_192_ = v___x_185_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
else
{
lean_object* v_k_x27_194_; uint8_t v___x_195_; 
v_k_x27_194_ = lean_array_fget_borrowed(v_ks_182_, v_x_179_);
v___x_195_ = l_Lean_instBEqMVarId_beq(v_x_180_, v_k_x27_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_197_; 
if (v_isShared_186_ == 0)
{
v___x_197_ = v___x_185_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_ks_182_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_vs_183_);
v___x_197_ = v_reuseFailAlloc_201_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_unsigned_to_nat(1u);
v___x_199_ = lean_nat_add(v_x_179_, v___x_198_);
lean_dec(v_x_179_);
v_x_178_ = v___x_197_;
v_x_179_ = v___x_199_;
goto _start;
}
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_202_ = lean_array_fset(v_ks_182_, v_x_179_, v_x_180_);
v___x_203_ = lean_array_fset(v_vs_183_, v_x_179_, v_x_181_);
lean_dec(v_x_179_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v___x_203_);
lean_ctor_set(v___x_185_, 0, v___x_202_);
v___x_205_ = v___x_185_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(lean_object* v_n_208_, lean_object* v_k_209_, lean_object* v_v_210_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_n_208_, v___x_211_, v_k_209_, v_v_210_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_213_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(lean_object* v_x_214_, size_t v_x_215_, size_t v_x_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_214_) == 0)
{
lean_object* v_es_219_; size_t v___x_220_; size_t v___x_221_; lean_object* v_j_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_es_219_ = lean_ctor_get(v_x_214_, 0);
v___x_220_ = ((size_t)31ULL);
v___x_221_ = lean_usize_land(v_x_215_, v___x_220_);
v_j_222_ = lean_usize_to_nat(v___x_221_);
v___x_223_ = lean_array_get_size(v_es_219_);
v___x_224_ = lean_nat_dec_lt(v_j_222_, v___x_223_);
if (v___x_224_ == 0)
{
lean_dec(v_j_222_);
lean_dec(v_x_218_);
lean_dec(v_x_217_);
return v_x_214_;
}
else
{
lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_263_; 
lean_inc_ref(v_es_219_);
v_isSharedCheck_263_ = !lean_is_exclusive(v_x_214_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; 
v_unused_264_ = lean_ctor_get(v_x_214_, 0);
lean_dec(v_unused_264_);
v___x_226_ = v_x_214_;
v_isShared_227_ = v_isSharedCheck_263_;
goto v_resetjp_225_;
}
else
{
lean_dec(v_x_214_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_263_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v_v_228_; lean_object* v___x_229_; lean_object* v_xs_x27_230_; lean_object* v___y_232_; 
v_v_228_ = lean_array_fget(v_es_219_, v_j_222_);
v___x_229_ = lean_box(0);
v_xs_x27_230_ = lean_array_fset(v_es_219_, v_j_222_, v___x_229_);
switch(lean_obj_tag(v_v_228_))
{
case 0:
{
lean_object* v_key_237_; lean_object* v_val_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_248_; 
v_key_237_ = lean_ctor_get(v_v_228_, 0);
v_val_238_ = lean_ctor_get(v_v_228_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_v_228_);
if (v_isSharedCheck_248_ == 0)
{
v___x_240_ = v_v_228_;
v_isShared_241_ = v_isSharedCheck_248_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_val_238_);
lean_inc(v_key_237_);
lean_dec(v_v_228_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_248_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
uint8_t v___x_242_; 
v___x_242_ = l_Lean_instBEqMVarId_beq(v_x_217_, v_key_237_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_del_object(v___x_240_);
v___x_243_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_237_, v_val_238_, v_x_217_, v_x_218_);
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
v___y_232_ = v___x_244_;
goto v___jp_231_;
}
else
{
lean_object* v___x_246_; 
lean_dec(v_val_238_);
lean_dec(v_key_237_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v_x_218_);
lean_ctor_set(v___x_240_, 0, v_x_217_);
v___x_246_ = v___x_240_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_x_217_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_x_218_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
v___y_232_ = v___x_246_;
goto v___jp_231_;
}
}
}
}
case 1:
{
lean_object* v_node_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_261_; 
v_node_249_ = lean_ctor_get(v_v_228_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v_v_228_);
if (v_isSharedCheck_261_ == 0)
{
v___x_251_ = v_v_228_;
v_isShared_252_ = v_isSharedCheck_261_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_node_249_);
lean_dec(v_v_228_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_261_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_253_ = ((size_t)5ULL);
v___x_254_ = lean_usize_shift_right(v_x_215_, v___x_253_);
v___x_255_ = ((size_t)1ULL);
v___x_256_ = lean_usize_add(v_x_216_, v___x_255_);
v___x_257_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_node_249_, v___x_254_, v___x_256_, v_x_217_, v_x_218_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___x_257_);
v___x_259_ = v___x_251_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
v___y_232_ = v___x_259_;
goto v___jp_231_;
}
}
}
default: 
{
lean_object* v___x_262_; 
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v_x_217_);
lean_ctor_set(v___x_262_, 1, v_x_218_);
v___y_232_ = v___x_262_;
goto v___jp_231_;
}
}
v___jp_231_:
{
lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_233_ = lean_array_fset(v_xs_x27_230_, v_j_222_, v___y_232_);
lean_dec(v_j_222_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_233_);
v___x_235_ = v___x_226_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
else
{
lean_object* v_ks_265_; lean_object* v_vs_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_284_; 
v_ks_265_ = lean_ctor_get(v_x_214_, 0);
v_vs_266_ = lean_ctor_get(v_x_214_, 1);
v_isSharedCheck_284_ = !lean_is_exclusive(v_x_214_);
if (v_isSharedCheck_284_ == 0)
{
v___x_268_ = v_x_214_;
v_isShared_269_ = v_isSharedCheck_284_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_vs_266_);
lean_inc(v_ks_265_);
lean_dec(v_x_214_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_284_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_ks_265_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_vs_266_);
v___x_271_ = v_reuseFailAlloc_283_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v_newNode_272_; size_t v___x_273_; uint8_t v___x_274_; 
v_newNode_272_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(v___x_271_, v_x_217_, v_x_218_);
v___x_273_ = ((size_t)7ULL);
v___x_274_ = lean_usize_dec_le(v___x_273_, v_x_216_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_275_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_272_);
v___x_276_ = lean_unsigned_to_nat(4u);
v___x_277_ = lean_nat_dec_lt(v___x_275_, v___x_276_);
lean_dec(v___x_275_);
if (v___x_277_ == 0)
{
lean_object* v_ks_278_; lean_object* v_vs_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_ks_278_ = lean_ctor_get(v_newNode_272_, 0);
lean_inc_ref(v_ks_278_);
v_vs_279_ = lean_ctor_get(v_newNode_272_, 1);
lean_inc_ref(v_vs_279_);
lean_dec_ref(v_newNode_272_);
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_282_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_x_216_, v_ks_278_, v_vs_279_, v___x_280_, v___x_281_);
lean_dec_ref(v_vs_279_);
lean_dec_ref(v_ks_278_);
return v___x_282_;
}
else
{
return v_newNode_272_;
}
}
else
{
return v_newNode_272_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_214_ = stack[0].m_obj;
size_t v_x_215_ = stack[1].m_num;
size_t v_x_216_ = stack[2].m_num;
lean_object* v_x_217_ = stack[3].m_obj;
lean_object* v_x_218_ = stack[4].m_obj;
lean_object* v_res_285_;
v_res_285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_214_, v_x_215_, v_x_216_, v_x_217_, v_x_218_);
stack->m_obj
 = v_res_285_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(size_t v_depth_286_, lean_object* v_keys_287_, lean_object* v_vals_288_, lean_object* v_i_289_, lean_object* v_entries_290_){
_start:
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_array_get_size(v_keys_287_);
v___x_292_ = lean_nat_dec_lt(v_i_289_, v___x_291_);
if (v___x_292_ == 0)
{
lean_dec(v_i_289_);
return v_entries_290_;
}
else
{
lean_object* v_k_293_; lean_object* v_v_294_; uint64_t v___x_295_; size_t v_h_296_; size_t v___x_297_; lean_object* v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; size_t v_h_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_k_293_ = lean_array_fget_borrowed(v_keys_287_, v_i_289_);
v_v_294_ = lean_array_fget_borrowed(v_vals_288_, v_i_289_);
v___x_295_ = l_Lean_instHashableMVarId_hash(v_k_293_);
v_h_296_ = lean_uint64_to_usize(v___x_295_);
v___x_297_ = ((size_t)5ULL);
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_sub(v_depth_286_, v___x_299_);
v___x_301_ = lean_usize_mul(v___x_297_, v___x_300_);
v_h_302_ = lean_usize_shift_right(v_h_296_, v___x_301_);
v___x_303_ = lean_nat_add(v_i_289_, v___x_298_);
lean_dec(v_i_289_);
lean_inc(v_v_294_);
lean_inc(v_k_293_);
v___x_304_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_entries_290_, v_h_302_, v_depth_286_, v_k_293_, v_v_294_);
v_i_289_ = v___x_303_;
v_entries_290_ = v___x_304_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_286_ = stack[0].m_num;
lean_object* v_keys_287_ = stack[1].m_obj;
lean_object* v_vals_288_ = stack[2].m_obj;
lean_object* v_i_289_ = stack[3].m_obj;
lean_object* v_entries_290_ = stack[4].m_obj;
lean_object* v_res_306_;
v_res_306_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_286_, v_keys_287_, v_vals_288_, v_i_289_, v_entries_290_);
stack->m_obj
 = v_res_306_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_307_, lean_object* v_keys_308_, lean_object* v_vals_309_, lean_object* v_i_310_, lean_object* v_entries_311_){
_start:
{
size_t v_depth_boxed_312_; lean_object* v_res_313_; 
v_depth_boxed_312_ = lean_unbox_usize(v_depth_307_);
lean_dec(v_depth_307_);
v_res_313_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_boxed_312_, v_keys_308_, v_vals_309_, v_i_310_, v_entries_311_);
lean_dec_ref(v_vals_309_);
lean_dec_ref(v_keys_308_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_314_, lean_object* v_x_315_, lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
size_t v_x_6950__boxed_319_; size_t v_x_6951__boxed_320_; lean_object* v_res_321_; 
v_x_6950__boxed_319_ = lean_unbox_usize(v_x_315_);
lean_dec(v_x_315_);
v_x_6951__boxed_320_ = lean_unbox_usize(v_x_316_);
lean_dec(v_x_316_);
v_res_321_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_314_, v_x_6950__boxed_319_, v_x_6951__boxed_320_, v_x_317_, v_x_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
uint64_t v___x_325_; size_t v___x_326_; size_t v___x_327_; lean_object* v___x_328_; 
v___x_325_ = l_Lean_instHashableMVarId_hash(v_x_323_);
v___x_326_ = lean_uint64_to_usize(v___x_325_);
v___x_327_ = ((size_t)1ULL);
v___x_328_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_322_, v___x_326_, v___x_327_, v_x_323_, v_x_324_);
return v___x_328_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(lean_object* v_mvarId_329_, lean_object* v_val_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___x_333_; lean_object* v_mctx_334_; lean_object* v_cache_335_; lean_object* v_zetaDeltaFVarIds_336_; lean_object* v_postponed_337_; lean_object* v_diag_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_368_; 
v___x_333_ = lean_st_ref_take(v___y_331_);
v_mctx_334_ = lean_ctor_get(v___x_333_, 0);
v_cache_335_ = lean_ctor_get(v___x_333_, 1);
v_zetaDeltaFVarIds_336_ = lean_ctor_get(v___x_333_, 2);
v_postponed_337_ = lean_ctor_get(v___x_333_, 3);
v_diag_338_ = lean_ctor_get(v___x_333_, 4);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_368_ == 0)
{
v___x_340_ = v___x_333_;
v_isShared_341_ = v_isSharedCheck_368_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_diag_338_);
lean_inc(v_postponed_337_);
lean_inc(v_zetaDeltaFVarIds_336_);
lean_inc(v_cache_335_);
lean_inc(v_mctx_334_);
lean_dec(v___x_333_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_368_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_depth_342_; lean_object* v_levelAssignDepth_343_; lean_object* v_lmvarCounter_344_; lean_object* v_mvarCounter_345_; lean_object* v_lDecls_346_; lean_object* v_decls_347_; lean_object* v_userNames_348_; lean_object* v_lAssignment_349_; lean_object* v_eAssignment_350_; lean_object* v_dAssignment_351_; lean_object* v_instanceTypedMVars_352_; lean_object* v_synthNormMemo_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_367_; 
v_depth_342_ = lean_ctor_get(v_mctx_334_, 0);
v_levelAssignDepth_343_ = lean_ctor_get(v_mctx_334_, 1);
v_lmvarCounter_344_ = lean_ctor_get(v_mctx_334_, 2);
v_mvarCounter_345_ = lean_ctor_get(v_mctx_334_, 3);
v_lDecls_346_ = lean_ctor_get(v_mctx_334_, 4);
v_decls_347_ = lean_ctor_get(v_mctx_334_, 5);
v_userNames_348_ = lean_ctor_get(v_mctx_334_, 6);
v_lAssignment_349_ = lean_ctor_get(v_mctx_334_, 7);
v_eAssignment_350_ = lean_ctor_get(v_mctx_334_, 8);
v_dAssignment_351_ = lean_ctor_get(v_mctx_334_, 9);
v_instanceTypedMVars_352_ = lean_ctor_get(v_mctx_334_, 10);
v_synthNormMemo_353_ = lean_ctor_get(v_mctx_334_, 11);
v_isSharedCheck_367_ = !lean_is_exclusive(v_mctx_334_);
if (v_isSharedCheck_367_ == 0)
{
v___x_355_ = v_mctx_334_;
v_isShared_356_ = v_isSharedCheck_367_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_synthNormMemo_353_);
lean_inc(v_instanceTypedMVars_352_);
lean_inc(v_dAssignment_351_);
lean_inc(v_eAssignment_350_);
lean_inc(v_lAssignment_349_);
lean_inc(v_userNames_348_);
lean_inc(v_decls_347_);
lean_inc(v_lDecls_346_);
lean_inc(v_mvarCounter_345_);
lean_inc(v_lmvarCounter_344_);
lean_inc(v_levelAssignDepth_343_);
lean_inc(v_depth_342_);
lean_dec(v_mctx_334_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_367_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_357_ = lean_box(0);
v___x_358_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(v_eAssignment_350_, v_mvarId_329_, v_val_330_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 8, v___x_358_);
v___x_360_ = v___x_355_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_depth_342_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_levelAssignDepth_343_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_lmvarCounter_344_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v_mvarCounter_345_);
lean_ctor_set(v_reuseFailAlloc_366_, 4, v_lDecls_346_);
lean_ctor_set(v_reuseFailAlloc_366_, 5, v_decls_347_);
lean_ctor_set(v_reuseFailAlloc_366_, 6, v_userNames_348_);
lean_ctor_set(v_reuseFailAlloc_366_, 7, v_lAssignment_349_);
lean_ctor_set(v_reuseFailAlloc_366_, 8, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_366_, 9, v_dAssignment_351_);
lean_ctor_set(v_reuseFailAlloc_366_, 10, v_instanceTypedMVars_352_);
lean_ctor_set(v_reuseFailAlloc_366_, 11, v_synthNormMemo_353_);
v___x_360_ = v_reuseFailAlloc_366_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_362_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_360_);
v___x_362_ = v___x_340_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_cache_335_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_zetaDeltaFVarIds_336_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v_postponed_337_);
lean_ctor_set(v_reuseFailAlloc_365_, 4, v_diag_338_);
v___x_362_ = v_reuseFailAlloc_365_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_st_ref_put(v___y_331_, v___x_362_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_357_);
return v___x_364_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_329_ = stack[0].m_obj;
lean_object* v_val_330_ = stack[1].m_obj;
lean_object* v___y_331_ = stack[2].m_obj;
lean_object* v_res_369_;
v_res_369_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_mvarId_329_, v_val_330_, v___y_331_);
stack->m_obj
 = v_res_369_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg___boxed(lean_object* v_mvarId_370_, lean_object* v_val_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_mvarId_370_, v_val_371_, v___y_372_);
lean_dec(v___y_372_);
return v_res_374_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(lean_object* v_msgData_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; lean_object* v_env_382_; uint8_t v___x_383_; lean_object* v_env_384_; lean_object* v___x_385_; lean_object* v_toCold_386_; lean_object* v_mctx_387_; lean_object* v_lctx_388_; lean_object* v_options_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_381_ = lean_st_ref_get(v___y_379_);
v_env_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc_ref(v_env_382_);
lean_dec(v___x_381_);
v___x_383_ = 0;
v_env_384_ = l_Lean_Environment_setRecordingDeps(v_env_382_, v___x_383_);
v___x_385_ = lean_st_ref_get(v___y_377_);
v_toCold_386_ = lean_ctor_get(v___y_378_, 0);
v_mctx_387_ = lean_ctor_get(v___x_385_, 0);
lean_inc_ref(v_mctx_387_);
lean_dec(v___x_385_);
v_lctx_388_ = lean_ctor_get(v___y_376_, 2);
v_options_389_ = lean_ctor_get(v_toCold_386_, 2);
lean_inc_ref(v_options_389_);
lean_inc_ref(v_lctx_388_);
v___x_390_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_390_, 0, v_env_384_);
lean_ctor_set(v___x_390_, 1, v_mctx_387_);
lean_ctor_set(v___x_390_, 2, v_lctx_388_);
lean_ctor_set(v___x_390_, 3, v_options_389_);
v___x_391_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v_msgData_375_);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_375_ = stack[0].m_obj;
lean_object* v___y_376_ = stack[1].m_obj;
lean_object* v___y_377_ = stack[2].m_obj;
lean_object* v___y_378_ = stack[3].m_obj;
lean_object* v___y_379_ = stack[4].m_obj;
lean_object* v_res_393_;
v_res_393_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(v_msgData_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
stack->m_obj
 = v_res_393_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4___boxed(lean_object* v_msgData_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(v_msgData_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_400_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(lean_object* v_msg_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_ref_407_; lean_object* v___x_408_; lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_417_; 
v_ref_407_ = lean_ctor_get(v___y_404_, 2);
v___x_408_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(v_msg_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_417_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_417_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_417_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_415_; 
lean_inc(v_ref_407_);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v_ref_407_);
lean_ctor_set(v___x_413_, 1, v_a_409_);
if (v_isShared_412_ == 0)
{
lean_ctor_set_tag(v___x_411_, 1);
lean_ctor_set(v___x_411_, 0, v___x_413_);
v___x_415_ = v___x_411_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_401_ = stack[0].m_obj;
lean_object* v___y_402_ = stack[1].m_obj;
lean_object* v___y_403_ = stack[2].m_obj;
lean_object* v___y_404_ = stack[3].m_obj;
lean_object* v___y_405_ = stack[4].m_obj;
lean_object* v_res_418_;
v_res_418_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v_msg_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
stack->m_obj
 = v_res_418_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg___boxed(lean_object* v_msg_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v_msg_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_425_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__5));
v___x_433_ = l_Lean_stringToMessageData(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__7));
v___x_436_ = l_Lean_stringToMessageData(v___x_435_);
return v___x_436_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0(lean_object* v___x_437_, lean_object* v_snd_438_, lean_object* v___x_439_, lean_object* v___x_440_, uint8_t v___x_441_, lean_object* v___x_442_, lean_object* v_fst_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
if (lean_obj_tag(v___x_437_) == 1)
{
lean_object* v_val_453_; lean_object* v_u_454_; lean_object* v_00_u03c3s_455_; lean_object* v_hyps_456_; lean_object* v_target_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_507_; 
v_val_453_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_val_453_);
lean_dec_ref_known(v___x_437_, 1);
v_u_454_ = lean_ctor_get(v_snd_438_, 0);
v_00_u03c3s_455_ = lean_ctor_get(v_snd_438_, 1);
v_hyps_456_ = lean_ctor_get(v_snd_438_, 2);
v_target_457_ = lean_ctor_get(v_snd_438_, 3);
v_isSharedCheck_507_ = !lean_is_exclusive(v_snd_438_);
if (v_isSharedCheck_507_ == 0)
{
v___x_459_ = v_snd_438_;
v_isShared_460_ = v_isSharedCheck_507_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_target_457_);
lean_inc(v_hyps_456_);
lean_inc(v_00_u03c3s_455_);
lean_inc(v_u_454_);
lean_dec(v_snd_438_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_507_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v_focusHyp_461_; lean_object* v_restHyps_462_; lean_object* v_proof_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_506_; 
v_focusHyp_461_ = lean_ctor_get(v_val_453_, 0);
v_restHyps_462_ = lean_ctor_get(v_val_453_, 1);
v_proof_463_ = lean_ctor_get(v_val_453_, 2);
v_isSharedCheck_506_ = !lean_is_exclusive(v_val_453_);
if (v_isSharedCheck_506_ == 0)
{
v___x_465_ = v_val_453_;
v_isShared_466_ = v_isSharedCheck_506_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_proof_463_);
lean_inc(v_restHyps_462_);
lean_inc(v_focusHyp_461_);
lean_dec(v_val_453_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_506_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v_a_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_467_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_451_);
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref(v___x_467_);
v___x_469_ = l_Lean_Syntax_getId(v___x_439_);
v___x_470_ = l_Lean_Expr_consumeMData(v_focusHyp_461_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 2, v___x_470_);
lean_ctor_set(v___x_465_, 1, v_a_468_);
lean_ctor_set(v___x_465_, 0, v___x_469_);
v___x_472_ = v___x_465_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_a_468_);
lean_ctor_set(v_reuseFailAlloc_505_, 2, v___x_470_);
v___x_472_ = v_reuseFailAlloc_505_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_473_; 
lean_inc_ref(v___x_472_);
lean_inc_ref(v_00_u03c3s_455_);
v___x_473_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v___x_440_, v_00_u03c3s_455_, v___x_472_, v___x_441_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
lean_dec_ref_known(v___x_473_, 1);
v___x_474_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_472_);
lean_inc_ref(v_hyps_456_);
lean_inc_ref_n(v_00_u03c3s_455_, 2);
lean_inc_n(v_u_454_, 2);
v___x_475_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_454_, v_00_u03c3s_455_, v_hyps_456_, v___x_474_);
lean_inc_ref(v_target_457_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 2, v___x_475_);
v___x_477_ = v___x_459_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_u_454_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_00_u03c3s_455_);
lean_ctor_set(v_reuseFailAlloc_504_, 2, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_504_, 3, v_target_457_);
v___x_477_ = v_reuseFailAlloc_504_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_477_);
v___x_479_ = lean_box(0);
v___x_480_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_478_, v___x_479_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc_n(v_a_481_, 2);
lean_dec_ref_known(v___x_480_, 1);
v___x_482_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0));
v___x_483_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1));
v___x_484_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2));
v___x_485_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3));
v___x_486_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__4));
v___x_487_ = l_Lean_Name_mkStr6(v___x_482_, v___x_483_, v___x_484_, v___x_442_, v___x_485_, v___x_486_);
v___x_488_ = lean_box(0);
v___x_489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_489_, 0, v_u_454_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = l_Lean_mkConst(v___x_487_, v___x_489_);
v___x_491_ = l_Lean_mkApp7(v___x_490_, v_00_u03c3s_455_, v_hyps_456_, v_restHyps_462_, v_focusHyp_461_, v_target_457_, v_proof_463_, v_a_481_);
v___x_492_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_443_, v___x_491_, v___y_449_);
lean_dec_ref(v___x_492_);
v___x_493_ = l_Lean_Expr_mvarId_x21(v_a_481_);
lean_dec(v_a_481_);
v___x_494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v___x_488_);
v___x_495_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_494_, v___y_445_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
return v___x_495_;
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v_proof_463_);
lean_dec_ref(v_restHyps_462_);
lean_dec_ref(v_focusHyp_461_);
lean_dec_ref(v_target_457_);
lean_dec_ref(v_hyps_456_);
lean_dec_ref(v_00_u03c3s_455_);
lean_dec(v_u_454_);
lean_dec(v_fst_443_);
lean_dec_ref(v___x_442_);
v_a_496_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_480_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_480_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_472_);
lean_dec_ref(v_proof_463_);
lean_dec_ref(v_restHyps_462_);
lean_dec_ref(v_focusHyp_461_);
lean_del_object(v___x_459_);
lean_dec_ref(v_target_457_);
lean_dec_ref(v_hyps_456_);
lean_dec_ref(v_00_u03c3s_455_);
lean_dec(v_u_454_);
lean_dec(v_fst_443_);
lean_dec_ref(v___x_442_);
return v___x_473_;
}
}
}
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec(v_fst_443_);
lean_dec_ref(v___x_442_);
lean_dec_ref(v_snd_438_);
lean_dec(v___x_437_);
v___x_508_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6);
v___x_509_ = l_Lean_MessageData_ofSyntax(v___x_440_);
v___x_510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8);
v___x_512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v___x_512_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
return v___x_513_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_437_ = stack[0].m_obj;
lean_object* v_snd_438_ = stack[1].m_obj;
lean_object* v___x_439_ = stack[2].m_obj;
lean_object* v___x_440_ = stack[3].m_obj;
uint8_t v___x_441_ = stack[4].m_num;
lean_object* v___x_442_ = stack[5].m_obj;
lean_object* v_fst_443_ = stack[6].m_obj;
lean_object* v___y_444_ = stack[7].m_obj;
lean_object* v___y_445_ = stack[8].m_obj;
lean_object* v___y_446_ = stack[9].m_obj;
lean_object* v___y_447_ = stack[10].m_obj;
lean_object* v___y_448_ = stack[11].m_obj;
lean_object* v___y_449_ = stack[12].m_obj;
lean_object* v___y_450_ = stack[13].m_obj;
lean_object* v___y_451_ = stack[14].m_obj;
lean_object* v_res_514_;
v_res_514_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0(v___x_437_, v_snd_438_, v___x_439_, v___x_440_, v___x_441_, v___x_442_, v_fst_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
stack->m_obj
 = v_res_514_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___boxed(lean_object* v___x_515_, lean_object* v_snd_516_, lean_object* v___x_517_, lean_object* v___x_518_, lean_object* v___x_519_, lean_object* v___x_520_, lean_object* v_fst_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
uint8_t v___x_7398__boxed_531_; lean_object* v_res_532_; 
v___x_7398__boxed_531_ = lean_unbox(v___x_519_);
v_res_532_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0(v___x_515_, v_snd_516_, v___x_517_, v___x_518_, v___x_7398__boxed_531_, v___x_520_, v_fst_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___x_517_);
return v_res_532_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup(lean_object* v_x_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2));
v___x_556_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4));
lean_inc(v_x_545_);
v___x_557_ = l_Lean_Syntax_isOfKind(v_x_545_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
lean_dec(v_x_545_);
v___x_558_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_558_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_559_ = lean_unsigned_to_nat(1u);
v___x_560_ = l_Lean_Syntax_getArg(v_x_545_, v___x_559_);
v___x_561_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__6));
lean_inc(v___x_560_);
v___x_562_ = l_Lean_Syntax_isOfKind(v___x_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; 
lean_dec(v___x_560_);
lean_dec(v_x_545_);
v___x_563_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_563_;
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_564_ = lean_unsigned_to_nat(3u);
v___x_565_ = l_Lean_Syntax_getArg(v_x_545_, v___x_564_);
lean_dec(v_x_545_);
lean_inc(v___x_565_);
v___x_566_ = l_Lean_Syntax_isOfKind(v___x_565_, v___x_561_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; 
lean_dec(v___x_565_);
lean_dec(v___x_560_);
v___x_567_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_567_;
}
else
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___y_575_; lean_object* v___x_576_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_568_, 1);
v_fst_570_ = lean_ctor_get(v_a_569_, 0);
lean_inc_n(v_fst_570_, 2);
v_snd_571_ = lean_ctor_get(v_a_569_, 1);
lean_inc_n(v_snd_571_, 2);
lean_dec(v_a_569_);
v___x_572_ = l_Lean_Syntax_getId(v___x_560_);
v___x_573_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_571_, v___x_572_);
lean_dec(v___x_572_);
v___x_574_ = lean_box(v___x_566_);
v___y_575_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___boxed), 16, 7);
lean_closure_set(v___y_575_, 0, v___x_573_);
lean_closure_set(v___y_575_, 1, v_snd_571_);
lean_closure_set(v___y_575_, 2, v___x_565_);
lean_closure_set(v___y_575_, 3, v___x_560_);
lean_closure_set(v___y_575_, 4, v___x_574_);
lean_closure_set(v___y_575_, 5, v___x_555_);
lean_closure_set(v___y_575_, 6, v_fst_570_);
v___x_576_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_570_, v___y_575_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
return v___x_576_;
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec(v___x_565_);
lean_dec(v___x_560_);
v_a_577_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_568_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_568_);
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
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMDup_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_545_ = stack[0].m_obj;
lean_object* v_a_546_ = stack[1].m_obj;
lean_object* v_a_547_ = stack[2].m_obj;
lean_object* v_a_548_ = stack[3].m_obj;
lean_object* v_a_549_ = stack[4].m_obj;
lean_object* v_a_550_ = stack[5].m_obj;
lean_object* v_a_551_ = stack[6].m_obj;
lean_object* v_a_552_ = stack[7].m_obj;
lean_object* v_a_553_ = stack[8].m_obj;
lean_object* v_res_585_;
v_res_585_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup(v_x_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
stack->m_obj
 = v_res_585_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___boxed(lean_object* v_x_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup(v_x_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
return v_res_596_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2(lean_object* v_mvarId_597_, lean_object* v_val_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_mvarId_597_, v_val_598_, v___y_604_);
return v___x_608_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_597_ = stack[0].m_obj;
lean_object* v_val_598_ = stack[1].m_obj;
lean_object* v___y_599_ = stack[2].m_obj;
lean_object* v___y_600_ = stack[3].m_obj;
lean_object* v___y_601_ = stack[4].m_obj;
lean_object* v___y_602_ = stack[5].m_obj;
lean_object* v___y_603_ = stack[6].m_obj;
lean_object* v___y_604_ = stack[7].m_obj;
lean_object* v___y_605_ = stack[8].m_obj;
lean_object* v___y_606_ = stack[9].m_obj;
lean_object* v_res_609_;
v_res_609_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2(v_mvarId_597_, v_val_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
stack->m_obj
 = v_res_609_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___boxed(lean_object* v_mvarId_610_, lean_object* v_val_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2(v_mvarId_610_, v_val_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
return v_res_621_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3(lean_object* v_00_u03b1_622_, lean_object* v_msg_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v_msg_623_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
return v___x_633_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_623_ = stack[1].m_obj;
lean_object* v___y_624_ = stack[2].m_obj;
lean_object* v___y_625_ = stack[3].m_obj;
lean_object* v___y_626_ = stack[4].m_obj;
lean_object* v___y_627_ = stack[5].m_obj;
lean_object* v___y_628_ = stack[6].m_obj;
lean_object* v___y_629_ = stack[7].m_obj;
lean_object* v___y_630_ = stack[8].m_obj;
lean_object* v___y_631_ = stack[9].m_obj;
lean_object* v_res_634_;
v_res_634_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3(lean_box(0), v_msg_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
stack->m_obj
 = v_res_634_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___boxed(lean_object* v_00_u03b1_635_, lean_object* v_msg_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3(v_00_u03b1_635_, v_msg_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2(lean_object* v_00_u03b2_647_, lean_object* v_x_648_, lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(v_x_648_, v_x_649_, v_x_650_);
return v___x_651_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_652_, lean_object* v_x_653_, size_t v_x_654_, size_t v_x_655_, lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_653_, v_x_654_, v_x_655_, v_x_656_, v_x_657_);
return v___x_658_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_653_ = stack[1].m_obj;
size_t v_x_654_ = stack[2].m_num;
size_t v_x_655_ = stack[3].m_num;
lean_object* v_x_656_ = stack[4].m_obj;
lean_object* v_x_657_ = stack[5].m_obj;
lean_object* v_res_659_;
v_res_659_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4(lean_box(0), v_x_653_, v_x_654_, v_x_655_, v_x_656_, v_x_657_);
stack->m_obj
 = v_res_659_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_660_, lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v_x_663_, lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
size_t v_x_7920__boxed_666_; size_t v_x_7921__boxed_667_; lean_object* v_res_668_; 
v_x_7920__boxed_666_ = lean_unbox_usize(v_x_662_);
lean_dec(v_x_662_);
v_x_7921__boxed_667_ = lean_unbox_usize(v_x_663_);
lean_dec(v_x_663_);
v_res_668_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4(v_00_u03b2_660_, v_x_661_, v_x_7920__boxed_666_, v_x_7921__boxed_667_, v_x_664_, v_x_665_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_669_, lean_object* v_n_670_, lean_object* v_k_671_, lean_object* v_v_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(v_n_670_, v_k_671_, v_v_672_);
return v___x_673_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_674_, size_t v_depth_675_, lean_object* v_keys_676_, lean_object* v_vals_677_, lean_object* v_heq_678_, lean_object* v_i_679_, lean_object* v_entries_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_675_, v_keys_676_, v_vals_677_, v_i_679_, v_entries_680_);
return v___x_681_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_depth_675_ = stack[1].m_num;
lean_object* v_keys_676_ = stack[2].m_obj;
lean_object* v_vals_677_ = stack[3].m_obj;
lean_object* v_i_679_ = stack[5].m_obj;
lean_object* v_entries_680_ = stack[6].m_obj;
lean_object* v_res_682_;
v_res_682_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8(lean_box(0), v_depth_675_, v_keys_676_, v_vals_677_, lean_box(0), v_i_679_, v_entries_680_);
stack->m_obj
 = v_res_682_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_683_, lean_object* v_depth_684_, lean_object* v_keys_685_, lean_object* v_vals_686_, lean_object* v_heq_687_, lean_object* v_i_688_, lean_object* v_entries_689_){
_start:
{
size_t v_depth_boxed_690_; lean_object* v_res_691_; 
v_depth_boxed_690_ = lean_unbox_usize(v_depth_684_);
lean_dec(v_depth_684_);
v_res_691_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_683_, v_depth_boxed_690_, v_keys_685_, v_vals_686_, v_heq_687_, v_i_688_, v_entries_689_);
lean_dec_ref(v_vals_686_);
lean_dec_ref(v_keys_685_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_692_, lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_693_, v_x_694_, v_x_695_, v_x_696_);
return v___x_697_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1(){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_709_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_710_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4));
v___x_711_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3));
v___x_712_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___boxed), 10, 0);
v___x_713_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_709_, v___x_710_, v___x_711_, v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_714_;
v_res_714_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1();
stack->m_obj
 = v_res_714_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___boxed(lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1();
return v_res_716_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0(lean_object* v___x_718_, lean_object* v_00_u03c3s_719_, uint8_t v___x_720_, lean_object* v_u_721_, lean_object* v_hyps_722_, lean_object* v___x_723_, lean_object* v_target_724_, lean_object* v___x_725_, lean_object* v___x_726_, lean_object* v___x_727_, lean_object* v___x_728_, lean_object* v___x_729_, lean_object* v_fst_730_, lean_object* v_H_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_741_; lean_object* v_a_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_741_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_739_);
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref(v___x_741_);
v___x_743_ = l_Lean_Syntax_getId(v___x_718_);
lean_inc_ref(v_H_731_);
v___x_744_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v_a_742_);
lean_ctor_set(v___x_744_, 2, v_H_731_);
lean_inc_ref(v___x_744_);
lean_inc_ref(v_00_u03c3s_719_);
v___x_745_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v___x_718_, v_00_u03c3s_719_, v___x_744_, v___x_720_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_798_; 
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v___x_745_, 0);
lean_dec(v_unused_799_);
v___x_747_ = v___x_745_;
v_isShared_748_ = v_isSharedCheck_798_;
goto v_resetjp_746_;
}
else
{
lean_dec(v___x_745_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_798_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_fst_751_; lean_object* v_snd_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_797_; 
v___x_749_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_744_);
lean_inc_ref(v___x_749_);
lean_inc_ref(v_hyps_722_);
lean_inc_ref(v_00_u03c3s_719_);
lean_inc(v_u_721_);
v___x_750_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_721_, v_00_u03c3s_719_, v_hyps_722_, v___x_749_);
v_fst_751_ = lean_ctor_get(v___x_750_, 0);
v_snd_752_ = lean_ctor_get(v___x_750_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_797_ == 0)
{
v___x_754_ = v___x_750_;
v_isShared_755_ = v_isSharedCheck_797_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_snd_752_);
lean_inc(v_fst_751_);
lean_dec(v___x_750_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_797_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
lean_inc_ref(v_hyps_722_);
lean_inc_ref(v_00_u03c3s_719_);
lean_inc(v_u_721_);
v___x_756_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_756_, 0, v_u_721_);
lean_ctor_set(v___x_756_, 1, v_00_u03c3s_719_);
lean_ctor_set(v___x_756_, 2, v_hyps_722_);
lean_ctor_set(v___x_756_, 3, v_H_731_);
v___x_757_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_756_);
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 1);
lean_ctor_set(v___x_747_, 0, v___x_757_);
v___x_759_ = v___x_747_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_796_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
uint8_t v___x_760_; lean_object* v___x_761_; 
v___x_760_ = 0;
v___x_761_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v___x_723_, v___x_759_, v___x_760_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
lean_inc_ref(v_target_724_);
lean_inc(v_fst_751_);
lean_inc_ref(v_00_u03c3s_719_);
v___x_763_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_763_, 0, v_u_721_);
lean_ctor_set(v___x_763_, 1, v_00_u03c3s_719_);
lean_ctor_set(v___x_763_, 2, v_fst_751_);
lean_ctor_set(v___x_763_, 3, v_target_724_);
v___x_764_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_763_);
v___x_765_ = lean_box(0);
v___x_766_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_764_, v___x_765_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc_n(v_a_767_, 2);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3));
v___x_769_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___closed__0));
v___x_770_ = l_Lean_Name_mkStr6(v___x_725_, v___x_726_, v___x_727_, v___x_728_, v___x_768_, v___x_769_);
v___x_771_ = l_Lean_mkConst(v___x_770_, v___x_729_);
v___x_772_ = l_Lean_mkApp8(v___x_771_, v_00_u03c3s_719_, v_hyps_722_, v___x_749_, v_fst_751_, v_target_724_, v_snd_752_, v_a_762_, v_a_767_);
v___x_773_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_730_, v___x_772_, v___y_737_);
lean_dec_ref(v___x_773_);
v___x_774_ = l_Lean_Expr_mvarId_x21(v_a_767_);
lean_dec(v_a_767_);
v___x_775_ = lean_box(0);
if (v_isShared_755_ == 0)
{
lean_ctor_set_tag(v___x_754_, 1);
lean_ctor_set(v___x_754_, 1, v___x_775_);
lean_ctor_set(v___x_754_, 0, v___x_774_);
v___x_777_ = v___x_754_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_775_);
v___x_777_ = v_reuseFailAlloc_779_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_777_, v___y_733_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
return v___x_778_;
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec(v_a_762_);
lean_del_object(v___x_754_);
lean_dec(v_snd_752_);
lean_dec(v_fst_751_);
lean_dec_ref(v___x_749_);
lean_dec(v_fst_730_);
lean_dec(v___x_729_);
lean_dec_ref(v___x_728_);
lean_dec_ref(v___x_727_);
lean_dec_ref(v___x_726_);
lean_dec_ref(v___x_725_);
lean_dec_ref(v_target_724_);
lean_dec_ref(v_hyps_722_);
lean_dec_ref(v_00_u03c3s_719_);
v_a_780_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_766_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_766_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_del_object(v___x_754_);
lean_dec(v_snd_752_);
lean_dec(v_fst_751_);
lean_dec_ref(v___x_749_);
lean_dec(v_fst_730_);
lean_dec(v___x_729_);
lean_dec_ref(v___x_728_);
lean_dec_ref(v___x_727_);
lean_dec_ref(v___x_726_);
lean_dec_ref(v___x_725_);
lean_dec_ref(v_target_724_);
lean_dec_ref(v_hyps_722_);
lean_dec(v_u_721_);
lean_dec_ref(v_00_u03c3s_719_);
v_a_788_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_761_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_761_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_744_, 3);
lean_dec_ref(v_H_731_);
lean_dec(v_fst_730_);
lean_dec(v___x_729_);
lean_dec_ref(v___x_728_);
lean_dec_ref(v___x_727_);
lean_dec_ref(v___x_726_);
lean_dec_ref(v___x_725_);
lean_dec_ref(v_target_724_);
lean_dec(v___x_723_);
lean_dec_ref(v_hyps_722_);
lean_dec(v_u_721_);
lean_dec_ref(v_00_u03c3s_719_);
return v___x_745_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_718_ = stack[0].m_obj;
lean_object* v_00_u03c3s_719_ = stack[1].m_obj;
uint8_t v___x_720_ = stack[2].m_num;
lean_object* v_u_721_ = stack[3].m_obj;
lean_object* v_hyps_722_ = stack[4].m_obj;
lean_object* v___x_723_ = stack[5].m_obj;
lean_object* v_target_724_ = stack[6].m_obj;
lean_object* v___x_725_ = stack[7].m_obj;
lean_object* v___x_726_ = stack[8].m_obj;
lean_object* v___x_727_ = stack[9].m_obj;
lean_object* v___x_728_ = stack[10].m_obj;
lean_object* v___x_729_ = stack[11].m_obj;
lean_object* v_fst_730_ = stack[12].m_obj;
lean_object* v_H_731_ = stack[13].m_obj;
lean_object* v___y_732_ = stack[14].m_obj;
lean_object* v___y_733_ = stack[15].m_obj;
lean_object* v___y_734_ = stack[16].m_obj;
lean_object* v___y_735_ = stack[17].m_obj;
lean_object* v___y_736_ = stack[18].m_obj;
lean_object* v___y_737_ = stack[19].m_obj;
lean_object* v___y_738_ = stack[20].m_obj;
lean_object* v___y_739_ = stack[21].m_obj;
lean_object* v_res_800_;
v_res_800_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0(v___x_718_, v_00_u03c3s_719_, v___x_720_, v_u_721_, v_hyps_722_, v___x_723_, v_target_724_, v___x_725_, v___x_726_, v___x_727_, v___x_728_, v___x_729_, v_fst_730_, v_H_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___boxed(lean_object** _args){
lean_object* v___x_801_ = _args[0];
lean_object* v_00_u03c3s_802_ = _args[1];
lean_object* v___x_803_ = _args[2];
lean_object* v_u_804_ = _args[3];
lean_object* v_hyps_805_ = _args[4];
lean_object* v___x_806_ = _args[5];
lean_object* v_target_807_ = _args[6];
lean_object* v___x_808_ = _args[7];
lean_object* v___x_809_ = _args[8];
lean_object* v___x_810_ = _args[9];
lean_object* v___x_811_ = _args[10];
lean_object* v___x_812_ = _args[11];
lean_object* v_fst_813_ = _args[12];
lean_object* v_H_814_ = _args[13];
lean_object* v___y_815_ = _args[14];
lean_object* v___y_816_ = _args[15];
lean_object* v___y_817_ = _args[16];
lean_object* v___y_818_ = _args[17];
lean_object* v___y_819_ = _args[18];
lean_object* v___y_820_ = _args[19];
lean_object* v___y_821_ = _args[20];
lean_object* v___y_822_ = _args[21];
lean_object* v___y_823_ = _args[22];
_start:
{
uint8_t v___x_2162__boxed_824_; lean_object* v_res_825_; 
v___x_2162__boxed_824_ = lean_unbox(v___x_803_);
v_res_825_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0(v___x_801_, v_00_u03c3s_802_, v___x_2162__boxed_824_, v_u_804_, v_hyps_805_, v___x_806_, v_target_807_, v___x_808_, v___x_809_, v___x_810_, v___x_811_, v___x_812_, v_fst_813_, v_H_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
return v_res_825_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1(lean_object* v_ty_x3f_826_, lean_object* v___x_827_, lean_object* v___f_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
if (lean_obj_tag(v_ty_x3f_826_) == 1)
{
lean_object* v_val_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_857_; 
v_val_838_ = lean_ctor_get(v_ty_x3f_826_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v_ty_x3f_826_);
if (v_isSharedCheck_857_ == 0)
{
v___x_840_ = v_ty_x3f_826_;
v_isShared_841_ = v_isSharedCheck_857_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_val_838_);
lean_dec(v_ty_x3f_826_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_857_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_827_);
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_827_);
v___x_843_ = v_reuseFailAlloc_856_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
uint8_t v___x_844_; lean_object* v___x_845_; 
v___x_844_ = 0;
v___x_845_ = l_Lean_Elab_Tactic_elabTerm(v_val_838_, v___x_843_, v___x_844_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_847_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_845_, 1);
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
lean_inc(v___y_834_);
lean_inc_ref(v___y_833_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
v___x_847_ = lean_apply_10(v___f_828_, v_a_846_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, lean_box(0));
return v___x_847_;
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec_ref(v___f_828_);
v_a_848_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_845_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_845_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
}
else
{
lean_object* v___x_858_; uint8_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec(v_ty_x3f_826_);
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_827_);
v___x_859_ = 0;
v___x_860_ = lean_box(0);
v___x_861_ = l_Lean_Meta_mkFreshExprMVar(v___x_858_, v___x_859_, v___x_860_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_863_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref_known(v___x_861_, 1);
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
lean_inc(v___y_834_);
lean_inc_ref(v___y_833_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
v___x_863_ = lean_apply_10(v___f_828_, v_a_862_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, lean_box(0));
return v___x_863_;
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec_ref(v___f_828_);
v_a_864_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_861_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_861_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ty_x3f_826_ = stack[0].m_obj;
lean_object* v___x_827_ = stack[1].m_obj;
lean_object* v___f_828_ = stack[2].m_obj;
lean_object* v___y_829_ = stack[3].m_obj;
lean_object* v___y_830_ = stack[4].m_obj;
lean_object* v___y_831_ = stack[5].m_obj;
lean_object* v___y_832_ = stack[6].m_obj;
lean_object* v___y_833_ = stack[7].m_obj;
lean_object* v___y_834_ = stack[8].m_obj;
lean_object* v___y_835_ = stack[9].m_obj;
lean_object* v___y_836_ = stack[10].m_obj;
lean_object* v_res_872_;
v_res_872_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1(v_ty_x3f_826_, v___x_827_, v___f_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
stack->m_obj
 = v_res_872_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1___boxed(lean_object* v_ty_x3f_873_, lean_object* v___x_874_, lean_object* v___f_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1(v_ty_x3f_873_, v___x_874_, v___f_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
return v_res_885_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave(lean_object* v_x_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_906_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2));
v___x_907_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1));
lean_inc(v_x_896_);
v___x_908_ = l_Lean_Syntax_isOfKind(v_x_896_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
lean_dec(v_x_896_);
v___x_909_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_909_;
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v_ty_x3f_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_910_ = lean_unsigned_to_nat(1u);
v___x_911_ = l_Lean_Syntax_getArg(v_x_896_, v___x_910_);
v___x_958_ = lean_unsigned_to_nat(2u);
v___x_959_ = l_Lean_Syntax_getArg(v_x_896_, v___x_958_);
v___x_960_ = l_Lean_Syntax_isNone(v___x_959_);
if (v___x_960_ == 0)
{
uint8_t v___x_961_; 
lean_inc(v___x_959_);
v___x_961_ = l_Lean_Syntax_matchesNull(v___x_959_, v___x_958_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
lean_dec(v___x_959_);
lean_dec(v___x_911_);
lean_dec(v_x_896_);
v___x_962_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_962_;
}
else
{
lean_object* v_ty_x3f_963_; lean_object* v___x_964_; 
v_ty_x3f_963_ = l_Lean_Syntax_getArg(v___x_959_, v___x_910_);
lean_dec(v___x_959_);
v___x_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_964_, 0, v_ty_x3f_963_);
v_ty_x3f_913_ = v___x_964_;
v___y_914_ = v_a_897_;
v___y_915_ = v_a_898_;
v___y_916_ = v_a_899_;
v___y_917_ = v_a_900_;
v___y_918_ = v_a_901_;
v___y_919_ = v_a_902_;
v___y_920_ = v_a_903_;
v___y_921_ = v_a_904_;
goto v___jp_912_;
}
}
else
{
lean_object* v___x_965_; 
lean_dec(v___x_959_);
v___x_965_ = lean_box(0);
v_ty_x3f_913_ = v___x_965_;
v___y_914_ = v_a_897_;
v___y_915_ = v_a_898_;
v___y_916_ = v_a_899_;
v___y_917_ = v_a_900_;
v___y_918_ = v_a_901_;
v___y_919_ = v_a_902_;
v___y_920_ = v_a_903_;
v___y_921_ = v_a_904_;
goto v___jp_912_;
}
v___jp_912_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_unsigned_to_nat(4u);
v___x_923_ = l_Lean_Syntax_getArg(v_x_896_, v___x_922_);
lean_dec(v_x_896_);
v___x_924_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v_snd_926_; lean_object* v_fst_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_949_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_924_, 1);
v_snd_926_ = lean_ctor_get(v_a_925_, 1);
v_fst_927_ = lean_ctor_get(v_a_925_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_a_925_);
if (v_isSharedCheck_949_ == 0)
{
v___x_929_ = v_a_925_;
v_isShared_930_ = v_isSharedCheck_949_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_snd_926_);
lean_inc(v_fst_927_);
lean_dec(v_a_925_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_949_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v_u_931_; lean_object* v_00_u03c3s_932_; lean_object* v_hyps_933_; lean_object* v_target_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
v_u_931_ = lean_ctor_get(v_snd_926_, 0);
lean_inc_n(v_u_931_, 2);
v_00_u03c3s_932_ = lean_ctor_get(v_snd_926_, 1);
lean_inc_ref(v_00_u03c3s_932_);
v_hyps_933_ = lean_ctor_get(v_snd_926_, 2);
lean_inc_ref(v_hyps_933_);
v_target_934_ = lean_ctor_get(v_snd_926_, 3);
lean_inc_ref(v_target_934_);
lean_dec(v_snd_926_);
v___x_935_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0));
v___x_936_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1));
v___x_937_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2));
v___x_938_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2));
v___x_939_ = lean_box(0);
if (v_isShared_930_ == 0)
{
lean_ctor_set_tag(v___x_929_, 1);
lean_ctor_set(v___x_929_, 1, v___x_939_);
lean_ctor_set(v___x_929_, 0, v_u_931_);
v___x_941_ = v___x_929_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_u_931_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_939_);
v___x_941_ = v_reuseFailAlloc_948_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_942_; lean_object* v___f_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___y_946_; lean_object* v___x_947_; 
v___x_942_ = lean_box(v___x_908_);
lean_inc(v_fst_927_);
lean_inc_ref(v___x_941_);
lean_inc_ref(v_00_u03c3s_932_);
v___f_943_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___boxed), 23, 13);
lean_closure_set(v___f_943_, 0, v___x_911_);
lean_closure_set(v___f_943_, 1, v_00_u03c3s_932_);
lean_closure_set(v___f_943_, 2, v___x_942_);
lean_closure_set(v___f_943_, 3, v_u_931_);
lean_closure_set(v___f_943_, 4, v_hyps_933_);
lean_closure_set(v___f_943_, 5, v___x_923_);
lean_closure_set(v___f_943_, 6, v_target_934_);
lean_closure_set(v___f_943_, 7, v___x_935_);
lean_closure_set(v___f_943_, 8, v___x_936_);
lean_closure_set(v___f_943_, 9, v___x_937_);
lean_closure_set(v___f_943_, 10, v___x_906_);
lean_closure_set(v___f_943_, 11, v___x_941_);
lean_closure_set(v___f_943_, 12, v_fst_927_);
v___x_944_ = l_Lean_mkConst(v___x_938_, v___x_941_);
v___x_945_ = l_Lean_Expr_app___override(v___x_944_, v_00_u03c3s_932_);
v___y_946_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1___boxed), 12, 3);
lean_closure_set(v___y_946_, 0, v_ty_x3f_913_);
lean_closure_set(v___y_946_, 1, v___x_945_);
lean_closure_set(v___y_946_, 2, v___f_943_);
v___x_947_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_927_, v___y_946_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
return v___x_947_;
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec(v___x_923_);
lean_dec(v_ty_x3f_913_);
lean_dec(v___x_911_);
v_a_950_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_924_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_924_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMHave_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_896_ = stack[0].m_obj;
lean_object* v_a_897_ = stack[1].m_obj;
lean_object* v_a_898_ = stack[2].m_obj;
lean_object* v_a_899_ = stack[3].m_obj;
lean_object* v_a_900_ = stack[4].m_obj;
lean_object* v_a_901_ = stack[5].m_obj;
lean_object* v_a_902_ = stack[6].m_obj;
lean_object* v_a_903_ = stack[7].m_obj;
lean_object* v_a_904_ = stack[8].m_obj;
lean_object* v_res_966_;
v_res_966_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave(v_x_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
stack->m_obj
 = v_res_966_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___boxed(lean_object* v_x_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave(v_x_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
return v_res_977_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1(){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_987_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_988_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1));
v___x_989_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1));
v___x_990_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___boxed), 10, 0);
v___x_991_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_987_, v___x_988_, v___x_989_, v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_992_;
v_res_992_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1();
stack->m_obj
 = v_res_992_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___boxed(lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1();
return v_res_994_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0(lean_object* v___x_996_, lean_object* v_u_997_, lean_object* v___x_998_, lean_object* v___x_999_, lean_object* v_00_u03c3s_1000_, uint8_t v___x_1001_, lean_object* v_hyps_1002_, lean_object* v___x_1003_, lean_object* v_target_1004_, lean_object* v___x_1005_, lean_object* v_fst_1006_, lean_object* v_ty_x3f_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
if (lean_obj_tag(v___x_996_) == 1)
{
lean_object* v_val_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1133_; 
v_val_1017_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1019_ = v___x_996_;
v_isShared_1020_ = v_isSharedCheck_1133_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_val_1017_);
lean_dec(v___x_996_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1133_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v_focusHyp_1021_; lean_object* v_restHyps_1022_; lean_object* v_proof_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1132_; 
v_focusHyp_1021_ = lean_ctor_get(v_val_1017_, 0);
v_restHyps_1022_ = lean_ctor_get(v_val_1017_, 1);
v_proof_1023_ = lean_ctor_get(v_val_1017_, 2);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_val_1017_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1025_ = v_val_1017_;
v_isShared_1026_ = v_isSharedCheck_1132_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_proof_1023_);
lean_inc(v_restHyps_1022_);
lean_inc(v_focusHyp_1021_);
lean_dec(v_val_1017_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1132_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v_H_x27_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1027_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0));
v___x_1028_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1));
v___x_1029_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2));
v___x_1030_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2));
v___x_1031_ = lean_box(0);
lean_inc(v_u_997_);
v___x_1032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1032_, 0, v_u_997_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
lean_inc_ref(v___x_1032_);
v___x_1098_ = l_Lean_mkConst(v___x_1030_, v___x_1032_);
lean_inc_ref(v_00_u03c3s_1000_);
v___x_1099_ = l_Lean_Expr_app___override(v___x_1098_, v_00_u03c3s_1000_);
if (lean_obj_tag(v_ty_x3f_1007_) == 1)
{
lean_object* v_val_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1118_; 
v_val_1100_ = lean_ctor_get(v_ty_x3f_1007_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_ty_x3f_1007_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1102_ = v_ty_x3f_1007_;
v_isShared_1103_ = v_isSharedCheck_1118_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_val_1100_);
lean_dec(v_ty_x3f_1007_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1118_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v___x_1099_);
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1099_);
v___x_1105_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
uint8_t v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = 0;
v___x_1107_ = l_Lean_Elab_Tactic_elabTerm(v_val_1100_, v___x_1105_, v___x_1106_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___x_1107_, 1);
v_H_x27_1034_ = v_a_1108_;
v___y_1035_ = v___y_1008_;
v___y_1036_ = v___y_1009_;
v___y_1037_ = v___y_1010_;
v___y_1038_ = v___y_1011_;
v___y_1039_ = v___y_1012_;
v___y_1040_ = v___y_1013_;
v___y_1041_ = v___y_1014_;
v___y_1042_ = v___y_1015_;
goto v___jp_1033_;
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec_ref_known(v___x_1032_, 2);
lean_del_object(v___x_1025_);
lean_dec_ref(v_proof_1023_);
lean_dec_ref(v_restHyps_1022_);
lean_dec_ref(v_focusHyp_1021_);
lean_del_object(v___x_1019_);
lean_dec(v_fst_1006_);
lean_dec_ref(v___x_1005_);
lean_dec_ref(v_target_1004_);
lean_dec(v___x_1003_);
lean_dec_ref(v_hyps_1002_);
lean_dec_ref(v_00_u03c3s_1000_);
lean_dec(v___x_999_);
lean_dec(v___x_998_);
lean_dec(v_u_997_);
v_a_1109_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1107_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1107_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
}
else
{
lean_object* v___x_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_dec(v_ty_x3f_1007_);
v___x_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1099_);
v___x_1120_ = 0;
v___x_1121_ = lean_box(0);
v___x_1122_ = l_Lean_Meta_mkFreshExprMVar(v___x_1119_, v___x_1120_, v___x_1121_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
v_H_x27_1034_ = v_a_1123_;
v___y_1035_ = v___y_1008_;
v___y_1036_ = v___y_1009_;
v___y_1037_ = v___y_1010_;
v___y_1038_ = v___y_1011_;
v___y_1039_ = v___y_1012_;
v___y_1040_ = v___y_1013_;
v___y_1041_ = v___y_1014_;
v___y_1042_ = v___y_1015_;
goto v___jp_1033_;
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec_ref_known(v___x_1032_, 2);
lean_del_object(v___x_1025_);
lean_dec_ref(v_proof_1023_);
lean_dec_ref(v_restHyps_1022_);
lean_dec_ref(v_focusHyp_1021_);
lean_del_object(v___x_1019_);
lean_dec(v_fst_1006_);
lean_dec_ref(v___x_1005_);
lean_dec_ref(v_target_1004_);
lean_dec(v___x_1003_);
lean_dec_ref(v_hyps_1002_);
lean_dec_ref(v_00_u03c3s_1000_);
lean_dec(v___x_999_);
lean_dec(v___x_998_);
lean_dec(v_u_997_);
v_a_1124_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1122_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1122_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
v___jp_1033_:
{
lean_object* v___x_1043_; lean_object* v_a_1044_; lean_object* v___x_1046_; 
v___x_1043_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_1042_);
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref(v___x_1043_);
lean_inc_ref(v_H_x27_1034_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 2, v_H_x27_1034_);
lean_ctor_set(v___x_1025_, 1, v_a_1044_);
lean_ctor_set(v___x_1025_, 0, v___x_998_);
v___x_1046_ = v___x_1025_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_a_1044_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_H_x27_1034_);
v___x_1046_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; 
lean_inc_ref(v___x_1046_);
lean_inc_ref(v_00_u03c3s_1000_);
v___x_1047_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v___x_999_, v_00_u03c3s_1000_, v___x_1046_, v___x_1001_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
lean_dec_ref_known(v___x_1047_, 1);
v___x_1048_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1046_);
lean_inc_ref(v_hyps_1002_);
lean_inc_ref(v_00_u03c3s_1000_);
lean_inc(v_u_997_);
v___x_1049_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1049_, 0, v_u_997_);
lean_ctor_set(v___x_1049_, 1, v_00_u03c3s_1000_);
lean_ctor_set(v___x_1049_, 2, v_hyps_1002_);
lean_ctor_set(v___x_1049_, 3, v_H_x27_1034_);
v___x_1050_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1049_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1050_);
v___x_1052_ = v___x_1019_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
uint8_t v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = 0;
v___x_1054_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v___x_1003_, v___x_1052_, v___x_1053_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1056_; lean_object* v_fst_1057_; lean_object* v_snd_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1087_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1054_, 1);
lean_inc_ref(v___x_1048_);
lean_inc_ref(v_restHyps_1022_);
lean_inc_ref(v_00_u03c3s_1000_);
lean_inc(v_u_997_);
v___x_1056_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_997_, v_00_u03c3s_1000_, v_restHyps_1022_, v___x_1048_);
v_fst_1057_ = lean_ctor_get(v___x_1056_, 0);
v_snd_1058_ = lean_ctor_get(v___x_1056_, 1);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1060_ = v___x_1056_;
v_isShared_1061_ = v_isSharedCheck_1087_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_snd_1058_);
lean_inc(v_fst_1057_);
lean_dec(v___x_1056_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1087_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_inc_ref(v_target_1004_);
lean_inc(v_fst_1057_);
lean_inc_ref(v_00_u03c3s_1000_);
v___x_1062_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1062_, 0, v_u_997_);
lean_ctor_set(v___x_1062_, 1, v_00_u03c3s_1000_);
lean_ctor_set(v___x_1062_, 2, v_fst_1057_);
lean_ctor_set(v___x_1062_, 3, v_target_1004_);
v___x_1063_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1062_);
v___x_1064_ = lean_box(0);
v___x_1065_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1063_, v___x_1064_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc_n(v_a_1066_, 2);
lean_dec_ref_known(v___x_1065_, 1);
v___x_1067_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3));
v___x_1068_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___closed__0));
v___x_1069_ = l_Lean_Name_mkStr6(v___x_1027_, v___x_1028_, v___x_1029_, v___x_1005_, v___x_1067_, v___x_1068_);
v___x_1070_ = l_Lean_mkConst(v___x_1069_, v___x_1032_);
v___x_1071_ = l_Lean_mkApp10(v___x_1070_, v_00_u03c3s_1000_, v_restHyps_1022_, v_focusHyp_1021_, v___x_1048_, v_hyps_1002_, v_fst_1057_, v_target_1004_, v_proof_1023_, v_snd_1058_, v_a_1055_);
v___x_1072_ = l_Lean_Expr_app___override(v___x_1071_, v_a_1066_);
v___x_1073_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_1006_, v___x_1072_, v___y_1040_);
lean_dec_ref(v___x_1073_);
v___x_1074_ = l_Lean_Expr_mvarId_x21(v_a_1066_);
lean_dec(v_a_1066_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 1);
lean_ctor_set(v___x_1060_, 1, v___x_1031_);
lean_ctor_set(v___x_1060_, 0, v___x_1074_);
v___x_1076_ = v___x_1060_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v___x_1031_);
v___x_1076_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1076_, v___y_1036_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
return v___x_1077_;
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_del_object(v___x_1060_);
lean_dec(v_snd_1058_);
lean_dec(v_fst_1057_);
lean_dec(v_a_1055_);
lean_dec_ref(v___x_1048_);
lean_dec_ref_known(v___x_1032_, 2);
lean_dec_ref(v_proof_1023_);
lean_dec_ref(v_restHyps_1022_);
lean_dec_ref(v_focusHyp_1021_);
lean_dec(v_fst_1006_);
lean_dec_ref(v___x_1005_);
lean_dec_ref(v_target_1004_);
lean_dec_ref(v_hyps_1002_);
lean_dec_ref(v_00_u03c3s_1000_);
v_a_1079_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1065_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1065_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec_ref(v___x_1048_);
lean_dec_ref_known(v___x_1032_, 2);
lean_dec_ref(v_proof_1023_);
lean_dec_ref(v_restHyps_1022_);
lean_dec_ref(v_focusHyp_1021_);
lean_dec(v_fst_1006_);
lean_dec_ref(v___x_1005_);
lean_dec_ref(v_target_1004_);
lean_dec_ref(v_hyps_1002_);
lean_dec_ref(v_00_u03c3s_1000_);
lean_dec(v_u_997_);
v_a_1088_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1054_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1054_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1046_);
lean_dec_ref(v_H_x27_1034_);
lean_dec_ref_known(v___x_1032_, 2);
lean_dec_ref(v_proof_1023_);
lean_dec_ref(v_restHyps_1022_);
lean_dec_ref(v_focusHyp_1021_);
lean_del_object(v___x_1019_);
lean_dec(v_fst_1006_);
lean_dec_ref(v___x_1005_);
lean_dec_ref(v_target_1004_);
lean_dec(v___x_1003_);
lean_dec_ref(v_hyps_1002_);
lean_dec_ref(v_00_u03c3s_1000_);
lean_dec(v_u_997_);
return v___x_1047_;
}
}
}
}
}
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec(v_ty_x3f_1007_);
lean_dec(v_fst_1006_);
lean_dec_ref(v___x_1005_);
lean_dec_ref(v_target_1004_);
lean_dec(v___x_1003_);
lean_dec_ref(v_hyps_1002_);
lean_dec_ref(v_00_u03c3s_1000_);
lean_dec(v___x_998_);
lean_dec(v_u_997_);
lean_dec(v___x_996_);
v___x_1134_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6);
v___x_1135_ = l_Lean_MessageData_ofSyntax(v___x_999_);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v___x_1138_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
return v___x_1139_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_996_ = stack[0].m_obj;
lean_object* v_u_997_ = stack[1].m_obj;
lean_object* v___x_998_ = stack[2].m_obj;
lean_object* v___x_999_ = stack[3].m_obj;
lean_object* v_00_u03c3s_1000_ = stack[4].m_obj;
uint8_t v___x_1001_ = stack[5].m_num;
lean_object* v_hyps_1002_ = stack[6].m_obj;
lean_object* v___x_1003_ = stack[7].m_obj;
lean_object* v_target_1004_ = stack[8].m_obj;
lean_object* v___x_1005_ = stack[9].m_obj;
lean_object* v_fst_1006_ = stack[10].m_obj;
lean_object* v_ty_x3f_1007_ = stack[11].m_obj;
lean_object* v___y_1008_ = stack[12].m_obj;
lean_object* v___y_1009_ = stack[13].m_obj;
lean_object* v___y_1010_ = stack[14].m_obj;
lean_object* v___y_1011_ = stack[15].m_obj;
lean_object* v___y_1012_ = stack[16].m_obj;
lean_object* v___y_1013_ = stack[17].m_obj;
lean_object* v___y_1014_ = stack[18].m_obj;
lean_object* v___y_1015_ = stack[19].m_obj;
lean_object* v_res_1140_;
v_res_1140_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0(v___x_996_, v_u_997_, v___x_998_, v___x_999_, v_00_u03c3s_1000_, v___x_1001_, v_hyps_1002_, v___x_1003_, v_target_1004_, v___x_1005_, v_fst_1006_, v_ty_x3f_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
stack->m_obj
 = v_res_1140_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___boxed(lean_object** _args){
lean_object* v___x_1141_ = _args[0];
lean_object* v_u_1142_ = _args[1];
lean_object* v___x_1143_ = _args[2];
lean_object* v___x_1144_ = _args[3];
lean_object* v_00_u03c3s_1145_ = _args[4];
lean_object* v___x_1146_ = _args[5];
lean_object* v_hyps_1147_ = _args[6];
lean_object* v___x_1148_ = _args[7];
lean_object* v_target_1149_ = _args[8];
lean_object* v___x_1150_ = _args[9];
lean_object* v_fst_1151_ = _args[10];
lean_object* v_ty_x3f_1152_ = _args[11];
lean_object* v___y_1153_ = _args[12];
lean_object* v___y_1154_ = _args[13];
lean_object* v___y_1155_ = _args[14];
lean_object* v___y_1156_ = _args[15];
lean_object* v___y_1157_ = _args[16];
lean_object* v___y_1158_ = _args[17];
lean_object* v___y_1159_ = _args[18];
lean_object* v___y_1160_ = _args[19];
lean_object* v___y_1161_ = _args[20];
_start:
{
uint8_t v___x_2642__boxed_1162_; lean_object* v_res_1163_; 
v___x_2642__boxed_1162_ = lean_unbox(v___x_1146_);
v_res_1163_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0(v___x_1141_, v_u_1142_, v___x_1143_, v___x_1144_, v_00_u03c3s_1145_, v___x_2642__boxed_1162_, v_hyps_1147_, v___x_1148_, v_target_1149_, v___x_1150_, v_fst_1151_, v_ty_x3f_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
return v_res_1163_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace(lean_object* v_x_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1180_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2));
v___x_1181_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1));
lean_inc(v_x_1170_);
v___x_1182_ = l_Lean_Syntax_isOfKind(v_x_1170_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
lean_dec(v_x_1170_);
v___x_1183_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_1183_;
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v_ty_x3f_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1184_ = lean_unsigned_to_nat(1u);
v___x_1185_ = l_Lean_Syntax_getArg(v_x_1170_, v___x_1184_);
v___x_1219_ = lean_unsigned_to_nat(2u);
v___x_1220_ = l_Lean_Syntax_getArg(v_x_1170_, v___x_1219_);
v___x_1221_ = l_Lean_Syntax_isNone(v___x_1220_);
if (v___x_1221_ == 0)
{
uint8_t v___x_1222_; 
lean_inc(v___x_1220_);
v___x_1222_ = l_Lean_Syntax_matchesNull(v___x_1220_, v___x_1219_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; 
lean_dec(v___x_1220_);
lean_dec(v___x_1185_);
lean_dec(v_x_1170_);
v___x_1223_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_1223_;
}
else
{
lean_object* v_ty_x3f_1224_; lean_object* v___x_1225_; 
v_ty_x3f_1224_ = l_Lean_Syntax_getArg(v___x_1220_, v___x_1184_);
lean_dec(v___x_1220_);
v___x_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1225_, 0, v_ty_x3f_1224_);
v_ty_x3f_1187_ = v___x_1225_;
v___y_1188_ = v_a_1171_;
v___y_1189_ = v_a_1172_;
v___y_1190_ = v_a_1173_;
v___y_1191_ = v_a_1174_;
v___y_1192_ = v_a_1175_;
v___y_1193_ = v_a_1176_;
v___y_1194_ = v_a_1177_;
v___y_1195_ = v_a_1178_;
goto v___jp_1186_;
}
}
else
{
lean_object* v___x_1226_; 
lean_dec(v___x_1220_);
v___x_1226_ = lean_box(0);
v_ty_x3f_1187_ = v___x_1226_;
v___y_1188_ = v_a_1171_;
v___y_1189_ = v_a_1172_;
v___y_1190_ = v_a_1173_;
v___y_1191_ = v_a_1174_;
v___y_1192_ = v_a_1175_;
v___y_1193_ = v_a_1176_;
v___y_1194_ = v_a_1177_;
v___y_1195_ = v_a_1178_;
goto v___jp_1186_;
}
v___jp_1186_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = lean_unsigned_to_nat(4u);
v___x_1197_ = l_Lean_Syntax_getArg(v_x_1170_, v___x_1196_);
lean_dec(v_x_1170_);
v___x_1198_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v_snd_1200_; lean_object* v_fst_1201_; lean_object* v_u_1202_; lean_object* v_00_u03c3s_1203_; lean_object* v_hyps_1204_; lean_object* v_target_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___y_1209_; lean_object* v___x_1210_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v_snd_1200_ = lean_ctor_get(v_a_1199_, 1);
lean_inc(v_snd_1200_);
v_fst_1201_ = lean_ctor_get(v_a_1199_, 0);
lean_inc_n(v_fst_1201_, 2);
lean_dec(v_a_1199_);
v_u_1202_ = lean_ctor_get(v_snd_1200_, 0);
lean_inc(v_u_1202_);
v_00_u03c3s_1203_ = lean_ctor_get(v_snd_1200_, 1);
lean_inc_ref(v_00_u03c3s_1203_);
v_hyps_1204_ = lean_ctor_get(v_snd_1200_, 2);
lean_inc_ref(v_hyps_1204_);
v_target_1205_ = lean_ctor_get(v_snd_1200_, 3);
lean_inc_ref(v_target_1205_);
v___x_1206_ = l_Lean_Syntax_getId(v___x_1185_);
v___x_1207_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_1200_, v___x_1206_);
v___x_1208_ = lean_box(v___x_1182_);
v___y_1209_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___boxed), 21, 12);
lean_closure_set(v___y_1209_, 0, v___x_1207_);
lean_closure_set(v___y_1209_, 1, v_u_1202_);
lean_closure_set(v___y_1209_, 2, v___x_1206_);
lean_closure_set(v___y_1209_, 3, v___x_1185_);
lean_closure_set(v___y_1209_, 4, v_00_u03c3s_1203_);
lean_closure_set(v___y_1209_, 5, v___x_1208_);
lean_closure_set(v___y_1209_, 6, v_hyps_1204_);
lean_closure_set(v___y_1209_, 7, v___x_1197_);
lean_closure_set(v___y_1209_, 8, v_target_1205_);
lean_closure_set(v___y_1209_, 9, v___x_1180_);
lean_closure_set(v___y_1209_, 10, v_fst_1201_);
lean_closure_set(v___y_1209_, 11, v_ty_x3f_1187_);
v___x_1210_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_1201_, v___y_1209_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
return v___x_1210_;
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec(v___x_1197_);
lean_dec(v_ty_x3f_1187_);
lean_dec(v___x_1185_);
v_a_1211_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1198_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1198_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1170_ = stack[0].m_obj;
lean_object* v_a_1171_ = stack[1].m_obj;
lean_object* v_a_1172_ = stack[2].m_obj;
lean_object* v_a_1173_ = stack[3].m_obj;
lean_object* v_a_1174_ = stack[4].m_obj;
lean_object* v_a_1175_ = stack[5].m_obj;
lean_object* v_a_1176_ = stack[6].m_obj;
lean_object* v_a_1177_ = stack[7].m_obj;
lean_object* v_a_1178_ = stack[8].m_obj;
lean_object* v_res_1227_;
v_res_1227_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace(v_x_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
stack->m_obj
 = v_res_1227_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___boxed(lean_object* v_x_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace(v_x_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
return v_res_1238_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1(){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1248_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1249_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1));
v___x_1250_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1));
v___x_1251_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___boxed), 10, 0);
v___x_1252_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1248_, v___x_1249_, v___x_1250_, v___x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1253_;
v_res_1253_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1();
stack->m_obj
 = v_res_1253_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___boxed(lean_object* v_a_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1();
return v_res_1255_;
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
