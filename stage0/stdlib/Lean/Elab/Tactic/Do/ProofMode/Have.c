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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2;
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
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabMDup"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 237, 91, 55, 155, 74, 73, 223)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabMHave"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 11, 27, 98, 145, 254, 24, 229)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabMReplace"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 34, 48, 214, 220, 188, 132, 60)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___boxed(lean_object*);
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
lean_object* v___x_33_; lean_object* v_ngen_34_; lean_object* v_namePrefix_35_; lean_object* v_idx_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_65_; 
v___x_33_ = lean_st_ref_get(v___y_31_);
v_ngen_34_ = lean_ctor_get(v___x_33_, 2);
lean_inc_ref(v_ngen_34_);
lean_dec(v___x_33_);
v_namePrefix_35_ = lean_ctor_get(v_ngen_34_, 0);
v_idx_36_ = lean_ctor_get(v_ngen_34_, 1);
v_isSharedCheck_65_ = !lean_is_exclusive(v_ngen_34_);
if (v_isSharedCheck_65_ == 0)
{
v___x_38_ = v_ngen_34_;
v_isShared_39_ = v_isSharedCheck_65_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_idx_36_);
lean_inc(v_namePrefix_35_);
lean_dec(v_ngen_34_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_65_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_40_; lean_object* v_env_41_; lean_object* v_nextMacroScope_42_; lean_object* v_auxDeclNGen_43_; lean_object* v_traceState_44_; lean_object* v_cache_45_; lean_object* v_messages_46_; lean_object* v_infoState_47_; lean_object* v_snapshotTasks_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_63_; 
v___x_40_ = lean_st_ref_take(v___y_31_);
v_env_41_ = lean_ctor_get(v___x_40_, 0);
v_nextMacroScope_42_ = lean_ctor_get(v___x_40_, 1);
v_auxDeclNGen_43_ = lean_ctor_get(v___x_40_, 3);
v_traceState_44_ = lean_ctor_get(v___x_40_, 4);
v_cache_45_ = lean_ctor_get(v___x_40_, 5);
v_messages_46_ = lean_ctor_get(v___x_40_, 6);
v_infoState_47_ = lean_ctor_get(v___x_40_, 7);
v_snapshotTasks_48_ = lean_ctor_get(v___x_40_, 8);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_63_ == 0)
{
lean_object* v_unused_64_; 
v_unused_64_ = lean_ctor_get(v___x_40_, 2);
lean_dec(v_unused_64_);
v___x_50_ = v___x_40_;
v_isShared_51_ = v_isSharedCheck_63_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_snapshotTasks_48_);
lean_inc(v_infoState_47_);
lean_inc(v_messages_46_);
lean_inc(v_cache_45_);
lean_inc(v_traceState_44_);
lean_inc(v_auxDeclNGen_43_);
lean_inc(v_nextMacroScope_42_);
lean_inc(v_env_41_);
lean_dec(v___x_40_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_63_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v_r_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_56_; 
lean_inc(v_idx_36_);
lean_inc(v_namePrefix_35_);
v_r_52_ = l_Lean_Name_num___override(v_namePrefix_35_, v_idx_36_);
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = lean_nat_add(v_idx_36_, v___x_53_);
lean_dec(v_idx_36_);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 1, v___x_54_);
v___x_56_ = v___x_38_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_namePrefix_35_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v___x_54_);
v___x_56_ = v_reuseFailAlloc_62_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
lean_object* v___x_58_; 
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 2, v___x_56_);
v___x_58_ = v___x_50_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_env_41_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v_nextMacroScope_42_);
lean_ctor_set(v_reuseFailAlloc_61_, 2, v___x_56_);
lean_ctor_set(v_reuseFailAlloc_61_, 3, v_auxDeclNGen_43_);
lean_ctor_set(v_reuseFailAlloc_61_, 4, v_traceState_44_);
lean_ctor_set(v_reuseFailAlloc_61_, 5, v_cache_45_);
lean_ctor_set(v_reuseFailAlloc_61_, 6, v_messages_46_);
lean_ctor_set(v_reuseFailAlloc_61_, 7, v_infoState_47_);
lean_ctor_set(v_reuseFailAlloc_61_, 8, v_snapshotTasks_48_);
v___x_58_ = v_reuseFailAlloc_61_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_st_ref_set(v___y_31_, v___x_58_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v_r_52_);
return v___x_60_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg___boxed(lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_66_);
lean_dec(v___y_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1(lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_76_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___boxed(lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1(v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0(lean_object* v_x_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_apply_9(v_x_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, lean_box(0));
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0___boxed(lean_object* v_x_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0(v_x_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(lean_object* v_mvarId_111_, lean_object* v_x_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v___f_122_; lean_object* v___x_123_; 
v___f_122_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_122_, 0, v_x_112_);
lean_closure_set(v___f_122_, 1, v___y_113_);
lean_closure_set(v___f_122_, 2, v___y_114_);
lean_closure_set(v___f_122_, 3, v___y_115_);
lean_closure_set(v___f_122_, 4, v___y_116_);
v___x_123_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_111_, v___f_122_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
if (lean_obj_tag(v___x_123_) == 0)
{
return v___x_123_;
}
else
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
v_a_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___boxed(lean_object* v_mvarId_132_, lean_object* v_x_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_mvarId_132_, v_x_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4(lean_object* v_00_u03b1_144_, lean_object* v_mvarId_145_, lean_object* v_x_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_mvarId_145_, v_x_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___boxed(lean_object* v_00_u03b1_157_, lean_object* v_mvarId_158_, lean_object* v_x_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4(v_00_u03b1_157_, v_mvarId_158_, v_x_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_x_172_, lean_object* v_x_173_){
_start:
{
lean_object* v_ks_174_; lean_object* v_vs_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_199_; 
v_ks_174_ = lean_ctor_get(v_x_170_, 0);
v_vs_175_ = lean_ctor_get(v_x_170_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_x_170_);
if (v_isSharedCheck_199_ == 0)
{
v___x_177_ = v_x_170_;
v_isShared_178_ = v_isSharedCheck_199_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_vs_175_);
lean_inc(v_ks_174_);
lean_dec(v_x_170_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_199_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_array_get_size(v_ks_174_);
v___x_180_ = lean_nat_dec_lt(v_x_171_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; 
lean_dec(v_x_171_);
v___x_181_ = lean_array_push(v_ks_174_, v_x_172_);
v___x_182_ = lean_array_push(v_vs_175_, v_x_173_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v___x_182_);
lean_ctor_set(v___x_177_, 0, v___x_181_);
v___x_184_ = v___x_177_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
else
{
lean_object* v_k_x27_186_; uint8_t v___x_187_; 
v_k_x27_186_ = lean_array_fget_borrowed(v_ks_174_, v_x_171_);
v___x_187_ = l_Lean_instBEqMVarId_beq(v_x_172_, v_k_x27_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_189_; 
if (v_isShared_178_ == 0)
{
v___x_189_ = v___x_177_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_ks_174_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_vs_175_);
v___x_189_ = v_reuseFailAlloc_193_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = lean_nat_add(v_x_171_, v___x_190_);
lean_dec(v_x_171_);
v_x_170_ = v___x_189_;
v_x_171_ = v___x_191_;
goto _start;
}
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_194_ = lean_array_fset(v_ks_174_, v_x_171_, v_x_172_);
v___x_195_ = lean_array_fset(v_vs_175_, v_x_171_, v_x_173_);
lean_dec(v_x_171_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v___x_195_);
lean_ctor_set(v___x_177_, 0, v___x_194_);
v___x_197_ = v___x_177_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(lean_object* v_n_200_, lean_object* v_k_201_, lean_object* v_v_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_unsigned_to_nat(0u);
v___x_204_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_n_200_, v___x_203_, v_k_201_, v_v_202_);
return v___x_204_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_205_; size_t v___x_206_; size_t v___x_207_; 
v___x_205_ = ((size_t)5ULL);
v___x_206_ = ((size_t)1ULL);
v___x_207_ = lean_usize_shift_left(v___x_206_, v___x_205_);
return v___x_207_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_208_; size_t v___x_209_; size_t v___x_210_; 
v___x_208_ = ((size_t)1ULL);
v___x_209_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_210_ = lean_usize_sub(v___x_209_, v___x_208_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(lean_object* v_x_212_, size_t v_x_213_, size_t v_x_214_, lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
if (lean_obj_tag(v_x_212_) == 0)
{
lean_object* v_es_217_; size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; lean_object* v_j_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_es_217_ = lean_ctor_get(v_x_212_, 0);
v___x_218_ = ((size_t)5ULL);
v___x_219_ = ((size_t)1ULL);
v___x_220_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1);
v___x_221_ = lean_usize_land(v_x_213_, v___x_220_);
v_j_222_ = lean_usize_to_nat(v___x_221_);
v___x_223_ = lean_array_get_size(v_es_217_);
v___x_224_ = lean_nat_dec_lt(v_j_222_, v___x_223_);
if (v___x_224_ == 0)
{
lean_dec(v_j_222_);
lean_dec(v_x_216_);
lean_dec(v_x_215_);
return v_x_212_;
}
else
{
lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_261_; 
lean_inc_ref(v_es_217_);
v_isSharedCheck_261_ = !lean_is_exclusive(v_x_212_);
if (v_isSharedCheck_261_ == 0)
{
lean_object* v_unused_262_; 
v_unused_262_ = lean_ctor_get(v_x_212_, 0);
lean_dec(v_unused_262_);
v___x_226_ = v_x_212_;
v_isShared_227_ = v_isSharedCheck_261_;
goto v_resetjp_225_;
}
else
{
lean_dec(v_x_212_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_261_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v_v_228_; lean_object* v___x_229_; lean_object* v_xs_x27_230_; lean_object* v___y_232_; 
v_v_228_ = lean_array_fget(v_es_217_, v_j_222_);
v___x_229_ = lean_box(0);
v_xs_x27_230_ = lean_array_fset(v_es_217_, v_j_222_, v___x_229_);
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
v___x_242_ = l_Lean_instBEqMVarId_beq(v_x_215_, v_key_237_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_del_object(v___x_240_);
v___x_243_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_237_, v_val_238_, v_x_215_, v_x_216_);
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
lean_ctor_set(v___x_240_, 1, v_x_216_);
lean_ctor_set(v___x_240_, 0, v_x_215_);
v___x_246_ = v___x_240_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_x_215_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_x_216_);
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
lean_object* v_node_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_259_; 
v_node_249_ = lean_ctor_get(v_v_228_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v_v_228_);
if (v_isSharedCheck_259_ == 0)
{
v___x_251_ = v_v_228_;
v_isShared_252_ = v_isSharedCheck_259_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_node_249_);
lean_dec(v_v_228_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_259_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
size_t v___x_253_; size_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_253_ = lean_usize_shift_right(v_x_213_, v___x_218_);
v___x_254_ = lean_usize_add(v_x_214_, v___x_219_);
v___x_255_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_node_249_, v___x_253_, v___x_254_, v_x_215_, v_x_216_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___x_255_);
v___x_257_ = v___x_251_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
v___y_232_ = v___x_257_;
goto v___jp_231_;
}
}
}
default: 
{
lean_object* v___x_260_; 
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v_x_215_);
lean_ctor_set(v___x_260_, 1, v_x_216_);
v___y_232_ = v___x_260_;
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
lean_object* v_ks_263_; lean_object* v_vs_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_284_; 
v_ks_263_ = lean_ctor_get(v_x_212_, 0);
v_vs_264_ = lean_ctor_get(v_x_212_, 1);
v_isSharedCheck_284_ = !lean_is_exclusive(v_x_212_);
if (v_isSharedCheck_284_ == 0)
{
v___x_266_ = v_x_212_;
v_isShared_267_ = v_isSharedCheck_284_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_vs_264_);
lean_inc(v_ks_263_);
lean_dec(v_x_212_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_284_;
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
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_ks_263_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_vs_264_);
v___x_269_ = v_reuseFailAlloc_283_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v_newNode_270_; uint8_t v___y_272_; size_t v___x_278_; uint8_t v___x_279_; 
v_newNode_270_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(v___x_269_, v_x_215_, v_x_216_);
v___x_278_ = ((size_t)7ULL);
v___x_279_ = lean_usize_dec_le(v___x_278_, v_x_214_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_280_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_270_);
v___x_281_ = lean_unsigned_to_nat(4u);
v___x_282_ = lean_nat_dec_lt(v___x_280_, v___x_281_);
lean_dec(v___x_280_);
v___y_272_ = v___x_282_;
goto v___jp_271_;
}
else
{
v___y_272_ = v___x_279_;
goto v___jp_271_;
}
v___jp_271_:
{
if (v___y_272_ == 0)
{
lean_object* v_ks_273_; lean_object* v_vs_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_ks_273_ = lean_ctor_get(v_newNode_270_, 0);
lean_inc_ref(v_ks_273_);
v_vs_274_ = lean_ctor_get(v_newNode_270_, 1);
lean_inc_ref(v_vs_274_);
lean_dec_ref(v_newNode_270_);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2);
v___x_277_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_x_214_, v_ks_273_, v_vs_274_, v___x_275_, v___x_276_);
lean_dec_ref(v_vs_274_);
lean_dec_ref(v_ks_273_);
return v___x_277_;
}
else
{
return v_newNode_270_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(size_t v_depth_285_, lean_object* v_keys_286_, lean_object* v_vals_287_, lean_object* v_i_288_, lean_object* v_entries_289_){
_start:
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_array_get_size(v_keys_286_);
v___x_291_ = lean_nat_dec_lt(v_i_288_, v___x_290_);
if (v___x_291_ == 0)
{
lean_dec(v_i_288_);
return v_entries_289_;
}
else
{
lean_object* v_k_292_; lean_object* v_v_293_; uint64_t v___x_294_; size_t v_h_295_; size_t v___x_296_; lean_object* v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v_h_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_k_292_ = lean_array_fget_borrowed(v_keys_286_, v_i_288_);
v_v_293_ = lean_array_fget_borrowed(v_vals_287_, v_i_288_);
v___x_294_ = l_Lean_instHashableMVarId_hash(v_k_292_);
v_h_295_ = lean_uint64_to_usize(v___x_294_);
v___x_296_ = ((size_t)5ULL);
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_sub(v_depth_285_, v___x_298_);
v___x_300_ = lean_usize_mul(v___x_296_, v___x_299_);
v_h_301_ = lean_usize_shift_right(v_h_295_, v___x_300_);
v___x_302_ = lean_nat_add(v_i_288_, v___x_297_);
lean_dec(v_i_288_);
lean_inc(v_v_293_);
lean_inc(v_k_292_);
v___x_303_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_entries_289_, v_h_301_, v_depth_285_, v_k_292_, v_v_293_);
v_i_288_ = v___x_302_;
v_entries_289_ = v___x_303_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_305_, lean_object* v_keys_306_, lean_object* v_vals_307_, lean_object* v_i_308_, lean_object* v_entries_309_){
_start:
{
size_t v_depth_boxed_310_; lean_object* v_res_311_; 
v_depth_boxed_310_ = lean_unbox_usize(v_depth_305_);
lean_dec(v_depth_305_);
v_res_311_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_boxed_310_, v_keys_306_, v_vals_307_, v_i_308_, v_entries_309_);
lean_dec_ref(v_vals_307_);
lean_dec_ref(v_keys_306_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
size_t v_x_7792__boxed_317_; size_t v_x_7793__boxed_318_; lean_object* v_res_319_; 
v_x_7792__boxed_317_ = lean_unbox_usize(v_x_313_);
lean_dec(v_x_313_);
v_x_7793__boxed_318_ = lean_unbox_usize(v_x_314_);
lean_dec(v_x_314_);
v_res_319_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_312_, v_x_7792__boxed_317_, v_x_7793__boxed_318_, v_x_315_, v_x_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
uint64_t v___x_323_; size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; 
v___x_323_ = l_Lean_instHashableMVarId_hash(v_x_321_);
v___x_324_ = lean_uint64_to_usize(v___x_323_);
v___x_325_ = ((size_t)1ULL);
v___x_326_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_320_, v___x_324_, v___x_325_, v_x_321_, v_x_322_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(lean_object* v_mvarId_327_, lean_object* v_val_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___x_331_; lean_object* v_mctx_332_; lean_object* v_cache_333_; lean_object* v_zetaDeltaFVarIds_334_; lean_object* v_postponed_335_; lean_object* v_diag_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_363_; 
v___x_331_ = lean_st_ref_take(v___y_329_);
v_mctx_332_ = lean_ctor_get(v___x_331_, 0);
v_cache_333_ = lean_ctor_get(v___x_331_, 1);
v_zetaDeltaFVarIds_334_ = lean_ctor_get(v___x_331_, 2);
v_postponed_335_ = lean_ctor_get(v___x_331_, 3);
v_diag_336_ = lean_ctor_get(v___x_331_, 4);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_363_ == 0)
{
v___x_338_ = v___x_331_;
v_isShared_339_ = v_isSharedCheck_363_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_diag_336_);
lean_inc(v_postponed_335_);
lean_inc(v_zetaDeltaFVarIds_334_);
lean_inc(v_cache_333_);
lean_inc(v_mctx_332_);
lean_dec(v___x_331_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_363_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v_depth_340_; lean_object* v_levelAssignDepth_341_; lean_object* v_mvarCounter_342_; lean_object* v_lDepth_343_; lean_object* v_decls_344_; lean_object* v_userNames_345_; lean_object* v_lAssignment_346_; lean_object* v_eAssignment_347_; lean_object* v_dAssignment_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_362_; 
v_depth_340_ = lean_ctor_get(v_mctx_332_, 0);
v_levelAssignDepth_341_ = lean_ctor_get(v_mctx_332_, 1);
v_mvarCounter_342_ = lean_ctor_get(v_mctx_332_, 2);
v_lDepth_343_ = lean_ctor_get(v_mctx_332_, 3);
v_decls_344_ = lean_ctor_get(v_mctx_332_, 4);
v_userNames_345_ = lean_ctor_get(v_mctx_332_, 5);
v_lAssignment_346_ = lean_ctor_get(v_mctx_332_, 6);
v_eAssignment_347_ = lean_ctor_get(v_mctx_332_, 7);
v_dAssignment_348_ = lean_ctor_get(v_mctx_332_, 8);
v_isSharedCheck_362_ = !lean_is_exclusive(v_mctx_332_);
if (v_isSharedCheck_362_ == 0)
{
v___x_350_ = v_mctx_332_;
v_isShared_351_ = v_isSharedCheck_362_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_dAssignment_348_);
lean_inc(v_eAssignment_347_);
lean_inc(v_lAssignment_346_);
lean_inc(v_userNames_345_);
lean_inc(v_decls_344_);
lean_inc(v_lDepth_343_);
lean_inc(v_mvarCounter_342_);
lean_inc(v_levelAssignDepth_341_);
lean_inc(v_depth_340_);
lean_dec(v_mctx_332_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_362_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(v_eAssignment_347_, v_mvarId_327_, v_val_328_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 7, v___x_352_);
v___x_354_ = v___x_350_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_depth_340_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_levelAssignDepth_341_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v_mvarCounter_342_);
lean_ctor_set(v_reuseFailAlloc_361_, 3, v_lDepth_343_);
lean_ctor_set(v_reuseFailAlloc_361_, 4, v_decls_344_);
lean_ctor_set(v_reuseFailAlloc_361_, 5, v_userNames_345_);
lean_ctor_set(v_reuseFailAlloc_361_, 6, v_lAssignment_346_);
lean_ctor_set(v_reuseFailAlloc_361_, 7, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_361_, 8, v_dAssignment_348_);
v___x_354_ = v_reuseFailAlloc_361_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_356_; 
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_354_);
v___x_356_ = v___x_338_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_cache_333_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_zetaDeltaFVarIds_334_);
lean_ctor_set(v_reuseFailAlloc_360_, 3, v_postponed_335_);
lean_ctor_set(v_reuseFailAlloc_360_, 4, v_diag_336_);
v___x_356_ = v_reuseFailAlloc_360_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_st_ref_set(v___y_329_, v___x_356_);
v___x_358_ = lean_box(0);
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg___boxed(lean_object* v_mvarId_364_, lean_object* v_val_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_mvarId_364_, v_val_365_, v___y_366_);
lean_dec(v___y_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(lean_object* v_msgData_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; lean_object* v_env_376_; lean_object* v___x_377_; lean_object* v_mctx_378_; lean_object* v_lctx_379_; lean_object* v_options_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_375_ = lean_st_ref_get(v___y_373_);
v_env_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc_ref(v_env_376_);
lean_dec(v___x_375_);
v___x_377_ = lean_st_ref_get(v___y_371_);
v_mctx_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc_ref(v_mctx_378_);
lean_dec(v___x_377_);
v_lctx_379_ = lean_ctor_get(v___y_370_, 2);
v_options_380_ = lean_ctor_get(v___y_372_, 2);
lean_inc_ref(v_options_380_);
lean_inc_ref(v_lctx_379_);
v___x_381_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_381_, 0, v_env_376_);
lean_ctor_set(v___x_381_, 1, v_mctx_378_);
lean_ctor_set(v___x_381_, 2, v_lctx_379_);
lean_ctor_set(v___x_381_, 3, v_options_380_);
v___x_382_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v_msgData_369_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4___boxed(lean_object* v_msgData_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(v_msgData_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_ref_397_; lean_object* v___x_398_; lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_407_; 
v_ref_397_ = lean_ctor_get(v___y_394_, 5);
v___x_398_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(v_msg_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_407_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_407_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_407_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_405_; 
lean_inc(v_ref_397_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v_ref_397_);
lean_ctor_set(v___x_403_, 1, v_a_399_);
if (v_isShared_402_ == 0)
{
lean_ctor_set_tag(v___x_401_, 1);
lean_ctor_set(v___x_401_, 0, v___x_403_);
v___x_405_ = v___x_401_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg___boxed(lean_object* v_msg_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v_msg_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_414_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__5));
v___x_422_ = l_Lean_stringToMessageData(v___x_421_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__7));
v___x_425_ = l_Lean_stringToMessageData(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0(lean_object* v___x_426_, lean_object* v_snd_427_, lean_object* v___x_428_, lean_object* v___x_429_, uint8_t v___x_430_, lean_object* v___x_431_, lean_object* v_fst_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
if (lean_obj_tag(v___x_426_) == 1)
{
lean_object* v_val_442_; lean_object* v___x_443_; lean_object* v_a_444_; lean_object* v_focusHyp_445_; lean_object* v_restHyps_446_; lean_object* v_proof_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_496_; 
v_val_442_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_val_442_);
lean_dec_ref(v___x_426_);
v___x_443_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_440_);
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref(v___x_443_);
v_focusHyp_445_ = lean_ctor_get(v_val_442_, 0);
v_restHyps_446_ = lean_ctor_get(v_val_442_, 1);
v_proof_447_ = lean_ctor_get(v_val_442_, 2);
v_isSharedCheck_496_ = !lean_is_exclusive(v_val_442_);
if (v_isSharedCheck_496_ == 0)
{
v___x_449_ = v_val_442_;
v_isShared_450_ = v_isSharedCheck_496_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_proof_447_);
lean_inc(v_restHyps_446_);
lean_inc(v_focusHyp_445_);
lean_dec(v_val_442_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_496_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v_u_451_; lean_object* v_00_u03c3s_452_; lean_object* v_hyps_453_; lean_object* v_target_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_495_; 
v_u_451_ = lean_ctor_get(v_snd_427_, 0);
v_00_u03c3s_452_ = lean_ctor_get(v_snd_427_, 1);
v_hyps_453_ = lean_ctor_get(v_snd_427_, 2);
v_target_454_ = lean_ctor_get(v_snd_427_, 3);
v_isSharedCheck_495_ = !lean_is_exclusive(v_snd_427_);
if (v_isSharedCheck_495_ == 0)
{
v___x_456_ = v_snd_427_;
v_isShared_457_ = v_isSharedCheck_495_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_target_454_);
lean_inc(v_hyps_453_);
lean_inc(v_00_u03c3s_452_);
lean_inc(v_u_451_);
lean_dec(v_snd_427_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_495_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_458_ = l_Lean_Syntax_getId(v___x_428_);
v___x_459_ = l_Lean_Expr_consumeMData(v_focusHyp_445_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 2, v___x_459_);
lean_ctor_set(v___x_449_, 1, v_a_444_);
lean_ctor_set(v___x_449_, 0, v___x_458_);
v___x_461_ = v___x_449_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_a_444_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v___x_459_);
v___x_461_ = v_reuseFailAlloc_494_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; 
lean_inc(v___y_440_);
lean_inc_ref(v___y_439_);
lean_inc(v___y_438_);
lean_inc_ref(v___y_437_);
lean_inc_ref(v___x_461_);
lean_inc_ref(v_00_u03c3s_452_);
v___x_462_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v___x_429_, v_00_u03c3s_452_, v___x_461_, v___x_430_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
lean_dec_ref(v___x_462_);
v___x_463_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_461_);
lean_inc_ref(v_hyps_453_);
lean_inc_ref(v_00_u03c3s_452_);
lean_inc(v_u_451_);
v___x_464_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_451_, v_00_u03c3s_452_, v_hyps_453_, v___x_463_);
lean_inc_ref(v_target_454_);
lean_inc_ref(v_00_u03c3s_452_);
lean_inc(v_u_451_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 2, v___x_464_);
v___x_466_ = v___x_456_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_u_451_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_00_u03c3s_452_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v_target_454_);
v___x_466_ = v_reuseFailAlloc_493_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_466_);
v___x_468_ = lean_box(0);
lean_inc_ref(v___y_437_);
v___x_469_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_467_, v___x_468_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref(v___x_469_);
v___x_471_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0));
v___x_472_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1));
v___x_473_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2));
v___x_474_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3));
v___x_475_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__4));
v___x_476_ = l_Lean_Name_mkStr6(v___x_471_, v___x_472_, v___x_473_, v___x_431_, v___x_474_, v___x_475_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v_u_451_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = l_Lean_mkConst(v___x_476_, v___x_478_);
lean_inc(v_a_470_);
v___x_480_ = l_Lean_mkApp7(v___x_479_, v_00_u03c3s_452_, v_hyps_453_, v_restHyps_446_, v_focusHyp_445_, v_target_454_, v_proof_447_, v_a_470_);
v___x_481_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_432_, v___x_480_, v___y_438_);
lean_dec_ref(v___x_481_);
v___x_482_ = l_Lean_Expr_mvarId_x21(v_a_470_);
lean_dec(v_a_470_);
v___x_483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___x_477_);
v___x_484_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_483_, v___y_434_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v___x_484_;
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref(v_target_454_);
lean_dec_ref(v_hyps_453_);
lean_dec_ref(v_00_u03c3s_452_);
lean_dec(v_u_451_);
lean_dec_ref(v_proof_447_);
lean_dec_ref(v_restHyps_446_);
lean_dec_ref(v_focusHyp_445_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v_fst_432_);
lean_dec_ref(v___x_431_);
v_a_485_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_469_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_469_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_461_);
lean_del_object(v___x_456_);
lean_dec_ref(v_target_454_);
lean_dec_ref(v_hyps_453_);
lean_dec_ref(v_00_u03c3s_452_);
lean_dec(v_u_451_);
lean_dec_ref(v_proof_447_);
lean_dec_ref(v_restHyps_446_);
lean_dec_ref(v_focusHyp_445_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v_fst_432_);
lean_dec_ref(v___x_431_);
return v___x_462_;
}
}
}
}
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
lean_dec(v_fst_432_);
lean_dec_ref(v___x_431_);
lean_dec_ref(v_snd_427_);
lean_dec(v___x_426_);
v___x_497_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6);
v___x_498_ = l_Lean_MessageData_ofSyntax(v___x_429_);
v___x_499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8);
v___x_501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v___x_501_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___boxed(lean_object* v___x_503_, lean_object* v_snd_504_, lean_object* v___x_505_, lean_object* v___x_506_, lean_object* v___x_507_, lean_object* v___x_508_, lean_object* v_fst_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
uint8_t v___x_8098__boxed_519_; lean_object* v_res_520_; 
v___x_8098__boxed_519_ = lean_unbox(v___x_507_);
v_res_520_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0(v___x_503_, v_snd_504_, v___x_505_, v___x_506_, v___x_8098__boxed_519_, v___x_508_, v_fst_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___x_505_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup(lean_object* v_x_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_543_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2));
v___x_544_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4));
lean_inc(v_x_533_);
v___x_545_ = l_Lean_Syntax_isOfKind(v_x_533_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_x_533_);
v___x_546_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = l_Lean_Syntax_getArg(v_x_533_, v___x_547_);
v___x_549_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__6));
lean_inc(v___x_548_);
v___x_550_ = l_Lean_Syntax_isOfKind(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
lean_dec(v___x_548_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_x_533_);
v___x_551_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_551_;
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_552_ = lean_unsigned_to_nat(3u);
v___x_553_ = l_Lean_Syntax_getArg(v_x_533_, v___x_552_);
lean_dec(v_x_533_);
lean_inc(v___x_553_);
v___x_554_ = l_Lean_Syntax_isOfKind(v___x_553_, v___x_549_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; 
lean_dec(v___x_553_);
lean_dec(v___x_548_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
v___x_555_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_555_;
}
else
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v_fst_558_; lean_object* v_snd_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___y_563_; lean_object* v___x_564_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref(v___x_556_);
v_fst_558_ = lean_ctor_get(v_a_557_, 0);
lean_inc(v_fst_558_);
v_snd_559_ = lean_ctor_get(v_a_557_, 1);
lean_inc(v_snd_559_);
lean_dec(v_a_557_);
v___x_560_ = l_Lean_Syntax_getId(v___x_548_);
lean_inc(v_snd_559_);
v___x_561_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_559_, v___x_560_);
lean_dec(v___x_560_);
v___x_562_ = lean_box(v___x_554_);
lean_inc(v_fst_558_);
v___y_563_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___boxed), 16, 7);
lean_closure_set(v___y_563_, 0, v___x_561_);
lean_closure_set(v___y_563_, 1, v_snd_559_);
lean_closure_set(v___y_563_, 2, v___x_553_);
lean_closure_set(v___y_563_, 3, v___x_548_);
lean_closure_set(v___y_563_, 4, v___x_562_);
lean_closure_set(v___y_563_, 5, v___x_543_);
lean_closure_set(v___y_563_, 6, v_fst_558_);
v___x_564_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_558_, v___y_563_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
return v___x_564_;
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec(v___x_553_);
lean_dec(v___x_548_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
v_a_565_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_556_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_556_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___boxed(lean_object* v_x_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup(v_x_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2(lean_object* v_mvarId_584_, lean_object* v_val_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_mvarId_584_, v_val_585_, v___y_591_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___boxed(lean_object* v_mvarId_596_, lean_object* v_val_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2(v_mvarId_596_, v_val_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3(lean_object* v_00_u03b1_608_, lean_object* v_msg_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v_msg_609_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___boxed(lean_object* v_00_u03b1_620_, lean_object* v_msg_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3(v_00_u03b1_620_, v_msg_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2(lean_object* v_00_u03b2_632_, lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(v_x_633_, v_x_634_, v_x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_637_, lean_object* v_x_638_, size_t v_x_639_, size_t v_x_640_, lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_638_, v_x_639_, v_x_640_, v_x_641_, v_x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_644_, lean_object* v_x_645_, lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
size_t v_x_8459__boxed_650_; size_t v_x_8460__boxed_651_; lean_object* v_res_652_; 
v_x_8459__boxed_650_ = lean_unbox_usize(v_x_646_);
lean_dec(v_x_646_);
v_x_8460__boxed_651_ = lean_unbox_usize(v_x_647_);
lean_dec(v_x_647_);
v_res_652_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4(v_00_u03b2_644_, v_x_645_, v_x_8459__boxed_650_, v_x_8460__boxed_651_, v_x_648_, v_x_649_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_653_, lean_object* v_n_654_, lean_object* v_k_655_, lean_object* v_v_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(v_n_654_, v_k_655_, v_v_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_658_, size_t v_depth_659_, lean_object* v_keys_660_, lean_object* v_vals_661_, lean_object* v_heq_662_, lean_object* v_i_663_, lean_object* v_entries_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_659_, v_keys_660_, v_vals_661_, v_i_663_, v_entries_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_666_, lean_object* v_depth_667_, lean_object* v_keys_668_, lean_object* v_vals_669_, lean_object* v_heq_670_, lean_object* v_i_671_, lean_object* v_entries_672_){
_start:
{
size_t v_depth_boxed_673_; lean_object* v_res_674_; 
v_depth_boxed_673_ = lean_unbox_usize(v_depth_667_);
lean_dec(v_depth_667_);
v_res_674_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_666_, v_depth_boxed_673_, v_keys_668_, v_vals_669_, v_heq_670_, v_i_671_, v_entries_672_);
lean_dec_ref(v_vals_669_);
lean_dec_ref(v_keys_668_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_675_, lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_676_, v_x_677_, v_x_678_, v_x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1(){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_692_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_693_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4));
v___x_694_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3));
v___x_695_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___boxed), 10, 0);
v___x_696_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_692_, v___x_693_, v___x_694_, v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___boxed(lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1();
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0(lean_object* v___x_700_, lean_object* v_00_u03c3s_701_, uint8_t v___x_702_, lean_object* v_u_703_, lean_object* v_hyps_704_, lean_object* v___x_705_, lean_object* v_target_706_, lean_object* v___x_707_, lean_object* v___x_708_, lean_object* v___x_709_, lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v_fst_712_, lean_object* v_H_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_723_; lean_object* v_a_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_723_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_721_);
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref(v___x_723_);
v___x_725_ = l_Lean_Syntax_getId(v___x_700_);
v___x_726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v_a_724_);
lean_ctor_set(v___x_726_, 2, v_H_713_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc_ref(v___x_726_);
lean_inc_ref(v_00_u03c3s_701_);
v___x_727_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v___x_700_, v_00_u03c3s_701_, v___x_726_, v___x_702_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_780_; 
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v___x_727_, 0);
lean_dec(v_unused_781_);
v___x_729_ = v___x_727_;
v_isShared_730_ = v_isSharedCheck_780_;
goto v_resetjp_728_;
}
else
{
lean_dec(v___x_727_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_780_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v_fst_733_; lean_object* v_snd_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_779_; 
v___x_731_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_726_);
lean_inc_ref(v___x_731_);
lean_inc_ref(v_hyps_704_);
lean_inc_ref(v_00_u03c3s_701_);
lean_inc(v_u_703_);
v___x_732_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_703_, v_00_u03c3s_701_, v_hyps_704_, v___x_731_);
v_fst_733_ = lean_ctor_get(v___x_732_, 0);
v_snd_734_ = lean_ctor_get(v___x_732_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_779_ == 0)
{
v___x_736_ = v___x_732_;
v_isShared_737_ = v_isSharedCheck_779_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_snd_734_);
lean_inc(v_fst_733_);
lean_dec(v___x_732_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_779_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
lean_inc_ref(v___x_731_);
lean_inc_ref(v_hyps_704_);
lean_inc_ref(v_00_u03c3s_701_);
lean_inc(v_u_703_);
v___x_738_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_738_, 0, v_u_703_);
lean_ctor_set(v___x_738_, 1, v_00_u03c3s_701_);
lean_ctor_set(v___x_738_, 2, v_hyps_704_);
lean_ctor_set(v___x_738_, 3, v___x_731_);
v___x_739_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_738_);
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 1);
lean_ctor_set(v___x_729_, 0, v___x_739_);
v___x_741_ = v___x_729_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_778_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
uint8_t v___x_742_; lean_object* v___x_743_; 
v___x_742_ = 0;
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_715_);
v___x_743_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v___x_705_, v___x_741_, v___x_742_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref(v___x_743_);
lean_inc_ref(v_target_706_);
lean_inc(v_fst_733_);
lean_inc_ref(v_00_u03c3s_701_);
v___x_745_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_745_, 0, v_u_703_);
lean_ctor_set(v___x_745_, 1, v_00_u03c3s_701_);
lean_ctor_set(v___x_745_, 2, v_fst_733_);
lean_ctor_set(v___x_745_, 3, v_target_706_);
v___x_746_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_745_);
v___x_747_ = lean_box(0);
lean_inc_ref(v___y_718_);
v___x_748_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_746_, v___x_747_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref(v___x_748_);
v___x_750_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3));
v___x_751_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___closed__0));
v___x_752_ = l_Lean_Name_mkStr6(v___x_707_, v___x_708_, v___x_709_, v___x_710_, v___x_750_, v___x_751_);
v___x_753_ = l_Lean_mkConst(v___x_752_, v___x_711_);
lean_inc(v_a_749_);
v___x_754_ = l_Lean_mkApp8(v___x_753_, v_00_u03c3s_701_, v_hyps_704_, v___x_731_, v_fst_733_, v_target_706_, v_snd_734_, v_a_744_, v_a_749_);
v___x_755_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_712_, v___x_754_, v___y_719_);
lean_dec_ref(v___x_755_);
v___x_756_ = l_Lean_Expr_mvarId_x21(v_a_749_);
lean_dec(v_a_749_);
v___x_757_ = lean_box(0);
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 1);
lean_ctor_set(v___x_736_, 1, v___x_757_);
lean_ctor_set(v___x_736_, 0, v___x_756_);
v___x_759_ = v___x_736_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___x_757_);
v___x_759_ = v_reuseFailAlloc_761_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_759_, v___y_715_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_715_);
return v___x_760_;
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec(v_a_744_);
lean_del_object(v___x_736_);
lean_dec(v_snd_734_);
lean_dec(v_fst_733_);
lean_dec_ref(v___x_731_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_715_);
lean_dec(v_fst_712_);
lean_dec(v___x_711_);
lean_dec_ref(v___x_710_);
lean_dec_ref(v___x_709_);
lean_dec_ref(v___x_708_);
lean_dec_ref(v___x_707_);
lean_dec_ref(v_target_706_);
lean_dec_ref(v_hyps_704_);
lean_dec_ref(v_00_u03c3s_701_);
v_a_762_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_748_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_748_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_del_object(v___x_736_);
lean_dec(v_snd_734_);
lean_dec(v_fst_733_);
lean_dec_ref(v___x_731_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_715_);
lean_dec(v_fst_712_);
lean_dec(v___x_711_);
lean_dec_ref(v___x_710_);
lean_dec_ref(v___x_709_);
lean_dec_ref(v___x_708_);
lean_dec_ref(v___x_707_);
lean_dec_ref(v_target_706_);
lean_dec_ref(v_hyps_704_);
lean_dec(v_u_703_);
lean_dec_ref(v_00_u03c3s_701_);
v_a_770_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_743_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_743_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_726_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v_fst_712_);
lean_dec(v___x_711_);
lean_dec_ref(v___x_710_);
lean_dec_ref(v___x_709_);
lean_dec_ref(v___x_708_);
lean_dec_ref(v___x_707_);
lean_dec_ref(v_target_706_);
lean_dec(v___x_705_);
lean_dec_ref(v_hyps_704_);
lean_dec(v_u_703_);
lean_dec_ref(v_00_u03c3s_701_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___boxed(lean_object** _args){
lean_object* v___x_782_ = _args[0];
lean_object* v_00_u03c3s_783_ = _args[1];
lean_object* v___x_784_ = _args[2];
lean_object* v_u_785_ = _args[3];
lean_object* v_hyps_786_ = _args[4];
lean_object* v___x_787_ = _args[5];
lean_object* v_target_788_ = _args[6];
lean_object* v___x_789_ = _args[7];
lean_object* v___x_790_ = _args[8];
lean_object* v___x_791_ = _args[9];
lean_object* v___x_792_ = _args[10];
lean_object* v___x_793_ = _args[11];
lean_object* v_fst_794_ = _args[12];
lean_object* v_H_795_ = _args[13];
lean_object* v___y_796_ = _args[14];
lean_object* v___y_797_ = _args[15];
lean_object* v___y_798_ = _args[16];
lean_object* v___y_799_ = _args[17];
lean_object* v___y_800_ = _args[18];
lean_object* v___y_801_ = _args[19];
lean_object* v___y_802_ = _args[20];
lean_object* v___y_803_ = _args[21];
lean_object* v___y_804_ = _args[22];
_start:
{
uint8_t v___x_2882__boxed_805_; lean_object* v_res_806_; 
v___x_2882__boxed_805_ = lean_unbox(v___x_784_);
v_res_806_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0(v___x_782_, v_00_u03c3s_783_, v___x_2882__boxed_805_, v_u_785_, v_hyps_786_, v___x_787_, v_target_788_, v___x_789_, v___x_790_, v___x_791_, v___x_792_, v___x_793_, v_fst_794_, v_H_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1(lean_object* v_ty_x3f_807_, lean_object* v___x_808_, lean_object* v___f_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
if (lean_obj_tag(v_ty_x3f_807_) == 1)
{
lean_object* v_val_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_838_; 
v_val_819_ = lean_ctor_get(v_ty_x3f_807_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v_ty_x3f_807_);
if (v_isSharedCheck_838_ == 0)
{
v___x_821_ = v_ty_x3f_807_;
v_isShared_822_ = v_isSharedCheck_838_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_val_819_);
lean_dec(v_ty_x3f_807_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_838_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_808_);
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_808_);
v___x_824_ = v_reuseFailAlloc_837_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
uint8_t v___x_825_; lean_object* v___x_826_; 
v___x_825_ = 0;
lean_inc(v___y_817_);
lean_inc_ref(v___y_816_);
lean_inc(v___y_815_);
lean_inc_ref(v___y_814_);
lean_inc(v___y_813_);
lean_inc_ref(v___y_812_);
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
v___x_826_ = l_Lean_Elab_Tactic_elabTerm(v_val_819_, v___x_824_, v___x_825_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_828_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref(v___x_826_);
v___x_828_ = lean_apply_10(v___f_809_, v_a_827_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, lean_box(0));
return v___x_828_;
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec_ref(v___f_809_);
v_a_829_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_826_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_826_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
}
else
{
lean_object* v___x_839_; uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec(v_ty_x3f_807_);
v___x_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_808_);
v___x_840_ = 0;
v___x_841_ = lean_box(0);
lean_inc_ref(v___y_814_);
v___x_842_ = l_Lean_Meta_mkFreshExprMVar(v___x_839_, v___x_840_, v___x_841_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_844_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref(v___x_842_);
v___x_844_ = lean_apply_10(v___f_809_, v_a_843_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, lean_box(0));
return v___x_844_;
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec_ref(v___f_809_);
v_a_845_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_842_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_842_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1___boxed(lean_object* v_ty_x3f_853_, lean_object* v___x_854_, lean_object* v___f_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1(v_ty_x3f_853_, v___x_854_, v___f_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave(lean_object* v_x_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v___x_886_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2));
v___x_887_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1));
lean_inc(v_x_876_);
v___x_888_ = l_Lean_Syntax_isOfKind(v_x_876_, v___x_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; 
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_x_876_);
v___x_889_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_889_;
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v_ty_x3f_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_890_ = lean_unsigned_to_nat(1u);
v___x_891_ = l_Lean_Syntax_getArg(v_x_876_, v___x_890_);
v___x_938_ = lean_unsigned_to_nat(2u);
v___x_939_ = l_Lean_Syntax_getArg(v_x_876_, v___x_938_);
v___x_940_ = l_Lean_Syntax_isNone(v___x_939_);
if (v___x_940_ == 0)
{
uint8_t v___x_941_; 
lean_inc(v___x_939_);
v___x_941_ = l_Lean_Syntax_matchesNull(v___x_939_, v___x_938_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
lean_dec(v___x_939_);
lean_dec(v___x_891_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_x_876_);
v___x_942_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_942_;
}
else
{
lean_object* v_ty_x3f_943_; lean_object* v___x_944_; 
v_ty_x3f_943_ = l_Lean_Syntax_getArg(v___x_939_, v___x_890_);
lean_dec(v___x_939_);
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v_ty_x3f_943_);
v_ty_x3f_893_ = v___x_944_;
v___y_894_ = v_a_877_;
v___y_895_ = v_a_878_;
v___y_896_ = v_a_879_;
v___y_897_ = v_a_880_;
v___y_898_ = v_a_881_;
v___y_899_ = v_a_882_;
v___y_900_ = v_a_883_;
v___y_901_ = v_a_884_;
goto v___jp_892_;
}
}
else
{
lean_object* v___x_945_; 
lean_dec(v___x_939_);
v___x_945_ = lean_box(0);
v_ty_x3f_893_ = v___x_945_;
v___y_894_ = v_a_877_;
v___y_895_ = v_a_878_;
v___y_896_ = v_a_879_;
v___y_897_ = v_a_880_;
v___y_898_ = v_a_881_;
v___y_899_ = v_a_882_;
v___y_900_ = v_a_883_;
v___y_901_ = v_a_884_;
goto v___jp_892_;
}
v___jp_892_:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v_snd_904_; lean_object* v_fst_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_929_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref(v___x_902_);
v_snd_904_ = lean_ctor_get(v_a_903_, 1);
v_fst_905_ = lean_ctor_get(v_a_903_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v_a_903_);
if (v_isSharedCheck_929_ == 0)
{
v___x_907_ = v_a_903_;
v_isShared_908_ = v_isSharedCheck_929_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_snd_904_);
lean_inc(v_fst_905_);
lean_dec(v_a_903_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_929_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v_u_909_; lean_object* v_00_u03c3s_910_; lean_object* v_hyps_911_; lean_object* v_target_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v_u_909_ = lean_ctor_get(v_snd_904_, 0);
lean_inc(v_u_909_);
v_00_u03c3s_910_ = lean_ctor_get(v_snd_904_, 1);
lean_inc_ref(v_00_u03c3s_910_);
v_hyps_911_ = lean_ctor_get(v_snd_904_, 2);
lean_inc_ref(v_hyps_911_);
v_target_912_ = lean_ctor_get(v_snd_904_, 3);
lean_inc_ref(v_target_912_);
lean_dec(v_snd_904_);
v___x_913_ = lean_unsigned_to_nat(4u);
v___x_914_ = l_Lean_Syntax_getArg(v_x_876_, v___x_913_);
lean_dec(v_x_876_);
v___x_915_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0));
v___x_916_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1));
v___x_917_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2));
v___x_918_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2));
v___x_919_ = lean_box(0);
lean_inc(v_u_909_);
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 1);
lean_ctor_set(v___x_907_, 1, v___x_919_);
lean_ctor_set(v___x_907_, 0, v_u_909_);
v___x_921_ = v___x_907_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_u_909_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v___x_919_);
v___x_921_ = v_reuseFailAlloc_928_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___f_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___y_926_; lean_object* v___x_927_; 
v___x_922_ = lean_box(v___x_888_);
lean_inc(v_fst_905_);
lean_inc_ref(v___x_921_);
lean_inc_ref(v_00_u03c3s_910_);
v___f_923_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___boxed), 23, 13);
lean_closure_set(v___f_923_, 0, v___x_891_);
lean_closure_set(v___f_923_, 1, v_00_u03c3s_910_);
lean_closure_set(v___f_923_, 2, v___x_922_);
lean_closure_set(v___f_923_, 3, v_u_909_);
lean_closure_set(v___f_923_, 4, v_hyps_911_);
lean_closure_set(v___f_923_, 5, v___x_914_);
lean_closure_set(v___f_923_, 6, v_target_912_);
lean_closure_set(v___f_923_, 7, v___x_915_);
lean_closure_set(v___f_923_, 8, v___x_916_);
lean_closure_set(v___f_923_, 9, v___x_917_);
lean_closure_set(v___f_923_, 10, v___x_886_);
lean_closure_set(v___f_923_, 11, v___x_921_);
lean_closure_set(v___f_923_, 12, v_fst_905_);
v___x_924_ = l_Lean_mkConst(v___x_918_, v___x_921_);
v___x_925_ = l_Lean_Expr_app___override(v___x_924_, v_00_u03c3s_910_);
v___y_926_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1___boxed), 12, 3);
lean_closure_set(v___y_926_, 0, v_ty_x3f_893_);
lean_closure_set(v___y_926_, 1, v___x_925_);
lean_closure_set(v___y_926_, 2, v___f_923_);
v___x_927_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_905_, v___y_926_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
return v___x_927_;
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v_ty_x3f_893_);
lean_dec(v___x_891_);
lean_dec(v_x_876_);
v_a_930_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_902_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_902_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___boxed(lean_object* v_x_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave(v_x_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1(){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_966_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_967_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1));
v___x_968_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1));
v___x_969_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___boxed), 10, 0);
v___x_970_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_966_, v___x_967_, v___x_968_, v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___boxed(lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1();
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0(lean_object* v___x_974_, lean_object* v_u_975_, lean_object* v___x_976_, lean_object* v___x_977_, lean_object* v_00_u03c3s_978_, uint8_t v___x_979_, lean_object* v_hyps_980_, lean_object* v___x_981_, lean_object* v_target_982_, lean_object* v___x_983_, lean_object* v_fst_984_, lean_object* v_ty_x3f_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
if (lean_obj_tag(v___x_974_) == 1)
{
lean_object* v_val_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1111_; 
v_val_995_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_997_ = v___x_974_;
v_isShared_998_ = v_isSharedCheck_1111_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_val_995_);
lean_dec(v___x_974_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1111_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_focusHyp_999_; lean_object* v_restHyps_1000_; lean_object* v_proof_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1110_; 
v_focusHyp_999_ = lean_ctor_get(v_val_995_, 0);
v_restHyps_1000_ = lean_ctor_get(v_val_995_, 1);
v_proof_1001_ = lean_ctor_get(v_val_995_, 2);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_val_995_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1003_ = v_val_995_;
v_isShared_1004_ = v_isSharedCheck_1110_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_proof_1001_);
lean_inc(v_restHyps_1000_);
lean_inc(v_focusHyp_999_);
lean_dec(v_val_995_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1110_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v_H_x27_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1005_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0));
v___x_1006_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1));
v___x_1007_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2));
v___x_1008_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2));
v___x_1009_ = lean_box(0);
lean_inc(v_u_975_);
v___x_1010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1010_, 0, v_u_975_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
lean_inc_ref(v___x_1010_);
v___x_1076_ = l_Lean_mkConst(v___x_1008_, v___x_1010_);
lean_inc_ref(v_00_u03c3s_978_);
v___x_1077_ = l_Lean_Expr_app___override(v___x_1076_, v_00_u03c3s_978_);
if (lean_obj_tag(v_ty_x3f_985_) == 1)
{
lean_object* v_val_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1096_; 
v_val_1078_ = lean_ctor_get(v_ty_x3f_985_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_ty_x3f_985_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1080_ = v_ty_x3f_985_;
v_isShared_1081_ = v_isSharedCheck_1096_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_val_1078_);
lean_dec(v_ty_x3f_985_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1096_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1077_);
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1077_);
v___x_1083_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
uint8_t v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = 0;
lean_inc(v___y_993_);
lean_inc_ref(v___y_992_);
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
v___x_1085_ = l_Lean_Elab_Tactic_elabTerm(v_val_1078_, v___x_1083_, v___x_1084_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref(v___x_1085_);
v_H_x27_1012_ = v_a_1086_;
v___y_1013_ = v___y_986_;
v___y_1014_ = v___y_987_;
v___y_1015_ = v___y_988_;
v___y_1016_ = v___y_989_;
v___y_1017_ = v___y_990_;
v___y_1018_ = v___y_991_;
v___y_1019_ = v___y_992_;
v___y_1020_ = v___y_993_;
goto v___jp_1011_;
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v___x_1010_);
lean_del_object(v___x_1003_);
lean_dec_ref(v_proof_1001_);
lean_dec_ref(v_restHyps_1000_);
lean_dec_ref(v_focusHyp_999_);
lean_del_object(v___x_997_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v_fst_984_);
lean_dec_ref(v___x_983_);
lean_dec_ref(v_target_982_);
lean_dec(v___x_981_);
lean_dec_ref(v_hyps_980_);
lean_dec_ref(v_00_u03c3s_978_);
lean_dec(v___x_977_);
lean_dec(v___x_976_);
lean_dec(v_u_975_);
v_a_1087_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1085_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1085_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
}
else
{
lean_object* v___x_1097_; uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_dec(v_ty_x3f_985_);
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1077_);
v___x_1098_ = 0;
v___x_1099_ = lean_box(0);
lean_inc_ref(v___y_990_);
v___x_1100_ = l_Lean_Meta_mkFreshExprMVar(v___x_1097_, v___x_1098_, v___x_1099_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref(v___x_1100_);
v_H_x27_1012_ = v_a_1101_;
v___y_1013_ = v___y_986_;
v___y_1014_ = v___y_987_;
v___y_1015_ = v___y_988_;
v___y_1016_ = v___y_989_;
v___y_1017_ = v___y_990_;
v___y_1018_ = v___y_991_;
v___y_1019_ = v___y_992_;
v___y_1020_ = v___y_993_;
goto v___jp_1011_;
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec_ref(v___x_1010_);
lean_del_object(v___x_1003_);
lean_dec_ref(v_proof_1001_);
lean_dec_ref(v_restHyps_1000_);
lean_dec_ref(v_focusHyp_999_);
lean_del_object(v___x_997_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v_fst_984_);
lean_dec_ref(v___x_983_);
lean_dec_ref(v_target_982_);
lean_dec(v___x_981_);
lean_dec_ref(v_hyps_980_);
lean_dec_ref(v_00_u03c3s_978_);
lean_dec(v___x_977_);
lean_dec(v___x_976_);
lean_dec(v_u_975_);
v_a_1102_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1100_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1100_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
v___jp_1011_:
{
lean_object* v___x_1021_; lean_object* v_a_1022_; lean_object* v___x_1024_; 
v___x_1021_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_1020_);
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref(v___x_1021_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 2, v_H_x27_1012_);
lean_ctor_set(v___x_1003_, 1, v_a_1022_);
lean_ctor_set(v___x_1003_, 0, v___x_976_);
v___x_1024_ = v___x_1003_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_a_1022_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v_H_x27_1012_);
v___x_1024_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; 
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc_ref(v___x_1024_);
lean_inc_ref(v_00_u03c3s_978_);
v___x_1025_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v___x_977_, v_00_u03c3s_978_, v___x_1024_, v___x_979_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
lean_dec_ref(v___x_1025_);
v___x_1026_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1024_);
lean_inc_ref(v___x_1026_);
lean_inc_ref(v_hyps_980_);
lean_inc_ref(v_00_u03c3s_978_);
lean_inc(v_u_975_);
v___x_1027_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1027_, 0, v_u_975_);
lean_ctor_set(v___x_1027_, 1, v_00_u03c3s_978_);
lean_ctor_set(v___x_1027_, 2, v_hyps_980_);
lean_ctor_set(v___x_1027_, 3, v___x_1026_);
v___x_1028_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1027_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1028_);
v___x_1030_ = v___x_997_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
uint8_t v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = 0;
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc(v___y_1014_);
v___x_1032_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v___x_981_, v___x_1030_, v___x_1031_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1034_; lean_object* v_fst_1035_; lean_object* v_snd_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1065_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref(v___x_1032_);
lean_inc_ref(v___x_1026_);
lean_inc_ref(v_restHyps_1000_);
lean_inc_ref(v_00_u03c3s_978_);
lean_inc(v_u_975_);
v___x_1034_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_975_, v_00_u03c3s_978_, v_restHyps_1000_, v___x_1026_);
v_fst_1035_ = lean_ctor_get(v___x_1034_, 0);
v_snd_1036_ = lean_ctor_get(v___x_1034_, 1);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1038_ = v___x_1034_;
v_isShared_1039_ = v_isSharedCheck_1065_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_snd_1036_);
lean_inc(v_fst_1035_);
lean_dec(v___x_1034_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1065_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_inc_ref(v_target_982_);
lean_inc(v_fst_1035_);
lean_inc_ref(v_00_u03c3s_978_);
v___x_1040_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1040_, 0, v_u_975_);
lean_ctor_set(v___x_1040_, 1, v_00_u03c3s_978_);
lean_ctor_set(v___x_1040_, 2, v_fst_1035_);
lean_ctor_set(v___x_1040_, 3, v_target_982_);
v___x_1041_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1040_);
v___x_1042_ = lean_box(0);
lean_inc_ref(v___y_1017_);
v___x_1043_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1041_, v___x_1042_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref(v___x_1043_);
v___x_1045_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3));
v___x_1046_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___closed__0));
v___x_1047_ = l_Lean_Name_mkStr6(v___x_1005_, v___x_1006_, v___x_1007_, v___x_983_, v___x_1045_, v___x_1046_);
v___x_1048_ = l_Lean_mkConst(v___x_1047_, v___x_1010_);
v___x_1049_ = l_Lean_mkApp10(v___x_1048_, v_00_u03c3s_978_, v_restHyps_1000_, v_focusHyp_999_, v___x_1026_, v_hyps_980_, v_fst_1035_, v_target_982_, v_proof_1001_, v_snd_1036_, v_a_1033_);
lean_inc(v_a_1044_);
v___x_1050_ = l_Lean_Expr_app___override(v___x_1049_, v_a_1044_);
v___x_1051_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_984_, v___x_1050_, v___y_1018_);
lean_dec_ref(v___x_1051_);
v___x_1052_ = l_Lean_Expr_mvarId_x21(v_a_1044_);
lean_dec(v_a_1044_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 1);
lean_ctor_set(v___x_1038_, 1, v___x_1009_);
lean_ctor_set(v___x_1038_, 0, v___x_1052_);
v___x_1054_ = v___x_1038_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1009_);
v___x_1054_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1054_, v___y_1014_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1014_);
return v___x_1055_;
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_del_object(v___x_1038_);
lean_dec(v_snd_1036_);
lean_dec(v_fst_1035_);
lean_dec(v_a_1033_);
lean_dec_ref(v___x_1026_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1014_);
lean_dec_ref(v___x_1010_);
lean_dec_ref(v_proof_1001_);
lean_dec_ref(v_restHyps_1000_);
lean_dec_ref(v_focusHyp_999_);
lean_dec(v_fst_984_);
lean_dec_ref(v___x_983_);
lean_dec_ref(v_target_982_);
lean_dec_ref(v_hyps_980_);
lean_dec_ref(v_00_u03c3s_978_);
v_a_1057_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1043_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1043_);
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
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec_ref(v___x_1026_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1014_);
lean_dec_ref(v___x_1010_);
lean_dec_ref(v_proof_1001_);
lean_dec_ref(v_restHyps_1000_);
lean_dec_ref(v_focusHyp_999_);
lean_dec(v_fst_984_);
lean_dec_ref(v___x_983_);
lean_dec_ref(v_target_982_);
lean_dec_ref(v_hyps_980_);
lean_dec_ref(v_00_u03c3s_978_);
lean_dec(v_u_975_);
v_a_1066_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1032_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1032_);
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
else
{
lean_dec_ref(v___x_1024_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec_ref(v___x_1010_);
lean_dec_ref(v_proof_1001_);
lean_dec_ref(v_restHyps_1000_);
lean_dec_ref(v_focusHyp_999_);
lean_del_object(v___x_997_);
lean_dec(v_fst_984_);
lean_dec_ref(v___x_983_);
lean_dec_ref(v_target_982_);
lean_dec(v___x_981_);
lean_dec_ref(v_hyps_980_);
lean_dec_ref(v_00_u03c3s_978_);
lean_dec(v_u_975_);
return v___x_1025_;
}
}
}
}
}
}
else
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v_ty_x3f_985_);
lean_dec(v_fst_984_);
lean_dec_ref(v___x_983_);
lean_dec_ref(v_target_982_);
lean_dec(v___x_981_);
lean_dec_ref(v_hyps_980_);
lean_dec_ref(v_00_u03c3s_978_);
lean_dec(v___x_976_);
lean_dec(v_u_975_);
lean_dec(v___x_974_);
v___x_1112_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6);
v___x_1113_ = l_Lean_MessageData_ofSyntax(v___x_977_);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1114_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v___x_1116_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___boxed(lean_object** _args){
lean_object* v___x_1118_ = _args[0];
lean_object* v_u_1119_ = _args[1];
lean_object* v___x_1120_ = _args[2];
lean_object* v___x_1121_ = _args[3];
lean_object* v_00_u03c3s_1122_ = _args[4];
lean_object* v___x_1123_ = _args[5];
lean_object* v_hyps_1124_ = _args[6];
lean_object* v___x_1125_ = _args[7];
lean_object* v_target_1126_ = _args[8];
lean_object* v___x_1127_ = _args[9];
lean_object* v_fst_1128_ = _args[10];
lean_object* v_ty_x3f_1129_ = _args[11];
lean_object* v___y_1130_ = _args[12];
lean_object* v___y_1131_ = _args[13];
lean_object* v___y_1132_ = _args[14];
lean_object* v___y_1133_ = _args[15];
lean_object* v___y_1134_ = _args[16];
lean_object* v___y_1135_ = _args[17];
lean_object* v___y_1136_ = _args[18];
lean_object* v___y_1137_ = _args[19];
lean_object* v___y_1138_ = _args[20];
_start:
{
uint8_t v___x_3617__boxed_1139_; lean_object* v_res_1140_; 
v___x_3617__boxed_1139_ = lean_unbox(v___x_1123_);
v_res_1140_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0(v___x_1118_, v_u_1119_, v___x_1120_, v___x_1121_, v_00_u03c3s_1122_, v___x_3617__boxed_1139_, v_hyps_1124_, v___x_1125_, v_target_1126_, v___x_1127_, v_fst_1128_, v_ty_x3f_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace(lean_object* v_x_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1157_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2));
v___x_1158_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1));
lean_inc(v_x_1147_);
v___x_1159_ = l_Lean_Syntax_isOfKind(v_x_1147_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_x_1147_);
v___x_1160_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v_ty_x3f_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = l_Lean_Syntax_getArg(v_x_1147_, v___x_1161_);
v___x_1196_ = lean_unsigned_to_nat(2u);
v___x_1197_ = l_Lean_Syntax_getArg(v_x_1147_, v___x_1196_);
v___x_1198_ = l_Lean_Syntax_isNone(v___x_1197_);
if (v___x_1198_ == 0)
{
uint8_t v___x_1199_; 
lean_inc(v___x_1197_);
v___x_1199_ = l_Lean_Syntax_matchesNull(v___x_1197_, v___x_1196_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; 
lean_dec(v___x_1197_);
lean_dec(v___x_1162_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_x_1147_);
v___x_1200_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_1200_;
}
else
{
lean_object* v_ty_x3f_1201_; lean_object* v___x_1202_; 
v_ty_x3f_1201_ = l_Lean_Syntax_getArg(v___x_1197_, v___x_1161_);
lean_dec(v___x_1197_);
v___x_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1202_, 0, v_ty_x3f_1201_);
v_ty_x3f_1164_ = v___x_1202_;
v___y_1165_ = v_a_1148_;
v___y_1166_ = v_a_1149_;
v___y_1167_ = v_a_1150_;
v___y_1168_ = v_a_1151_;
v___y_1169_ = v_a_1152_;
v___y_1170_ = v_a_1153_;
v___y_1171_ = v_a_1154_;
v___y_1172_ = v_a_1155_;
goto v___jp_1163_;
}
}
else
{
lean_object* v___x_1203_; 
lean_dec(v___x_1197_);
v___x_1203_ = lean_box(0);
v_ty_x3f_1164_ = v___x_1203_;
v___y_1165_ = v_a_1148_;
v___y_1166_ = v_a_1149_;
v___y_1167_ = v_a_1150_;
v___y_1168_ = v_a_1151_;
v___y_1169_ = v_a_1152_;
v___y_1170_ = v_a_1153_;
v___y_1171_ = v_a_1154_;
v___y_1172_ = v_a_1155_;
goto v___jp_1163_;
}
v___jp_1163_:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v_snd_1175_; lean_object* v_fst_1176_; lean_object* v_u_1177_; lean_object* v_00_u03c3s_1178_; lean_object* v_hyps_1179_; lean_object* v_target_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___y_1186_; lean_object* v___x_1187_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref(v___x_1173_);
v_snd_1175_ = lean_ctor_get(v_a_1174_, 1);
lean_inc(v_snd_1175_);
v_fst_1176_ = lean_ctor_get(v_a_1174_, 0);
lean_inc(v_fst_1176_);
lean_dec(v_a_1174_);
v_u_1177_ = lean_ctor_get(v_snd_1175_, 0);
lean_inc(v_u_1177_);
v_00_u03c3s_1178_ = lean_ctor_get(v_snd_1175_, 1);
lean_inc_ref(v_00_u03c3s_1178_);
v_hyps_1179_ = lean_ctor_get(v_snd_1175_, 2);
lean_inc_ref(v_hyps_1179_);
v_target_1180_ = lean_ctor_get(v_snd_1175_, 3);
lean_inc_ref(v_target_1180_);
v___x_1181_ = lean_unsigned_to_nat(4u);
v___x_1182_ = l_Lean_Syntax_getArg(v_x_1147_, v___x_1181_);
lean_dec(v_x_1147_);
v___x_1183_ = l_Lean_Syntax_getId(v___x_1162_);
v___x_1184_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_1175_, v___x_1183_);
v___x_1185_ = lean_box(v___x_1159_);
lean_inc(v_fst_1176_);
v___y_1186_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___boxed), 21, 12);
lean_closure_set(v___y_1186_, 0, v___x_1184_);
lean_closure_set(v___y_1186_, 1, v_u_1177_);
lean_closure_set(v___y_1186_, 2, v___x_1183_);
lean_closure_set(v___y_1186_, 3, v___x_1162_);
lean_closure_set(v___y_1186_, 4, v_00_u03c3s_1178_);
lean_closure_set(v___y_1186_, 5, v___x_1185_);
lean_closure_set(v___y_1186_, 6, v_hyps_1179_);
lean_closure_set(v___y_1186_, 7, v___x_1182_);
lean_closure_set(v___y_1186_, 8, v_target_1180_);
lean_closure_set(v___y_1186_, 9, v___x_1157_);
lean_closure_set(v___y_1186_, 10, v_fst_1176_);
lean_closure_set(v___y_1186_, 11, v_ty_x3f_1164_);
v___x_1187_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_1176_, v___y_1186_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
return v___x_1187_;
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v_ty_x3f_1164_);
lean_dec(v___x_1162_);
lean_dec(v_x_1147_);
v_a_1188_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1173_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1173_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___boxed(lean_object* v_x_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace(v_x_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1(){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1224_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1225_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1));
v___x_1226_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1));
v___x_1227_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___boxed), 10, 0);
v___x_1228_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1224_, v___x_1225_, v___x_1226_, v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___boxed(lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1();
return v_res_1230_;
}
}
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Have(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1();
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
