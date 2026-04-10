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
lean_inc(v___y_93_);
lean_inc_ref(v___y_92_);
lean_inc(v___y_91_);
lean_inc_ref(v___y_90_);
v___x_99_ = lean_apply_9(v_x_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, lean_box(0));
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0___boxed(lean_object* v_x_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0(v_x_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(lean_object* v_mvarId_111_, lean_object* v_x_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v___f_122_; lean_object* v___x_123_; 
lean_inc(v___y_116_);
lean_inc_ref(v___y_115_);
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
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
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
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
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
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
size_t v_x_7753__boxed_317_; size_t v_x_7754__boxed_318_; lean_object* v_res_319_; 
v_x_7753__boxed_317_ = lean_unbox_usize(v_x_313_);
lean_dec(v_x_313_);
v_x_7754__boxed_318_ = lean_unbox_usize(v_x_314_);
lean_dec(v_x_314_);
v_res_319_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_312_, v_x_7753__boxed_317_, v_x_7754__boxed_318_, v_x_315_, v_x_316_);
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
lean_object* v___x_331_; lean_object* v_mctx_332_; lean_object* v_cache_333_; lean_object* v_zetaDeltaFVarIds_334_; lean_object* v_postponed_335_; lean_object* v_diag_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_364_; 
v___x_331_ = lean_st_ref_take(v___y_329_);
v_mctx_332_ = lean_ctor_get(v___x_331_, 0);
v_cache_333_ = lean_ctor_get(v___x_331_, 1);
v_zetaDeltaFVarIds_334_ = lean_ctor_get(v___x_331_, 2);
v_postponed_335_ = lean_ctor_get(v___x_331_, 3);
v_diag_336_ = lean_ctor_get(v___x_331_, 4);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_364_ == 0)
{
v___x_338_ = v___x_331_;
v_isShared_339_ = v_isSharedCheck_364_;
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
v_isShared_339_ = v_isSharedCheck_364_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v_depth_340_; lean_object* v_levelAssignDepth_341_; lean_object* v_lmvarCounter_342_; lean_object* v_mvarCounter_343_; lean_object* v_lDecls_344_; lean_object* v_decls_345_; lean_object* v_userNames_346_; lean_object* v_lAssignment_347_; lean_object* v_eAssignment_348_; lean_object* v_dAssignment_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_363_; 
v_depth_340_ = lean_ctor_get(v_mctx_332_, 0);
v_levelAssignDepth_341_ = lean_ctor_get(v_mctx_332_, 1);
v_lmvarCounter_342_ = lean_ctor_get(v_mctx_332_, 2);
v_mvarCounter_343_ = lean_ctor_get(v_mctx_332_, 3);
v_lDecls_344_ = lean_ctor_get(v_mctx_332_, 4);
v_decls_345_ = lean_ctor_get(v_mctx_332_, 5);
v_userNames_346_ = lean_ctor_get(v_mctx_332_, 6);
v_lAssignment_347_ = lean_ctor_get(v_mctx_332_, 7);
v_eAssignment_348_ = lean_ctor_get(v_mctx_332_, 8);
v_dAssignment_349_ = lean_ctor_get(v_mctx_332_, 9);
v_isSharedCheck_363_ = !lean_is_exclusive(v_mctx_332_);
if (v_isSharedCheck_363_ == 0)
{
v___x_351_ = v_mctx_332_;
v_isShared_352_ = v_isSharedCheck_363_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_dAssignment_349_);
lean_inc(v_eAssignment_348_);
lean_inc(v_lAssignment_347_);
lean_inc(v_userNames_346_);
lean_inc(v_decls_345_);
lean_inc(v_lDecls_344_);
lean_inc(v_mvarCounter_343_);
lean_inc(v_lmvarCounter_342_);
lean_inc(v_levelAssignDepth_341_);
lean_inc(v_depth_340_);
lean_dec(v_mctx_332_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_363_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(v_eAssignment_348_, v_mvarId_327_, v_val_328_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 8, v___x_353_);
v___x_355_ = v___x_351_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_depth_340_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_levelAssignDepth_341_);
lean_ctor_set(v_reuseFailAlloc_362_, 2, v_lmvarCounter_342_);
lean_ctor_set(v_reuseFailAlloc_362_, 3, v_mvarCounter_343_);
lean_ctor_set(v_reuseFailAlloc_362_, 4, v_lDecls_344_);
lean_ctor_set(v_reuseFailAlloc_362_, 5, v_decls_345_);
lean_ctor_set(v_reuseFailAlloc_362_, 6, v_userNames_346_);
lean_ctor_set(v_reuseFailAlloc_362_, 7, v_lAssignment_347_);
lean_ctor_set(v_reuseFailAlloc_362_, 8, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_362_, 9, v_dAssignment_349_);
v___x_355_ = v_reuseFailAlloc_362_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_357_; 
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_355_);
v___x_357_ = v___x_338_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_cache_333_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v_zetaDeltaFVarIds_334_);
lean_ctor_set(v_reuseFailAlloc_361_, 3, v_postponed_335_);
lean_ctor_set(v_reuseFailAlloc_361_, 4, v_diag_336_);
v___x_357_ = v_reuseFailAlloc_361_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = lean_st_ref_set(v___y_329_, v___x_357_);
v___x_359_ = lean_box(0);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg___boxed(lean_object* v_mvarId_365_, lean_object* v_val_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_mvarId_365_, v_val_366_, v___y_367_);
lean_dec(v___y_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(lean_object* v_msgData_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; lean_object* v_env_377_; lean_object* v___x_378_; lean_object* v_mctx_379_; lean_object* v_lctx_380_; lean_object* v_options_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_376_ = lean_st_ref_get(v___y_374_);
v_env_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc_ref(v_env_377_);
lean_dec(v___x_376_);
v___x_378_ = lean_st_ref_get(v___y_372_);
v_mctx_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc_ref(v_mctx_379_);
lean_dec(v___x_378_);
v_lctx_380_ = lean_ctor_get(v___y_371_, 2);
v_options_381_ = lean_ctor_get(v___y_373_, 2);
lean_inc_ref(v_options_381_);
lean_inc_ref(v_lctx_380_);
v___x_382_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_382_, 0, v_env_377_);
lean_ctor_set(v___x_382_, 1, v_mctx_379_);
lean_ctor_set(v___x_382_, 2, v_lctx_380_);
lean_ctor_set(v___x_382_, 3, v_options_381_);
v___x_383_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v_msgData_370_);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4___boxed(lean_object* v_msgData_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(v_msgData_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(lean_object* v_msg_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_ref_398_; lean_object* v___x_399_; lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_408_; 
v_ref_398_ = lean_ctor_get(v___y_395_, 5);
v___x_399_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(v_msg_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_408_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
lean_inc(v_ref_398_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v_ref_398_);
lean_ctor_set(v___x_404_, 1, v_a_400_);
if (v_isShared_403_ == 0)
{
lean_ctor_set_tag(v___x_402_, 1);
lean_ctor_set(v___x_402_, 0, v___x_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg___boxed(lean_object* v_msg_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v_msg_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_415_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__5));
v___x_423_ = l_Lean_stringToMessageData(v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__7));
v___x_426_ = l_Lean_stringToMessageData(v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0(lean_object* v___x_427_, lean_object* v_snd_428_, lean_object* v___x_429_, lean_object* v___x_430_, uint8_t v___x_431_, lean_object* v___x_432_, lean_object* v_fst_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
if (lean_obj_tag(v___x_427_) == 1)
{
lean_object* v_val_443_; lean_object* v___x_444_; lean_object* v_a_445_; lean_object* v_focusHyp_446_; lean_object* v_restHyps_447_; lean_object* v_proof_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_497_; 
v_val_443_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_val_443_);
lean_dec_ref(v___x_427_);
v___x_444_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_441_);
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref(v___x_444_);
v_focusHyp_446_ = lean_ctor_get(v_val_443_, 0);
v_restHyps_447_ = lean_ctor_get(v_val_443_, 1);
v_proof_448_ = lean_ctor_get(v_val_443_, 2);
v_isSharedCheck_497_ = !lean_is_exclusive(v_val_443_);
if (v_isSharedCheck_497_ == 0)
{
v___x_450_ = v_val_443_;
v_isShared_451_ = v_isSharedCheck_497_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_proof_448_);
lean_inc(v_restHyps_447_);
lean_inc(v_focusHyp_446_);
lean_dec(v_val_443_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_497_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_u_452_; lean_object* v_00_u03c3s_453_; lean_object* v_hyps_454_; lean_object* v_target_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_496_; 
v_u_452_ = lean_ctor_get(v_snd_428_, 0);
v_00_u03c3s_453_ = lean_ctor_get(v_snd_428_, 1);
v_hyps_454_ = lean_ctor_get(v_snd_428_, 2);
v_target_455_ = lean_ctor_get(v_snd_428_, 3);
v_isSharedCheck_496_ = !lean_is_exclusive(v_snd_428_);
if (v_isSharedCheck_496_ == 0)
{
v___x_457_ = v_snd_428_;
v_isShared_458_ = v_isSharedCheck_496_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_target_455_);
lean_inc(v_hyps_454_);
lean_inc(v_00_u03c3s_453_);
lean_inc(v_u_452_);
lean_dec(v_snd_428_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_496_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_459_ = l_Lean_Syntax_getId(v___x_429_);
v___x_460_ = l_Lean_Expr_consumeMData(v_focusHyp_446_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 2, v___x_460_);
lean_ctor_set(v___x_450_, 1, v_a_445_);
lean_ctor_set(v___x_450_, 0, v___x_459_);
v___x_462_ = v___x_450_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_a_445_);
lean_ctor_set(v_reuseFailAlloc_495_, 2, v___x_460_);
v___x_462_ = v_reuseFailAlloc_495_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; 
lean_inc_ref(v___x_462_);
lean_inc_ref(v_00_u03c3s_453_);
v___x_463_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v___x_430_, v_00_u03c3s_453_, v___x_462_, v___x_431_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
lean_dec_ref(v___x_463_);
v___x_464_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_462_);
lean_inc_ref(v_hyps_454_);
lean_inc_ref_n(v_00_u03c3s_453_, 2);
lean_inc_n(v_u_452_, 2);
v___x_465_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_452_, v_00_u03c3s_453_, v_hyps_454_, v___x_464_);
lean_inc_ref(v_target_455_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 2, v___x_465_);
v___x_467_ = v___x_457_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_u_452_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_00_u03c3s_453_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_494_, 3, v_target_455_);
v___x_467_ = v_reuseFailAlloc_494_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_467_);
v___x_469_ = lean_box(0);
v___x_470_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_468_, v___x_469_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc_n(v_a_471_, 2);
lean_dec_ref(v___x_470_);
v___x_472_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0));
v___x_473_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1));
v___x_474_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2));
v___x_475_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3));
v___x_476_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__4));
v___x_477_ = l_Lean_Name_mkStr6(v___x_472_, v___x_473_, v___x_474_, v___x_432_, v___x_475_, v___x_476_);
v___x_478_ = lean_box(0);
v___x_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_479_, 0, v_u_452_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = l_Lean_mkConst(v___x_477_, v___x_479_);
v___x_481_ = l_Lean_mkApp7(v___x_480_, v_00_u03c3s_453_, v_hyps_454_, v_restHyps_447_, v_focusHyp_446_, v_target_455_, v_proof_448_, v_a_471_);
v___x_482_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_433_, v___x_481_, v___y_439_);
lean_dec_ref(v___x_482_);
v___x_483_ = l_Lean_Expr_mvarId_x21(v_a_471_);
lean_dec(v_a_471_);
v___x_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v___x_478_);
v___x_485_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_484_, v___y_435_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
return v___x_485_;
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec_ref(v_target_455_);
lean_dec_ref(v_hyps_454_);
lean_dec_ref(v_00_u03c3s_453_);
lean_dec(v_u_452_);
lean_dec_ref(v_proof_448_);
lean_dec_ref(v_restHyps_447_);
lean_dec_ref(v_focusHyp_446_);
lean_dec(v_fst_433_);
lean_dec_ref(v___x_432_);
v_a_486_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_470_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_470_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_462_);
lean_del_object(v___x_457_);
lean_dec_ref(v_target_455_);
lean_dec_ref(v_hyps_454_);
lean_dec_ref(v_00_u03c3s_453_);
lean_dec(v_u_452_);
lean_dec_ref(v_proof_448_);
lean_dec_ref(v_restHyps_447_);
lean_dec_ref(v_focusHyp_446_);
lean_dec(v_fst_433_);
lean_dec_ref(v___x_432_);
return v___x_463_;
}
}
}
}
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v_fst_433_);
lean_dec_ref(v___x_432_);
lean_dec_ref(v_snd_428_);
lean_dec(v___x_427_);
v___x_498_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6);
v___x_499_ = l_Lean_MessageData_ofSyntax(v___x_430_);
v___x_500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8);
v___x_502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v___x_502_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
return v___x_503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___boxed(lean_object* v___x_504_, lean_object* v_snd_505_, lean_object* v___x_506_, lean_object* v___x_507_, lean_object* v___x_508_, lean_object* v___x_509_, lean_object* v_fst_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
uint8_t v___x_8059__boxed_520_; lean_object* v_res_521_; 
v___x_8059__boxed_520_ = lean_unbox(v___x_508_);
v_res_521_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0(v___x_504_, v_snd_505_, v___x_506_, v___x_507_, v___x_8059__boxed_520_, v___x_509_, v_fst_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___x_506_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup(lean_object* v_x_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_544_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2));
v___x_545_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4));
lean_inc(v_x_534_);
v___x_546_ = l_Lean_Syntax_isOfKind(v_x_534_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
lean_dec(v_x_534_);
v___x_547_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_547_;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_548_ = lean_unsigned_to_nat(1u);
v___x_549_ = l_Lean_Syntax_getArg(v_x_534_, v___x_548_);
v___x_550_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__6));
lean_inc(v___x_549_);
v___x_551_ = l_Lean_Syntax_isOfKind(v___x_549_, v___x_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
lean_dec(v___x_549_);
lean_dec(v_x_534_);
v___x_552_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_552_;
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_553_ = lean_unsigned_to_nat(3u);
v___x_554_ = l_Lean_Syntax_getArg(v_x_534_, v___x_553_);
lean_dec(v_x_534_);
lean_inc(v___x_554_);
v___x_555_ = l_Lean_Syntax_isOfKind(v___x_554_, v___x_550_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
lean_dec(v___x_554_);
lean_dec(v___x_549_);
v___x_556_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_556_;
}
else
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v_fst_559_; lean_object* v_snd_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___y_564_; lean_object* v___x_565_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
lean_dec_ref(v___x_557_);
v_fst_559_ = lean_ctor_get(v_a_558_, 0);
lean_inc_n(v_fst_559_, 2);
v_snd_560_ = lean_ctor_get(v_a_558_, 1);
lean_inc_n(v_snd_560_, 2);
lean_dec(v_a_558_);
v___x_561_ = l_Lean_Syntax_getId(v___x_549_);
v___x_562_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_560_, v___x_561_);
lean_dec(v___x_561_);
v___x_563_ = lean_box(v___x_555_);
v___y_564_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___boxed), 16, 7);
lean_closure_set(v___y_564_, 0, v___x_562_);
lean_closure_set(v___y_564_, 1, v_snd_560_);
lean_closure_set(v___y_564_, 2, v___x_554_);
lean_closure_set(v___y_564_, 3, v___x_549_);
lean_closure_set(v___y_564_, 4, v___x_563_);
lean_closure_set(v___y_564_, 5, v___x_544_);
lean_closure_set(v___y_564_, 6, v_fst_559_);
v___x_565_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_559_, v___y_564_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
return v___x_565_;
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec(v___x_554_);
lean_dec(v___x_549_);
v_a_566_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_557_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_557_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___boxed(lean_object* v_x_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup(v_x_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2(lean_object* v_mvarId_585_, lean_object* v_val_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_mvarId_585_, v_val_586_, v___y_592_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___boxed(lean_object* v_mvarId_597_, lean_object* v_val_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2(v_mvarId_597_, v_val_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3(lean_object* v_00_u03b1_609_, lean_object* v_msg_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v_msg_610_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___boxed(lean_object* v_00_u03b1_621_, lean_object* v_msg_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3(v_00_u03b1_621_, v_msg_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2(lean_object* v_00_u03b2_633_, lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(v_x_634_, v_x_635_, v_x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_638_, lean_object* v_x_639_, size_t v_x_640_, size_t v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_639_, v_x_640_, v_x_641_, v_x_642_, v_x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_645_, lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
size_t v_x_8396__boxed_651_; size_t v_x_8397__boxed_652_; lean_object* v_res_653_; 
v_x_8396__boxed_651_ = lean_unbox_usize(v_x_647_);
lean_dec(v_x_647_);
v_x_8397__boxed_652_ = lean_unbox_usize(v_x_648_);
lean_dec(v_x_648_);
v_res_653_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4(v_00_u03b2_645_, v_x_646_, v_x_8396__boxed_651_, v_x_8397__boxed_652_, v_x_649_, v_x_650_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_654_, lean_object* v_n_655_, lean_object* v_k_656_, lean_object* v_v_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(v_n_655_, v_k_656_, v_v_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_659_, size_t v_depth_660_, lean_object* v_keys_661_, lean_object* v_vals_662_, lean_object* v_heq_663_, lean_object* v_i_664_, lean_object* v_entries_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_660_, v_keys_661_, v_vals_662_, v_i_664_, v_entries_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_667_, lean_object* v_depth_668_, lean_object* v_keys_669_, lean_object* v_vals_670_, lean_object* v_heq_671_, lean_object* v_i_672_, lean_object* v_entries_673_){
_start:
{
size_t v_depth_boxed_674_; lean_object* v_res_675_; 
v_depth_boxed_674_ = lean_unbox_usize(v_depth_668_);
lean_dec(v_depth_668_);
v_res_675_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_667_, v_depth_boxed_674_, v_keys_669_, v_vals_670_, v_heq_671_, v_i_672_, v_entries_673_);
lean_dec_ref(v_vals_670_);
lean_dec_ref(v_keys_669_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_676_, lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_677_, v_x_678_, v_x_679_, v_x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1(){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_693_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_694_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4));
v___x_695_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3));
v___x_696_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___boxed), 10, 0);
v___x_697_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_693_, v___x_694_, v___x_695_, v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___boxed(lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1();
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0(lean_object* v___x_701_, lean_object* v_00_u03c3s_702_, uint8_t v___x_703_, lean_object* v_u_704_, lean_object* v_hyps_705_, lean_object* v___x_706_, lean_object* v_target_707_, lean_object* v___x_708_, lean_object* v___x_709_, lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v___x_712_, lean_object* v_fst_713_, lean_object* v_H_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; lean_object* v_a_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_724_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_722_);
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref(v___x_724_);
v___x_726_ = l_Lean_Syntax_getId(v___x_701_);
v___x_727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v_a_725_);
lean_ctor_set(v___x_727_, 2, v_H_714_);
lean_inc_ref(v___x_727_);
lean_inc_ref(v_00_u03c3s_702_);
v___x_728_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v___x_701_, v_00_u03c3s_702_, v___x_727_, v___x_703_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_781_; 
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v___x_728_, 0);
lean_dec(v_unused_782_);
v___x_730_ = v___x_728_;
v_isShared_731_ = v_isSharedCheck_781_;
goto v_resetjp_729_;
}
else
{
lean_dec(v___x_728_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_781_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v_fst_734_; lean_object* v_snd_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_780_; 
v___x_732_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_727_);
lean_inc_ref(v___x_732_);
lean_inc_ref(v_hyps_705_);
lean_inc_ref(v_00_u03c3s_702_);
lean_inc(v_u_704_);
v___x_733_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_704_, v_00_u03c3s_702_, v_hyps_705_, v___x_732_);
v_fst_734_ = lean_ctor_get(v___x_733_, 0);
v_snd_735_ = lean_ctor_get(v___x_733_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_780_ == 0)
{
v___x_737_ = v___x_733_;
v_isShared_738_ = v_isSharedCheck_780_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_snd_735_);
lean_inc(v_fst_734_);
lean_dec(v___x_733_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_780_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
lean_inc_ref(v___x_732_);
lean_inc_ref(v_hyps_705_);
lean_inc_ref(v_00_u03c3s_702_);
lean_inc(v_u_704_);
v___x_739_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_739_, 0, v_u_704_);
lean_ctor_set(v___x_739_, 1, v_00_u03c3s_702_);
lean_ctor_set(v___x_739_, 2, v_hyps_705_);
lean_ctor_set(v___x_739_, 3, v___x_732_);
v___x_740_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_739_);
if (v_isShared_731_ == 0)
{
lean_ctor_set_tag(v___x_730_, 1);
lean_ctor_set(v___x_730_, 0, v___x_740_);
v___x_742_ = v___x_730_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_779_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
uint8_t v___x_743_; lean_object* v___x_744_; 
v___x_743_ = 0;
v___x_744_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v___x_706_, v___x_742_, v___x_743_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref(v___x_744_);
lean_inc_ref(v_target_707_);
lean_inc(v_fst_734_);
lean_inc_ref(v_00_u03c3s_702_);
v___x_746_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_746_, 0, v_u_704_);
lean_ctor_set(v___x_746_, 1, v_00_u03c3s_702_);
lean_ctor_set(v___x_746_, 2, v_fst_734_);
lean_ctor_set(v___x_746_, 3, v_target_707_);
v___x_747_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_746_);
v___x_748_ = lean_box(0);
v___x_749_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_747_, v___x_748_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc_n(v_a_750_, 2);
lean_dec_ref(v___x_749_);
v___x_751_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3));
v___x_752_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___closed__0));
v___x_753_ = l_Lean_Name_mkStr6(v___x_708_, v___x_709_, v___x_710_, v___x_711_, v___x_751_, v___x_752_);
v___x_754_ = l_Lean_mkConst(v___x_753_, v___x_712_);
v___x_755_ = l_Lean_mkApp8(v___x_754_, v_00_u03c3s_702_, v_hyps_705_, v___x_732_, v_fst_734_, v_target_707_, v_snd_735_, v_a_745_, v_a_750_);
v___x_756_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_713_, v___x_755_, v___y_720_);
lean_dec_ref(v___x_756_);
v___x_757_ = l_Lean_Expr_mvarId_x21(v_a_750_);
lean_dec(v_a_750_);
v___x_758_ = lean_box(0);
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 1);
lean_ctor_set(v___x_737_, 1, v___x_758_);
lean_ctor_set(v___x_737_, 0, v___x_757_);
v___x_760_ = v___x_737_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___x_758_);
v___x_760_ = v_reuseFailAlloc_762_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_760_, v___y_716_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
return v___x_761_;
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_a_745_);
lean_del_object(v___x_737_);
lean_dec(v_snd_735_);
lean_dec(v_fst_734_);
lean_dec_ref(v___x_732_);
lean_dec(v_fst_713_);
lean_dec(v___x_712_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v___x_710_);
lean_dec_ref(v___x_709_);
lean_dec_ref(v___x_708_);
lean_dec_ref(v_target_707_);
lean_dec_ref(v_hyps_705_);
lean_dec_ref(v_00_u03c3s_702_);
v_a_763_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_749_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_749_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_del_object(v___x_737_);
lean_dec(v_snd_735_);
lean_dec(v_fst_734_);
lean_dec_ref(v___x_732_);
lean_dec(v_fst_713_);
lean_dec(v___x_712_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v___x_710_);
lean_dec_ref(v___x_709_);
lean_dec_ref(v___x_708_);
lean_dec_ref(v_target_707_);
lean_dec_ref(v_hyps_705_);
lean_dec(v_u_704_);
lean_dec_ref(v_00_u03c3s_702_);
v_a_771_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_744_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_744_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
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
}
}
else
{
lean_dec_ref(v___x_727_);
lean_dec(v_fst_713_);
lean_dec(v___x_712_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v___x_710_);
lean_dec_ref(v___x_709_);
lean_dec_ref(v___x_708_);
lean_dec_ref(v_target_707_);
lean_dec(v___x_706_);
lean_dec_ref(v_hyps_705_);
lean_dec(v_u_704_);
lean_dec_ref(v_00_u03c3s_702_);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___boxed(lean_object** _args){
lean_object* v___x_783_ = _args[0];
lean_object* v_00_u03c3s_784_ = _args[1];
lean_object* v___x_785_ = _args[2];
lean_object* v_u_786_ = _args[3];
lean_object* v_hyps_787_ = _args[4];
lean_object* v___x_788_ = _args[5];
lean_object* v_target_789_ = _args[6];
lean_object* v___x_790_ = _args[7];
lean_object* v___x_791_ = _args[8];
lean_object* v___x_792_ = _args[9];
lean_object* v___x_793_ = _args[10];
lean_object* v___x_794_ = _args[11];
lean_object* v_fst_795_ = _args[12];
lean_object* v_H_796_ = _args[13];
lean_object* v___y_797_ = _args[14];
lean_object* v___y_798_ = _args[15];
lean_object* v___y_799_ = _args[16];
lean_object* v___y_800_ = _args[17];
lean_object* v___y_801_ = _args[18];
lean_object* v___y_802_ = _args[19];
lean_object* v___y_803_ = _args[20];
lean_object* v___y_804_ = _args[21];
lean_object* v___y_805_ = _args[22];
_start:
{
uint8_t v___x_2876__boxed_806_; lean_object* v_res_807_; 
v___x_2876__boxed_806_ = lean_unbox(v___x_785_);
v_res_807_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0(v___x_783_, v_00_u03c3s_784_, v___x_2876__boxed_806_, v_u_786_, v_hyps_787_, v___x_788_, v_target_789_, v___x_790_, v___x_791_, v___x_792_, v___x_793_, v___x_794_, v_fst_795_, v_H_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1(lean_object* v_ty_x3f_808_, lean_object* v___x_809_, lean_object* v___f_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
if (lean_obj_tag(v_ty_x3f_808_) == 1)
{
lean_object* v_val_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_839_; 
v_val_820_ = lean_ctor_get(v_ty_x3f_808_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v_ty_x3f_808_);
if (v_isSharedCheck_839_ == 0)
{
v___x_822_ = v_ty_x3f_808_;
v_isShared_823_ = v_isSharedCheck_839_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_val_820_);
lean_dec(v_ty_x3f_808_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_839_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_809_);
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_809_);
v___x_825_ = v_reuseFailAlloc_838_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
uint8_t v___x_826_; lean_object* v___x_827_; 
v___x_826_ = 0;
v___x_827_ = l_Lean_Elab_Tactic_elabTerm(v_val_820_, v___x_825_, v___x_826_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_829_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref(v___x_827_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
v___x_829_ = lean_apply_10(v___f_810_, v_a_828_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, lean_box(0));
return v___x_829_;
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v___f_810_);
v_a_830_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_827_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_827_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
else
{
lean_object* v___x_840_; uint8_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec(v_ty_x3f_808_);
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_809_);
v___x_841_ = 0;
v___x_842_ = lean_box(0);
v___x_843_ = l_Lean_Meta_mkFreshExprMVar(v___x_840_, v___x_841_, v___x_842_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_845_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref(v___x_843_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
v___x_845_ = lean_apply_10(v___f_810_, v_a_844_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, lean_box(0));
return v___x_845_;
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec_ref(v___f_810_);
v_a_846_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_843_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_843_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1___boxed(lean_object* v_ty_x3f_854_, lean_object* v___x_855_, lean_object* v___f_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1(v_ty_x3f_854_, v___x_855_, v___f_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave(lean_object* v_x_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_887_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2));
v___x_888_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1));
lean_inc(v_x_877_);
v___x_889_ = l_Lean_Syntax_isOfKind(v_x_877_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
lean_dec(v_x_877_);
v___x_890_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_890_;
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_ty_x3f_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_891_ = lean_unsigned_to_nat(1u);
v___x_892_ = l_Lean_Syntax_getArg(v_x_877_, v___x_891_);
v___x_939_ = lean_unsigned_to_nat(2u);
v___x_940_ = l_Lean_Syntax_getArg(v_x_877_, v___x_939_);
v___x_941_ = l_Lean_Syntax_isNone(v___x_940_);
if (v___x_941_ == 0)
{
uint8_t v___x_942_; 
lean_inc(v___x_940_);
v___x_942_ = l_Lean_Syntax_matchesNull(v___x_940_, v___x_939_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
lean_dec(v___x_940_);
lean_dec(v___x_892_);
lean_dec(v_x_877_);
v___x_943_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_943_;
}
else
{
lean_object* v_ty_x3f_944_; lean_object* v___x_945_; 
v_ty_x3f_944_ = l_Lean_Syntax_getArg(v___x_940_, v___x_891_);
lean_dec(v___x_940_);
v___x_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_945_, 0, v_ty_x3f_944_);
v_ty_x3f_894_ = v___x_945_;
v___y_895_ = v_a_878_;
v___y_896_ = v_a_879_;
v___y_897_ = v_a_880_;
v___y_898_ = v_a_881_;
v___y_899_ = v_a_882_;
v___y_900_ = v_a_883_;
v___y_901_ = v_a_884_;
v___y_902_ = v_a_885_;
goto v___jp_893_;
}
}
else
{
lean_object* v___x_946_; 
lean_dec(v___x_940_);
v___x_946_ = lean_box(0);
v_ty_x3f_894_ = v___x_946_;
v___y_895_ = v_a_878_;
v___y_896_ = v_a_879_;
v___y_897_ = v_a_880_;
v___y_898_ = v_a_881_;
v___y_899_ = v_a_882_;
v___y_900_ = v_a_883_;
v___y_901_ = v_a_884_;
v___y_902_ = v_a_885_;
goto v___jp_893_;
}
v___jp_893_:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v_snd_905_; lean_object* v_fst_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_930_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref(v___x_903_);
v_snd_905_ = lean_ctor_get(v_a_904_, 1);
v_fst_906_ = lean_ctor_get(v_a_904_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v_a_904_);
if (v_isSharedCheck_930_ == 0)
{
v___x_908_ = v_a_904_;
v_isShared_909_ = v_isSharedCheck_930_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_snd_905_);
lean_inc(v_fst_906_);
lean_dec(v_a_904_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_930_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_u_910_; lean_object* v_00_u03c3s_911_; lean_object* v_hyps_912_; lean_object* v_target_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v_u_910_ = lean_ctor_get(v_snd_905_, 0);
lean_inc_n(v_u_910_, 2);
v_00_u03c3s_911_ = lean_ctor_get(v_snd_905_, 1);
lean_inc_ref(v_00_u03c3s_911_);
v_hyps_912_ = lean_ctor_get(v_snd_905_, 2);
lean_inc_ref(v_hyps_912_);
v_target_913_ = lean_ctor_get(v_snd_905_, 3);
lean_inc_ref(v_target_913_);
lean_dec(v_snd_905_);
v___x_914_ = lean_unsigned_to_nat(4u);
v___x_915_ = l_Lean_Syntax_getArg(v_x_877_, v___x_914_);
lean_dec(v_x_877_);
v___x_916_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0));
v___x_917_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1));
v___x_918_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2));
v___x_919_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2));
v___x_920_ = lean_box(0);
if (v_isShared_909_ == 0)
{
lean_ctor_set_tag(v___x_908_, 1);
lean_ctor_set(v___x_908_, 1, v___x_920_);
lean_ctor_set(v___x_908_, 0, v_u_910_);
v___x_922_ = v___x_908_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_u_910_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v___x_920_);
v___x_922_ = v_reuseFailAlloc_929_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; lean_object* v___f_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___y_927_; lean_object* v___x_928_; 
v___x_923_ = lean_box(v___x_889_);
lean_inc(v_fst_906_);
lean_inc_ref(v___x_922_);
lean_inc_ref(v_00_u03c3s_911_);
v___f_924_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___boxed), 23, 13);
lean_closure_set(v___f_924_, 0, v___x_892_);
lean_closure_set(v___f_924_, 1, v_00_u03c3s_911_);
lean_closure_set(v___f_924_, 2, v___x_923_);
lean_closure_set(v___f_924_, 3, v_u_910_);
lean_closure_set(v___f_924_, 4, v_hyps_912_);
lean_closure_set(v___f_924_, 5, v___x_915_);
lean_closure_set(v___f_924_, 6, v_target_913_);
lean_closure_set(v___f_924_, 7, v___x_916_);
lean_closure_set(v___f_924_, 8, v___x_917_);
lean_closure_set(v___f_924_, 9, v___x_918_);
lean_closure_set(v___f_924_, 10, v___x_887_);
lean_closure_set(v___f_924_, 11, v___x_922_);
lean_closure_set(v___f_924_, 12, v_fst_906_);
v___x_925_ = l_Lean_mkConst(v___x_919_, v___x_922_);
v___x_926_ = l_Lean_Expr_app___override(v___x_925_, v_00_u03c3s_911_);
v___y_927_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1___boxed), 12, 3);
lean_closure_set(v___y_927_, 0, v_ty_x3f_894_);
lean_closure_set(v___y_927_, 1, v___x_926_);
lean_closure_set(v___y_927_, 2, v___f_924_);
v___x_928_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_906_, v___y_927_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
return v___x_928_;
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec(v_ty_x3f_894_);
lean_dec(v___x_892_);
lean_dec(v_x_877_);
v_a_931_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_903_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_903_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___boxed(lean_object* v_x_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave(v_x_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1(){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_967_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_968_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1));
v___x_969_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1));
v___x_970_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___boxed), 10, 0);
v___x_971_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_967_, v___x_968_, v___x_969_, v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___boxed(lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1();
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0(lean_object* v___x_975_, lean_object* v_u_976_, lean_object* v___x_977_, lean_object* v___x_978_, lean_object* v_00_u03c3s_979_, uint8_t v___x_980_, lean_object* v_hyps_981_, lean_object* v___x_982_, lean_object* v_target_983_, lean_object* v___x_984_, lean_object* v_fst_985_, lean_object* v_ty_x3f_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
if (lean_obj_tag(v___x_975_) == 1)
{
lean_object* v_val_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1112_; 
v_val_996_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_998_ = v___x_975_;
v_isShared_999_ = v_isSharedCheck_1112_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_val_996_);
lean_dec(v___x_975_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1112_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v_focusHyp_1000_; lean_object* v_restHyps_1001_; lean_object* v_proof_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1111_; 
v_focusHyp_1000_ = lean_ctor_get(v_val_996_, 0);
v_restHyps_1001_ = lean_ctor_get(v_val_996_, 1);
v_proof_1002_ = lean_ctor_get(v_val_996_, 2);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_val_996_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1004_ = v_val_996_;
v_isShared_1005_ = v_isSharedCheck_1111_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_proof_1002_);
lean_inc(v_restHyps_1001_);
lean_inc(v_focusHyp_1000_);
lean_dec(v_val_996_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1111_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v_H_x27_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1006_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0));
v___x_1007_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1));
v___x_1008_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2));
v___x_1009_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2));
v___x_1010_ = lean_box(0);
lean_inc(v_u_976_);
v___x_1011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1011_, 0, v_u_976_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
lean_inc_ref(v___x_1011_);
v___x_1077_ = l_Lean_mkConst(v___x_1009_, v___x_1011_);
lean_inc_ref(v_00_u03c3s_979_);
v___x_1078_ = l_Lean_Expr_app___override(v___x_1077_, v_00_u03c3s_979_);
if (lean_obj_tag(v_ty_x3f_986_) == 1)
{
lean_object* v_val_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1097_; 
v_val_1079_ = lean_ctor_get(v_ty_x3f_986_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_ty_x3f_986_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1081_ = v_ty_x3f_986_;
v_isShared_1082_ = v_isSharedCheck_1097_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_val_1079_);
lean_dec(v_ty_x3f_986_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1097_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1078_);
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1078_);
v___x_1084_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
uint8_t v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = 0;
v___x_1086_ = l_Lean_Elab_Tactic_elabTerm(v_val_1079_, v___x_1084_, v___x_1085_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref(v___x_1086_);
v_H_x27_1013_ = v_a_1087_;
v___y_1014_ = v___y_987_;
v___y_1015_ = v___y_988_;
v___y_1016_ = v___y_989_;
v___y_1017_ = v___y_990_;
v___y_1018_ = v___y_991_;
v___y_1019_ = v___y_992_;
v___y_1020_ = v___y_993_;
v___y_1021_ = v___y_994_;
goto v___jp_1012_;
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec_ref(v___x_1011_);
lean_del_object(v___x_1004_);
lean_dec_ref(v_proof_1002_);
lean_dec_ref(v_restHyps_1001_);
lean_dec_ref(v_focusHyp_1000_);
lean_del_object(v___x_998_);
lean_dec(v_fst_985_);
lean_dec_ref(v___x_984_);
lean_dec_ref(v_target_983_);
lean_dec(v___x_982_);
lean_dec_ref(v_hyps_981_);
lean_dec_ref(v_00_u03c3s_979_);
lean_dec(v___x_978_);
lean_dec(v___x_977_);
lean_dec(v_u_976_);
v_a_1088_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1086_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1086_);
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
}
else
{
lean_object* v___x_1098_; uint8_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v_ty_x3f_986_);
v___x_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1078_);
v___x_1099_ = 0;
v___x_1100_ = lean_box(0);
v___x_1101_ = l_Lean_Meta_mkFreshExprMVar(v___x_1098_, v___x_1099_, v___x_1100_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref(v___x_1101_);
v_H_x27_1013_ = v_a_1102_;
v___y_1014_ = v___y_987_;
v___y_1015_ = v___y_988_;
v___y_1016_ = v___y_989_;
v___y_1017_ = v___y_990_;
v___y_1018_ = v___y_991_;
v___y_1019_ = v___y_992_;
v___y_1020_ = v___y_993_;
v___y_1021_ = v___y_994_;
goto v___jp_1012_;
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec_ref(v___x_1011_);
lean_del_object(v___x_1004_);
lean_dec_ref(v_proof_1002_);
lean_dec_ref(v_restHyps_1001_);
lean_dec_ref(v_focusHyp_1000_);
lean_del_object(v___x_998_);
lean_dec(v_fst_985_);
lean_dec_ref(v___x_984_);
lean_dec_ref(v_target_983_);
lean_dec(v___x_982_);
lean_dec_ref(v_hyps_981_);
lean_dec_ref(v_00_u03c3s_979_);
lean_dec(v___x_978_);
lean_dec(v___x_977_);
lean_dec(v_u_976_);
v_a_1103_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1101_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1101_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
v___jp_1012_:
{
lean_object* v___x_1022_; lean_object* v_a_1023_; lean_object* v___x_1025_; 
v___x_1022_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_1021_);
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref(v___x_1022_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 2, v_H_x27_1013_);
lean_ctor_set(v___x_1004_, 1, v_a_1023_);
lean_ctor_set(v___x_1004_, 0, v___x_977_);
v___x_1025_ = v___x_1004_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_a_1023_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_H_x27_1013_);
v___x_1025_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; 
lean_inc_ref(v___x_1025_);
lean_inc_ref(v_00_u03c3s_979_);
v___x_1026_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v___x_978_, v_00_u03c3s_979_, v___x_1025_, v___x_980_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
lean_dec_ref(v___x_1026_);
v___x_1027_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1025_);
lean_inc_ref(v___x_1027_);
lean_inc_ref(v_hyps_981_);
lean_inc_ref(v_00_u03c3s_979_);
lean_inc(v_u_976_);
v___x_1028_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1028_, 0, v_u_976_);
lean_ctor_set(v___x_1028_, 1, v_00_u03c3s_979_);
lean_ctor_set(v___x_1028_, 2, v_hyps_981_);
lean_ctor_set(v___x_1028_, 3, v___x_1027_);
v___x_1029_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1028_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1029_);
v___x_1031_ = v___x_998_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
uint8_t v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = 0;
v___x_1033_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v___x_982_, v___x_1031_, v___x_1032_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1035_; lean_object* v_fst_1036_; lean_object* v_snd_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1066_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref(v___x_1033_);
lean_inc_ref(v___x_1027_);
lean_inc_ref(v_restHyps_1001_);
lean_inc_ref(v_00_u03c3s_979_);
lean_inc(v_u_976_);
v___x_1035_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_976_, v_00_u03c3s_979_, v_restHyps_1001_, v___x_1027_);
v_fst_1036_ = lean_ctor_get(v___x_1035_, 0);
v_snd_1037_ = lean_ctor_get(v___x_1035_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1039_ = v___x_1035_;
v_isShared_1040_ = v_isSharedCheck_1066_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_snd_1037_);
lean_inc(v_fst_1036_);
lean_dec(v___x_1035_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1066_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_inc_ref(v_target_983_);
lean_inc(v_fst_1036_);
lean_inc_ref(v_00_u03c3s_979_);
v___x_1041_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1041_, 0, v_u_976_);
lean_ctor_set(v___x_1041_, 1, v_00_u03c3s_979_);
lean_ctor_set(v___x_1041_, 2, v_fst_1036_);
lean_ctor_set(v___x_1041_, 3, v_target_983_);
v___x_1042_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1041_);
v___x_1043_ = lean_box(0);
v___x_1044_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1042_, v___x_1043_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc_n(v_a_1045_, 2);
lean_dec_ref(v___x_1044_);
v___x_1046_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3));
v___x_1047_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___closed__0));
v___x_1048_ = l_Lean_Name_mkStr6(v___x_1006_, v___x_1007_, v___x_1008_, v___x_984_, v___x_1046_, v___x_1047_);
v___x_1049_ = l_Lean_mkConst(v___x_1048_, v___x_1011_);
v___x_1050_ = l_Lean_mkApp10(v___x_1049_, v_00_u03c3s_979_, v_restHyps_1001_, v_focusHyp_1000_, v___x_1027_, v_hyps_981_, v_fst_1036_, v_target_983_, v_proof_1002_, v_snd_1037_, v_a_1034_);
v___x_1051_ = l_Lean_Expr_app___override(v___x_1050_, v_a_1045_);
v___x_1052_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_985_, v___x_1051_, v___y_1019_);
lean_dec_ref(v___x_1052_);
v___x_1053_ = l_Lean_Expr_mvarId_x21(v_a_1045_);
lean_dec(v_a_1045_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set_tag(v___x_1039_, 1);
lean_ctor_set(v___x_1039_, 1, v___x_1010_);
lean_ctor_set(v___x_1039_, 0, v___x_1053_);
v___x_1055_ = v___x_1039_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v___x_1010_);
v___x_1055_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1055_, v___y_1015_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
return v___x_1056_;
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_del_object(v___x_1039_);
lean_dec(v_snd_1037_);
lean_dec(v_fst_1036_);
lean_dec(v_a_1034_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1011_);
lean_dec_ref(v_proof_1002_);
lean_dec_ref(v_restHyps_1001_);
lean_dec_ref(v_focusHyp_1000_);
lean_dec(v_fst_985_);
lean_dec_ref(v___x_984_);
lean_dec_ref(v_target_983_);
lean_dec_ref(v_hyps_981_);
lean_dec_ref(v_00_u03c3s_979_);
v_a_1058_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1044_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1044_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1011_);
lean_dec_ref(v_proof_1002_);
lean_dec_ref(v_restHyps_1001_);
lean_dec_ref(v_focusHyp_1000_);
lean_dec(v_fst_985_);
lean_dec_ref(v___x_984_);
lean_dec_ref(v_target_983_);
lean_dec_ref(v_hyps_981_);
lean_dec_ref(v_00_u03c3s_979_);
lean_dec(v_u_976_);
v_a_1067_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1033_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1033_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1025_);
lean_dec_ref(v___x_1011_);
lean_dec_ref(v_proof_1002_);
lean_dec_ref(v_restHyps_1001_);
lean_dec_ref(v_focusHyp_1000_);
lean_del_object(v___x_998_);
lean_dec(v_fst_985_);
lean_dec_ref(v___x_984_);
lean_dec_ref(v_target_983_);
lean_dec(v___x_982_);
lean_dec_ref(v_hyps_981_);
lean_dec_ref(v_00_u03c3s_979_);
lean_dec(v_u_976_);
return v___x_1026_;
}
}
}
}
}
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec(v_ty_x3f_986_);
lean_dec(v_fst_985_);
lean_dec_ref(v___x_984_);
lean_dec_ref(v_target_983_);
lean_dec(v___x_982_);
lean_dec_ref(v_hyps_981_);
lean_dec_ref(v_00_u03c3s_979_);
lean_dec(v___x_977_);
lean_dec(v_u_976_);
lean_dec(v___x_975_);
v___x_1113_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6);
v___x_1114_ = l_Lean_MessageData_ofSyntax(v___x_978_);
v___x_1115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1113_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8);
v___x_1117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1115_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v___x_1117_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
return v___x_1118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___boxed(lean_object** _args){
lean_object* v___x_1119_ = _args[0];
lean_object* v_u_1120_ = _args[1];
lean_object* v___x_1121_ = _args[2];
lean_object* v___x_1122_ = _args[3];
lean_object* v_00_u03c3s_1123_ = _args[4];
lean_object* v___x_1124_ = _args[5];
lean_object* v_hyps_1125_ = _args[6];
lean_object* v___x_1126_ = _args[7];
lean_object* v_target_1127_ = _args[8];
lean_object* v___x_1128_ = _args[9];
lean_object* v_fst_1129_ = _args[10];
lean_object* v_ty_x3f_1130_ = _args[11];
lean_object* v___y_1131_ = _args[12];
lean_object* v___y_1132_ = _args[13];
lean_object* v___y_1133_ = _args[14];
lean_object* v___y_1134_ = _args[15];
lean_object* v___y_1135_ = _args[16];
lean_object* v___y_1136_ = _args[17];
lean_object* v___y_1137_ = _args[18];
lean_object* v___y_1138_ = _args[19];
lean_object* v___y_1139_ = _args[20];
_start:
{
uint8_t v___x_3611__boxed_1140_; lean_object* v_res_1141_; 
v___x_3611__boxed_1140_ = lean_unbox(v___x_1124_);
v_res_1141_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0(v___x_1119_, v_u_1120_, v___x_1121_, v___x_1122_, v_00_u03c3s_1123_, v___x_3611__boxed_1140_, v_hyps_1125_, v___x_1126_, v_target_1127_, v___x_1128_, v_fst_1129_, v_ty_x3f_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace(lean_object* v_x_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1158_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2));
v___x_1159_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1));
lean_inc(v_x_1148_);
v___x_1160_ = l_Lean_Syntax_isOfKind(v_x_1148_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
lean_dec(v_x_1148_);
v___x_1161_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_1161_;
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v_ty_x3f_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1162_ = lean_unsigned_to_nat(1u);
v___x_1163_ = l_Lean_Syntax_getArg(v_x_1148_, v___x_1162_);
v___x_1197_ = lean_unsigned_to_nat(2u);
v___x_1198_ = l_Lean_Syntax_getArg(v_x_1148_, v___x_1197_);
v___x_1199_ = l_Lean_Syntax_isNone(v___x_1198_);
if (v___x_1199_ == 0)
{
uint8_t v___x_1200_; 
lean_inc(v___x_1198_);
v___x_1200_ = l_Lean_Syntax_matchesNull(v___x_1198_, v___x_1197_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; 
lean_dec(v___x_1198_);
lean_dec(v___x_1163_);
lean_dec(v_x_1148_);
v___x_1201_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_1201_;
}
else
{
lean_object* v_ty_x3f_1202_; lean_object* v___x_1203_; 
v_ty_x3f_1202_ = l_Lean_Syntax_getArg(v___x_1198_, v___x_1162_);
lean_dec(v___x_1198_);
v___x_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1203_, 0, v_ty_x3f_1202_);
v_ty_x3f_1165_ = v___x_1203_;
v___y_1166_ = v_a_1149_;
v___y_1167_ = v_a_1150_;
v___y_1168_ = v_a_1151_;
v___y_1169_ = v_a_1152_;
v___y_1170_ = v_a_1153_;
v___y_1171_ = v_a_1154_;
v___y_1172_ = v_a_1155_;
v___y_1173_ = v_a_1156_;
goto v___jp_1164_;
}
}
else
{
lean_object* v___x_1204_; 
lean_dec(v___x_1198_);
v___x_1204_ = lean_box(0);
v_ty_x3f_1165_ = v___x_1204_;
v___y_1166_ = v_a_1149_;
v___y_1167_ = v_a_1150_;
v___y_1168_ = v_a_1151_;
v___y_1169_ = v_a_1152_;
v___y_1170_ = v_a_1153_;
v___y_1171_ = v_a_1154_;
v___y_1172_ = v_a_1155_;
v___y_1173_ = v_a_1156_;
goto v___jp_1164_;
}
v___jp_1164_:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v_snd_1176_; lean_object* v_fst_1177_; lean_object* v_u_1178_; lean_object* v_00_u03c3s_1179_; lean_object* v_hyps_1180_; lean_object* v_target_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___y_1187_; lean_object* v___x_1188_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref(v___x_1174_);
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
v___x_1182_ = lean_unsigned_to_nat(4u);
v___x_1183_ = l_Lean_Syntax_getArg(v_x_1148_, v___x_1182_);
lean_dec(v_x_1148_);
v___x_1184_ = l_Lean_Syntax_getId(v___x_1163_);
v___x_1185_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_1176_, v___x_1184_);
v___x_1186_ = lean_box(v___x_1160_);
v___y_1187_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___boxed), 21, 12);
lean_closure_set(v___y_1187_, 0, v___x_1185_);
lean_closure_set(v___y_1187_, 1, v_u_1178_);
lean_closure_set(v___y_1187_, 2, v___x_1184_);
lean_closure_set(v___y_1187_, 3, v___x_1163_);
lean_closure_set(v___y_1187_, 4, v_00_u03c3s_1179_);
lean_closure_set(v___y_1187_, 5, v___x_1186_);
lean_closure_set(v___y_1187_, 6, v_hyps_1180_);
lean_closure_set(v___y_1187_, 7, v___x_1183_);
lean_closure_set(v___y_1187_, 8, v_target_1181_);
lean_closure_set(v___y_1187_, 9, v___x_1158_);
lean_closure_set(v___y_1187_, 10, v_fst_1177_);
lean_closure_set(v___y_1187_, 11, v_ty_x3f_1165_);
v___x_1188_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_1177_, v___y_1187_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
return v___x_1188_;
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec(v_ty_x3f_1165_);
lean_dec(v___x_1163_);
lean_dec(v_x_1148_);
v_a_1189_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1174_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1174_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___boxed(lean_object* v_x_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace(v_x_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1(){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1225_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1226_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1));
v___x_1227_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1));
v___x_1228_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___boxed), 10, 0);
v___x_1229_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1225_, v___x_1226_, v___x_1227_, v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___boxed(lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1();
return v_res_1231_;
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
