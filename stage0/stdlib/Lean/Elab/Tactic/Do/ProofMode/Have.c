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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(lean_object* v_x_206_, size_t v_x_207_, size_t v_x_208_, lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
if (lean_obj_tag(v_x_206_) == 0)
{
lean_object* v_es_211_; size_t v___x_212_; size_t v___x_213_; lean_object* v_j_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_es_211_ = lean_ctor_get(v_x_206_, 0);
v___x_212_ = ((size_t)31ULL);
v___x_213_ = lean_usize_land(v_x_207_, v___x_212_);
v_j_214_ = lean_usize_to_nat(v___x_213_);
v___x_215_ = lean_array_get_size(v_es_211_);
v___x_216_ = lean_nat_dec_lt(v_j_214_, v___x_215_);
if (v___x_216_ == 0)
{
lean_dec(v_j_214_);
lean_dec(v_x_210_);
lean_dec(v_x_209_);
return v_x_206_;
}
else
{
lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_255_; 
lean_inc_ref(v_es_211_);
v_isSharedCheck_255_ = !lean_is_exclusive(v_x_206_);
if (v_isSharedCheck_255_ == 0)
{
lean_object* v_unused_256_; 
v_unused_256_ = lean_ctor_get(v_x_206_, 0);
lean_dec(v_unused_256_);
v___x_218_ = v_x_206_;
v_isShared_219_ = v_isSharedCheck_255_;
goto v_resetjp_217_;
}
else
{
lean_dec(v_x_206_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_255_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v_v_220_; lean_object* v___x_221_; lean_object* v_xs_x27_222_; lean_object* v___y_224_; 
v_v_220_ = lean_array_fget(v_es_211_, v_j_214_);
v___x_221_ = lean_box(0);
v_xs_x27_222_ = lean_array_fset(v_es_211_, v_j_214_, v___x_221_);
switch(lean_obj_tag(v_v_220_))
{
case 0:
{
lean_object* v_key_229_; lean_object* v_val_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_240_; 
v_key_229_ = lean_ctor_get(v_v_220_, 0);
v_val_230_ = lean_ctor_get(v_v_220_, 1);
v_isSharedCheck_240_ = !lean_is_exclusive(v_v_220_);
if (v_isSharedCheck_240_ == 0)
{
v___x_232_ = v_v_220_;
v_isShared_233_ = v_isSharedCheck_240_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_val_230_);
lean_inc(v_key_229_);
lean_dec(v_v_220_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_240_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
uint8_t v___x_234_; 
v___x_234_ = l_Lean_instBEqMVarId_beq(v_x_209_, v_key_229_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_del_object(v___x_232_);
v___x_235_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_229_, v_val_230_, v_x_209_, v_x_210_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
v___y_224_ = v___x_236_;
goto v___jp_223_;
}
else
{
lean_object* v___x_238_; 
lean_dec(v_val_230_);
lean_dec(v_key_229_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 1, v_x_210_);
lean_ctor_set(v___x_232_, 0, v_x_209_);
v___x_238_ = v___x_232_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_x_209_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_x_210_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
v___y_224_ = v___x_238_;
goto v___jp_223_;
}
}
}
}
case 1:
{
lean_object* v_node_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_253_; 
v_node_241_ = lean_ctor_get(v_v_220_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v_v_220_);
if (v_isSharedCheck_253_ == 0)
{
v___x_243_ = v_v_220_;
v_isShared_244_ = v_isSharedCheck_253_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_node_241_);
lean_dec(v_v_220_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_253_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_245_ = ((size_t)5ULL);
v___x_246_ = lean_usize_shift_right(v_x_207_, v___x_245_);
v___x_247_ = ((size_t)1ULL);
v___x_248_ = lean_usize_add(v_x_208_, v___x_247_);
v___x_249_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_node_241_, v___x_246_, v___x_248_, v_x_209_, v_x_210_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_249_);
v___x_251_ = v___x_243_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
v___y_224_ = v___x_251_;
goto v___jp_223_;
}
}
}
default: 
{
lean_object* v___x_254_; 
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v_x_209_);
lean_ctor_set(v___x_254_, 1, v_x_210_);
v___y_224_ = v___x_254_;
goto v___jp_223_;
}
}
v___jp_223_:
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = lean_array_fset(v_xs_x27_222_, v_j_214_, v___y_224_);
lean_dec(v_j_214_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_225_);
v___x_227_ = v___x_218_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
else
{
lean_object* v_ks_257_; lean_object* v_vs_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_278_; 
v_ks_257_ = lean_ctor_get(v_x_206_, 0);
v_vs_258_ = lean_ctor_get(v_x_206_, 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_x_206_);
if (v_isSharedCheck_278_ == 0)
{
v___x_260_ = v_x_206_;
v_isShared_261_ = v_isSharedCheck_278_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_vs_258_);
lean_inc(v_ks_257_);
lean_dec(v_x_206_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_278_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_ks_257_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_vs_258_);
v___x_263_ = v_reuseFailAlloc_277_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v_newNode_264_; uint8_t v___y_266_; size_t v___x_272_; uint8_t v___x_273_; 
v_newNode_264_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(v___x_263_, v_x_209_, v_x_210_);
v___x_272_ = ((size_t)7ULL);
v___x_273_ = lean_usize_dec_le(v___x_272_, v_x_208_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_274_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_264_);
v___x_275_ = lean_unsigned_to_nat(4u);
v___x_276_ = lean_nat_dec_lt(v___x_274_, v___x_275_);
lean_dec(v___x_274_);
v___y_266_ = v___x_276_;
goto v___jp_265_;
}
else
{
v___y_266_ = v___x_273_;
goto v___jp_265_;
}
v___jp_265_:
{
if (v___y_266_ == 0)
{
lean_object* v_ks_267_; lean_object* v_vs_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_ks_267_ = lean_ctor_get(v_newNode_264_, 0);
lean_inc_ref(v_ks_267_);
v_vs_268_ = lean_ctor_get(v_newNode_264_, 1);
lean_inc_ref(v_vs_268_);
lean_dec_ref(v_newNode_264_);
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_271_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_x_208_, v_ks_267_, v_vs_268_, v___x_269_, v___x_270_);
lean_dec_ref(v_vs_268_);
lean_dec_ref(v_ks_267_);
return v___x_271_;
}
else
{
return v_newNode_264_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(size_t v_depth_279_, lean_object* v_keys_280_, lean_object* v_vals_281_, lean_object* v_i_282_, lean_object* v_entries_283_){
_start:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_array_get_size(v_keys_280_);
v___x_285_ = lean_nat_dec_lt(v_i_282_, v___x_284_);
if (v___x_285_ == 0)
{
lean_dec(v_i_282_);
return v_entries_283_;
}
else
{
lean_object* v_k_286_; lean_object* v_v_287_; uint64_t v___x_288_; size_t v_h_289_; size_t v___x_290_; lean_object* v___x_291_; size_t v___x_292_; size_t v___x_293_; size_t v___x_294_; size_t v_h_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_k_286_ = lean_array_fget_borrowed(v_keys_280_, v_i_282_);
v_v_287_ = lean_array_fget_borrowed(v_vals_281_, v_i_282_);
v___x_288_ = l_Lean_instHashableMVarId_hash(v_k_286_);
v_h_289_ = lean_uint64_to_usize(v___x_288_);
v___x_290_ = ((size_t)5ULL);
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = ((size_t)1ULL);
v___x_293_ = lean_usize_sub(v_depth_279_, v___x_292_);
v___x_294_ = lean_usize_mul(v___x_290_, v___x_293_);
v_h_295_ = lean_usize_shift_right(v_h_289_, v___x_294_);
v___x_296_ = lean_nat_add(v_i_282_, v___x_291_);
lean_dec(v_i_282_);
lean_inc(v_v_287_);
lean_inc(v_k_286_);
v___x_297_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_entries_283_, v_h_295_, v_depth_279_, v_k_286_, v_v_287_);
v_i_282_ = v___x_296_;
v_entries_283_ = v___x_297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_299_, lean_object* v_keys_300_, lean_object* v_vals_301_, lean_object* v_i_302_, lean_object* v_entries_303_){
_start:
{
size_t v_depth_boxed_304_; lean_object* v_res_305_; 
v_depth_boxed_304_ = lean_unbox_usize(v_depth_299_);
lean_dec(v_depth_299_);
v_res_305_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_boxed_304_, v_keys_300_, v_vals_301_, v_i_302_, v_entries_303_);
lean_dec_ref(v_vals_301_);
lean_dec_ref(v_keys_300_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
size_t v_x_7743__boxed_311_; size_t v_x_7744__boxed_312_; lean_object* v_res_313_; 
v_x_7743__boxed_311_ = lean_unbox_usize(v_x_307_);
lean_dec(v_x_307_);
v_x_7744__boxed_312_ = lean_unbox_usize(v_x_308_);
lean_dec(v_x_308_);
v_res_313_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_306_, v_x_7743__boxed_311_, v_x_7744__boxed_312_, v_x_309_, v_x_310_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(lean_object* v_x_314_, lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
uint64_t v___x_317_; size_t v___x_318_; size_t v___x_319_; lean_object* v___x_320_; 
v___x_317_ = l_Lean_instHashableMVarId_hash(v_x_315_);
v___x_318_ = lean_uint64_to_usize(v___x_317_);
v___x_319_ = ((size_t)1ULL);
v___x_320_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_314_, v___x_318_, v___x_319_, v_x_315_, v_x_316_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(lean_object* v_mvarId_321_, lean_object* v_val_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; lean_object* v_mctx_326_; lean_object* v_cache_327_; lean_object* v_zetaDeltaFVarIds_328_; lean_object* v_postponed_329_; lean_object* v_diag_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_358_; 
v___x_325_ = lean_st_ref_take(v___y_323_);
v_mctx_326_ = lean_ctor_get(v___x_325_, 0);
v_cache_327_ = lean_ctor_get(v___x_325_, 1);
v_zetaDeltaFVarIds_328_ = lean_ctor_get(v___x_325_, 2);
v_postponed_329_ = lean_ctor_get(v___x_325_, 3);
v_diag_330_ = lean_ctor_get(v___x_325_, 4);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_358_ == 0)
{
v___x_332_ = v___x_325_;
v_isShared_333_ = v_isSharedCheck_358_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_diag_330_);
lean_inc(v_postponed_329_);
lean_inc(v_zetaDeltaFVarIds_328_);
lean_inc(v_cache_327_);
lean_inc(v_mctx_326_);
lean_dec(v___x_325_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_358_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v_depth_334_; lean_object* v_levelAssignDepth_335_; lean_object* v_lmvarCounter_336_; lean_object* v_mvarCounter_337_; lean_object* v_lDecls_338_; lean_object* v_decls_339_; lean_object* v_userNames_340_; lean_object* v_lAssignment_341_; lean_object* v_eAssignment_342_; lean_object* v_dAssignment_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_357_; 
v_depth_334_ = lean_ctor_get(v_mctx_326_, 0);
v_levelAssignDepth_335_ = lean_ctor_get(v_mctx_326_, 1);
v_lmvarCounter_336_ = lean_ctor_get(v_mctx_326_, 2);
v_mvarCounter_337_ = lean_ctor_get(v_mctx_326_, 3);
v_lDecls_338_ = lean_ctor_get(v_mctx_326_, 4);
v_decls_339_ = lean_ctor_get(v_mctx_326_, 5);
v_userNames_340_ = lean_ctor_get(v_mctx_326_, 6);
v_lAssignment_341_ = lean_ctor_get(v_mctx_326_, 7);
v_eAssignment_342_ = lean_ctor_get(v_mctx_326_, 8);
v_dAssignment_343_ = lean_ctor_get(v_mctx_326_, 9);
v_isSharedCheck_357_ = !lean_is_exclusive(v_mctx_326_);
if (v_isSharedCheck_357_ == 0)
{
v___x_345_ = v_mctx_326_;
v_isShared_346_ = v_isSharedCheck_357_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_dAssignment_343_);
lean_inc(v_eAssignment_342_);
lean_inc(v_lAssignment_341_);
lean_inc(v_userNames_340_);
lean_inc(v_decls_339_);
lean_inc(v_lDecls_338_);
lean_inc(v_mvarCounter_337_);
lean_inc(v_lmvarCounter_336_);
lean_inc(v_levelAssignDepth_335_);
lean_inc(v_depth_334_);
lean_dec(v_mctx_326_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_357_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_347_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(v_eAssignment_342_, v_mvarId_321_, v_val_322_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 8, v___x_347_);
v___x_349_ = v___x_345_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_depth_334_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_levelAssignDepth_335_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_lmvarCounter_336_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v_mvarCounter_337_);
lean_ctor_set(v_reuseFailAlloc_356_, 4, v_lDecls_338_);
lean_ctor_set(v_reuseFailAlloc_356_, 5, v_decls_339_);
lean_ctor_set(v_reuseFailAlloc_356_, 6, v_userNames_340_);
lean_ctor_set(v_reuseFailAlloc_356_, 7, v_lAssignment_341_);
lean_ctor_set(v_reuseFailAlloc_356_, 8, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_356_, 9, v_dAssignment_343_);
v___x_349_ = v_reuseFailAlloc_356_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_351_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_349_);
v___x_351_ = v___x_332_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_cache_327_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_zetaDeltaFVarIds_328_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v_postponed_329_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v_diag_330_);
v___x_351_ = v_reuseFailAlloc_355_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_st_ref_set(v___y_323_, v___x_351_);
v___x_353_ = lean_box(0);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg___boxed(lean_object* v_mvarId_359_, lean_object* v_val_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_mvarId_359_, v_val_360_, v___y_361_);
lean_dec(v___y_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(lean_object* v_msgData_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v___x_370_; lean_object* v_env_371_; lean_object* v___x_372_; lean_object* v_mctx_373_; lean_object* v_lctx_374_; lean_object* v_options_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_370_ = lean_st_ref_get(v___y_368_);
v_env_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc_ref(v_env_371_);
lean_dec(v___x_370_);
v___x_372_ = lean_st_ref_get(v___y_366_);
v_mctx_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc_ref(v_mctx_373_);
lean_dec(v___x_372_);
v_lctx_374_ = lean_ctor_get(v___y_365_, 2);
v_options_375_ = lean_ctor_get(v___y_367_, 2);
lean_inc_ref(v_options_375_);
lean_inc_ref(v_lctx_374_);
v___x_376_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_376_, 0, v_env_371_);
lean_ctor_set(v___x_376_, 1, v_mctx_373_);
lean_ctor_set(v___x_376_, 2, v_lctx_374_);
lean_ctor_set(v___x_376_, 3, v_options_375_);
v___x_377_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v_msgData_364_);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4___boxed(lean_object* v_msgData_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(v_msgData_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(lean_object* v_msg_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_ref_392_; lean_object* v___x_393_; lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_402_; 
v_ref_392_ = lean_ctor_get(v___y_389_, 5);
v___x_393_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(v_msg_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_402_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_400_; 
lean_inc(v_ref_392_);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v_ref_392_);
lean_ctor_set(v___x_398_, 1, v_a_394_);
if (v_isShared_397_ == 0)
{
lean_ctor_set_tag(v___x_396_, 1);
lean_ctor_set(v___x_396_, 0, v___x_398_);
v___x_400_ = v___x_396_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg___boxed(lean_object* v_msg_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v_msg_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_409_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__5));
v___x_417_ = l_Lean_stringToMessageData(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__7));
v___x_420_ = l_Lean_stringToMessageData(v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0(lean_object* v___x_421_, lean_object* v_snd_422_, lean_object* v___x_423_, lean_object* v___x_424_, uint8_t v___x_425_, lean_object* v___x_426_, lean_object* v_fst_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
if (lean_obj_tag(v___x_421_) == 1)
{
lean_object* v_val_437_; lean_object* v___x_438_; lean_object* v_a_439_; lean_object* v_focusHyp_440_; lean_object* v_restHyps_441_; lean_object* v_proof_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_491_; 
v_val_437_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_val_437_);
lean_dec_ref_known(v___x_421_, 1);
v___x_438_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_435_);
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref(v___x_438_);
v_focusHyp_440_ = lean_ctor_get(v_val_437_, 0);
v_restHyps_441_ = lean_ctor_get(v_val_437_, 1);
v_proof_442_ = lean_ctor_get(v_val_437_, 2);
v_isSharedCheck_491_ = !lean_is_exclusive(v_val_437_);
if (v_isSharedCheck_491_ == 0)
{
v___x_444_ = v_val_437_;
v_isShared_445_ = v_isSharedCheck_491_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_proof_442_);
lean_inc(v_restHyps_441_);
lean_inc(v_focusHyp_440_);
lean_dec(v_val_437_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_491_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_u_446_; lean_object* v_00_u03c3s_447_; lean_object* v_hyps_448_; lean_object* v_target_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_490_; 
v_u_446_ = lean_ctor_get(v_snd_422_, 0);
v_00_u03c3s_447_ = lean_ctor_get(v_snd_422_, 1);
v_hyps_448_ = lean_ctor_get(v_snd_422_, 2);
v_target_449_ = lean_ctor_get(v_snd_422_, 3);
v_isSharedCheck_490_ = !lean_is_exclusive(v_snd_422_);
if (v_isSharedCheck_490_ == 0)
{
v___x_451_ = v_snd_422_;
v_isShared_452_ = v_isSharedCheck_490_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_target_449_);
lean_inc(v_hyps_448_);
lean_inc(v_00_u03c3s_447_);
lean_inc(v_u_446_);
lean_dec(v_snd_422_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_490_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_453_ = l_Lean_Syntax_getId(v___x_423_);
v___x_454_ = l_Lean_Expr_consumeMData(v_focusHyp_440_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 2, v___x_454_);
lean_ctor_set(v___x_444_, 1, v_a_439_);
lean_ctor_set(v___x_444_, 0, v___x_453_);
v___x_456_ = v___x_444_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_a_439_);
lean_ctor_set(v_reuseFailAlloc_489_, 2, v___x_454_);
v___x_456_ = v_reuseFailAlloc_489_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; 
lean_inc_ref(v___x_456_);
lean_inc_ref(v_00_u03c3s_447_);
v___x_457_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v___x_424_, v_00_u03c3s_447_, v___x_456_, v___x_425_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
lean_dec_ref_known(v___x_457_, 1);
v___x_458_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_456_);
lean_inc_ref(v_hyps_448_);
lean_inc_ref_n(v_00_u03c3s_447_, 2);
lean_inc_n(v_u_446_, 2);
v___x_459_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_446_, v_00_u03c3s_447_, v_hyps_448_, v___x_458_);
lean_inc_ref(v_target_449_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 2, v___x_459_);
v___x_461_ = v___x_451_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_u_446_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_00_u03c3s_447_);
lean_ctor_set(v_reuseFailAlloc_488_, 2, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_488_, 3, v_target_449_);
v___x_461_ = v_reuseFailAlloc_488_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_461_);
v___x_463_ = lean_box(0);
v___x_464_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_462_, v___x_463_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc_n(v_a_465_, 2);
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0));
v___x_467_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1));
v___x_468_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2));
v___x_469_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3));
v___x_470_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__4));
v___x_471_ = l_Lean_Name_mkStr6(v___x_466_, v___x_467_, v___x_468_, v___x_426_, v___x_469_, v___x_470_);
v___x_472_ = lean_box(0);
v___x_473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_473_, 0, v_u_446_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = l_Lean_mkConst(v___x_471_, v___x_473_);
v___x_475_ = l_Lean_mkApp7(v___x_474_, v_00_u03c3s_447_, v_hyps_448_, v_restHyps_441_, v_focusHyp_440_, v_target_449_, v_proof_442_, v_a_465_);
v___x_476_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_427_, v___x_475_, v___y_433_);
lean_dec_ref(v___x_476_);
v___x_477_ = l_Lean_Expr_mvarId_x21(v_a_465_);
lean_dec(v_a_465_);
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v___x_472_);
v___x_479_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_478_, v___y_429_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
return v___x_479_;
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec_ref(v_target_449_);
lean_dec_ref(v_hyps_448_);
lean_dec_ref(v_00_u03c3s_447_);
lean_dec(v_u_446_);
lean_dec_ref(v_proof_442_);
lean_dec_ref(v_restHyps_441_);
lean_dec_ref(v_focusHyp_440_);
lean_dec(v_fst_427_);
lean_dec_ref(v___x_426_);
v_a_480_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_464_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_464_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_456_);
lean_del_object(v___x_451_);
lean_dec_ref(v_target_449_);
lean_dec_ref(v_hyps_448_);
lean_dec_ref(v_00_u03c3s_447_);
lean_dec(v_u_446_);
lean_dec_ref(v_proof_442_);
lean_dec_ref(v_restHyps_441_);
lean_dec_ref(v_focusHyp_440_);
lean_dec(v_fst_427_);
lean_dec_ref(v___x_426_);
return v___x_457_;
}
}
}
}
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v_fst_427_);
lean_dec_ref(v___x_426_);
lean_dec_ref(v_snd_422_);
lean_dec(v___x_421_);
v___x_492_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6);
v___x_493_ = l_Lean_MessageData_ofSyntax(v___x_424_);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8);
v___x_496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v___x_496_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___boxed(lean_object* v___x_498_, lean_object* v_snd_499_, lean_object* v___x_500_, lean_object* v___x_501_, lean_object* v___x_502_, lean_object* v___x_503_, lean_object* v_fst_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
uint8_t v___x_8043__boxed_514_; lean_object* v_res_515_; 
v___x_8043__boxed_514_ = lean_unbox(v___x_502_);
v_res_515_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0(v___x_498_, v_snd_499_, v___x_500_, v___x_501_, v___x_8043__boxed_514_, v___x_503_, v_fst_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___x_500_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup(lean_object* v_x_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_538_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2));
v___x_539_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4));
lean_inc(v_x_528_);
v___x_540_ = l_Lean_Syntax_isOfKind(v_x_528_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
lean_dec(v_x_528_);
v___x_541_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_541_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = l_Lean_Syntax_getArg(v_x_528_, v___x_542_);
v___x_544_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__6));
lean_inc(v___x_543_);
v___x_545_ = l_Lean_Syntax_isOfKind(v___x_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
lean_dec(v___x_543_);
lean_dec(v_x_528_);
v___x_546_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_547_ = lean_unsigned_to_nat(3u);
v___x_548_ = l_Lean_Syntax_getArg(v_x_528_, v___x_547_);
lean_dec(v_x_528_);
lean_inc(v___x_548_);
v___x_549_ = l_Lean_Syntax_isOfKind(v___x_548_, v___x_544_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
lean_dec(v___x_548_);
lean_dec(v___x_543_);
v___x_550_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_550_;
}
else
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v_fst_553_; lean_object* v_snd_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___y_558_; lean_object* v___x_559_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v___x_551_, 1);
v_fst_553_ = lean_ctor_get(v_a_552_, 0);
lean_inc_n(v_fst_553_, 2);
v_snd_554_ = lean_ctor_get(v_a_552_, 1);
lean_inc_n(v_snd_554_, 2);
lean_dec(v_a_552_);
v___x_555_ = l_Lean_Syntax_getId(v___x_543_);
v___x_556_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_554_, v___x_555_);
lean_dec(v___x_555_);
v___x_557_ = lean_box(v___x_549_);
v___y_558_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___boxed), 16, 7);
lean_closure_set(v___y_558_, 0, v___x_556_);
lean_closure_set(v___y_558_, 1, v_snd_554_);
lean_closure_set(v___y_558_, 2, v___x_548_);
lean_closure_set(v___y_558_, 3, v___x_543_);
lean_closure_set(v___y_558_, 4, v___x_557_);
lean_closure_set(v___y_558_, 5, v___x_538_);
lean_closure_set(v___y_558_, 6, v_fst_553_);
v___x_559_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_553_, v___y_558_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
return v___x_559_;
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v___x_548_);
lean_dec(v___x_543_);
v_a_560_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_551_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_551_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___boxed(lean_object* v_x_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup(v_x_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2(lean_object* v_mvarId_579_, lean_object* v_val_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_mvarId_579_, v_val_580_, v___y_586_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___boxed(lean_object* v_mvarId_591_, lean_object* v_val_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2(v_mvarId_591_, v_val_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3(lean_object* v_00_u03b1_603_, lean_object* v_msg_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v_msg_604_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___boxed(lean_object* v_00_u03b1_615_, lean_object* v_msg_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3(v_00_u03b1_615_, v_msg_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2(lean_object* v_00_u03b2_627_, lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_x_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(v_x_628_, v_x_629_, v_x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_632_, lean_object* v_x_633_, size_t v_x_634_, size_t v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_633_, v_x_634_, v_x_635_, v_x_636_, v_x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_639_, lean_object* v_x_640_, lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v_x_644_){
_start:
{
size_t v_x_8380__boxed_645_; size_t v_x_8381__boxed_646_; lean_object* v_res_647_; 
v_x_8380__boxed_645_ = lean_unbox_usize(v_x_641_);
lean_dec(v_x_641_);
v_x_8381__boxed_646_ = lean_unbox_usize(v_x_642_);
lean_dec(v_x_642_);
v_res_647_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4(v_00_u03b2_639_, v_x_640_, v_x_8380__boxed_645_, v_x_8381__boxed_646_, v_x_643_, v_x_644_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_648_, lean_object* v_n_649_, lean_object* v_k_650_, lean_object* v_v_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(v_n_649_, v_k_650_, v_v_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_653_, size_t v_depth_654_, lean_object* v_keys_655_, lean_object* v_vals_656_, lean_object* v_heq_657_, lean_object* v_i_658_, lean_object* v_entries_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_654_, v_keys_655_, v_vals_656_, v_i_658_, v_entries_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_661_, lean_object* v_depth_662_, lean_object* v_keys_663_, lean_object* v_vals_664_, lean_object* v_heq_665_, lean_object* v_i_666_, lean_object* v_entries_667_){
_start:
{
size_t v_depth_boxed_668_; lean_object* v_res_669_; 
v_depth_boxed_668_ = lean_unbox_usize(v_depth_662_);
lean_dec(v_depth_662_);
v_res_669_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_661_, v_depth_boxed_668_, v_keys_663_, v_vals_664_, v_heq_665_, v_i_666_, v_entries_667_);
lean_dec_ref(v_vals_664_);
lean_dec_ref(v_keys_663_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_670_, lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_671_, v_x_672_, v_x_673_, v_x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1(){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_687_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_688_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4));
v___x_689_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3));
v___x_690_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___boxed), 10, 0);
v___x_691_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_687_, v___x_688_, v___x_689_, v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___boxed(lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1();
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0(lean_object* v___x_695_, lean_object* v_00_u03c3s_696_, uint8_t v___x_697_, lean_object* v_u_698_, lean_object* v_hyps_699_, lean_object* v___x_700_, lean_object* v_target_701_, lean_object* v___x_702_, lean_object* v___x_703_, lean_object* v___x_704_, lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v_fst_707_, lean_object* v_H_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; lean_object* v_a_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_718_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_716_);
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref(v___x_718_);
v___x_720_ = l_Lean_Syntax_getId(v___x_695_);
lean_inc_ref(v_H_708_);
v___x_721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v_a_719_);
lean_ctor_set(v___x_721_, 2, v_H_708_);
lean_inc_ref(v___x_721_);
lean_inc_ref(v_00_u03c3s_696_);
v___x_722_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v___x_695_, v_00_u03c3s_696_, v___x_721_, v___x_697_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_775_; 
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; 
v_unused_776_ = lean_ctor_get(v___x_722_, 0);
lean_dec(v_unused_776_);
v___x_724_ = v___x_722_;
v_isShared_725_ = v_isSharedCheck_775_;
goto v_resetjp_723_;
}
else
{
lean_dec(v___x_722_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_775_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v_fst_728_; lean_object* v_snd_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_774_; 
v___x_726_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_721_);
lean_inc_ref(v___x_726_);
lean_inc_ref(v_hyps_699_);
lean_inc_ref(v_00_u03c3s_696_);
lean_inc(v_u_698_);
v___x_727_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_698_, v_00_u03c3s_696_, v_hyps_699_, v___x_726_);
v_fst_728_ = lean_ctor_get(v___x_727_, 0);
v_snd_729_ = lean_ctor_get(v___x_727_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_774_ == 0)
{
v___x_731_ = v___x_727_;
v_isShared_732_ = v_isSharedCheck_774_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_snd_729_);
lean_inc(v_fst_728_);
lean_dec(v___x_727_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_774_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
lean_inc_ref(v_hyps_699_);
lean_inc_ref(v_00_u03c3s_696_);
lean_inc(v_u_698_);
v___x_733_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_733_, 0, v_u_698_);
lean_ctor_set(v___x_733_, 1, v_00_u03c3s_696_);
lean_ctor_set(v___x_733_, 2, v_hyps_699_);
lean_ctor_set(v___x_733_, 3, v_H_708_);
v___x_734_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_733_);
if (v_isShared_725_ == 0)
{
lean_ctor_set_tag(v___x_724_, 1);
lean_ctor_set(v___x_724_, 0, v___x_734_);
v___x_736_ = v___x_724_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_773_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
uint8_t v___x_737_; lean_object* v___x_738_; 
v___x_737_ = 0;
v___x_738_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v___x_700_, v___x_736_, v___x_737_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
lean_inc_ref(v_target_701_);
lean_inc(v_fst_728_);
lean_inc_ref(v_00_u03c3s_696_);
v___x_740_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_740_, 0, v_u_698_);
lean_ctor_set(v___x_740_, 1, v_00_u03c3s_696_);
lean_ctor_set(v___x_740_, 2, v_fst_728_);
lean_ctor_set(v___x_740_, 3, v_target_701_);
v___x_741_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_740_);
v___x_742_ = lean_box(0);
v___x_743_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_741_, v___x_742_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc_n(v_a_744_, 2);
lean_dec_ref_known(v___x_743_, 1);
v___x_745_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3));
v___x_746_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___closed__0));
v___x_747_ = l_Lean_Name_mkStr6(v___x_702_, v___x_703_, v___x_704_, v___x_705_, v___x_745_, v___x_746_);
v___x_748_ = l_Lean_mkConst(v___x_747_, v___x_706_);
v___x_749_ = l_Lean_mkApp8(v___x_748_, v_00_u03c3s_696_, v_hyps_699_, v___x_726_, v_fst_728_, v_target_701_, v_snd_729_, v_a_739_, v_a_744_);
v___x_750_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_707_, v___x_749_, v___y_714_);
lean_dec_ref(v___x_750_);
v___x_751_ = l_Lean_Expr_mvarId_x21(v_a_744_);
lean_dec(v_a_744_);
v___x_752_ = lean_box(0);
if (v_isShared_732_ == 0)
{
lean_ctor_set_tag(v___x_731_, 1);
lean_ctor_set(v___x_731_, 1, v___x_752_);
lean_ctor_set(v___x_731_, 0, v___x_751_);
v___x_754_ = v___x_731_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_752_);
v___x_754_ = v_reuseFailAlloc_756_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_754_, v___y_710_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
return v___x_755_;
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec(v_a_739_);
lean_del_object(v___x_731_);
lean_dec(v_snd_729_);
lean_dec(v_fst_728_);
lean_dec_ref(v___x_726_);
lean_dec(v_fst_707_);
lean_dec(v___x_706_);
lean_dec_ref(v___x_705_);
lean_dec_ref(v___x_704_);
lean_dec_ref(v___x_703_);
lean_dec_ref(v___x_702_);
lean_dec_ref(v_target_701_);
lean_dec_ref(v_hyps_699_);
lean_dec_ref(v_00_u03c3s_696_);
v_a_757_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_743_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_743_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_del_object(v___x_731_);
lean_dec(v_snd_729_);
lean_dec(v_fst_728_);
lean_dec_ref(v___x_726_);
lean_dec(v_fst_707_);
lean_dec(v___x_706_);
lean_dec_ref(v___x_705_);
lean_dec_ref(v___x_704_);
lean_dec_ref(v___x_703_);
lean_dec_ref(v___x_702_);
lean_dec_ref(v_target_701_);
lean_dec_ref(v_hyps_699_);
lean_dec(v_u_698_);
lean_dec_ref(v_00_u03c3s_696_);
v_a_765_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_738_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_738_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_721_, 3);
lean_dec_ref(v_H_708_);
lean_dec(v_fst_707_);
lean_dec(v___x_706_);
lean_dec_ref(v___x_705_);
lean_dec_ref(v___x_704_);
lean_dec_ref(v___x_703_);
lean_dec_ref(v___x_702_);
lean_dec_ref(v_target_701_);
lean_dec(v___x_700_);
lean_dec_ref(v_hyps_699_);
lean_dec(v_u_698_);
lean_dec_ref(v_00_u03c3s_696_);
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___boxed(lean_object** _args){
lean_object* v___x_777_ = _args[0];
lean_object* v_00_u03c3s_778_ = _args[1];
lean_object* v___x_779_ = _args[2];
lean_object* v_u_780_ = _args[3];
lean_object* v_hyps_781_ = _args[4];
lean_object* v___x_782_ = _args[5];
lean_object* v_target_783_ = _args[6];
lean_object* v___x_784_ = _args[7];
lean_object* v___x_785_ = _args[8];
lean_object* v___x_786_ = _args[9];
lean_object* v___x_787_ = _args[10];
lean_object* v___x_788_ = _args[11];
lean_object* v_fst_789_ = _args[12];
lean_object* v_H_790_ = _args[13];
lean_object* v___y_791_ = _args[14];
lean_object* v___y_792_ = _args[15];
lean_object* v___y_793_ = _args[16];
lean_object* v___y_794_ = _args[17];
lean_object* v___y_795_ = _args[18];
lean_object* v___y_796_ = _args[19];
lean_object* v___y_797_ = _args[20];
lean_object* v___y_798_ = _args[21];
lean_object* v___y_799_ = _args[22];
_start:
{
uint8_t v___x_2878__boxed_800_; lean_object* v_res_801_; 
v___x_2878__boxed_800_ = lean_unbox(v___x_779_);
v_res_801_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0(v___x_777_, v_00_u03c3s_778_, v___x_2878__boxed_800_, v_u_780_, v_hyps_781_, v___x_782_, v_target_783_, v___x_784_, v___x_785_, v___x_786_, v___x_787_, v___x_788_, v_fst_789_, v_H_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1(lean_object* v_ty_x3f_802_, lean_object* v___x_803_, lean_object* v___f_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
if (lean_obj_tag(v_ty_x3f_802_) == 1)
{
lean_object* v_val_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_833_; 
v_val_814_ = lean_ctor_get(v_ty_x3f_802_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v_ty_x3f_802_);
if (v_isSharedCheck_833_ == 0)
{
v___x_816_ = v_ty_x3f_802_;
v_isShared_817_ = v_isSharedCheck_833_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_val_814_);
lean_dec(v_ty_x3f_802_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_833_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_803_);
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_803_);
v___x_819_ = v_reuseFailAlloc_832_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
uint8_t v___x_820_; lean_object* v___x_821_; 
v___x_820_ = 0;
v___x_821_ = l_Lean_Elab_Tactic_elabTerm(v_val_814_, v___x_819_, v___x_820_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_823_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_821_, 1);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
lean_inc(v___y_806_);
lean_inc_ref(v___y_805_);
v___x_823_ = lean_apply_10(v___f_804_, v_a_822_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, lean_box(0));
return v___x_823_;
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec_ref(v___f_804_);
v_a_824_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_821_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_821_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
}
else
{
lean_object* v___x_834_; uint8_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec(v_ty_x3f_802_);
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_803_);
v___x_835_ = 0;
v___x_836_ = lean_box(0);
v___x_837_ = l_Lean_Meta_mkFreshExprMVar(v___x_834_, v___x_835_, v___x_836_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_837_, 1);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
lean_inc(v___y_806_);
lean_inc_ref(v___y_805_);
v___x_839_ = lean_apply_10(v___f_804_, v_a_838_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, lean_box(0));
return v___x_839_;
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v___f_804_);
v_a_840_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_837_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_837_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1___boxed(lean_object* v_ty_x3f_848_, lean_object* v___x_849_, lean_object* v___f_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1(v_ty_x3f_848_, v___x_849_, v___f_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave(lean_object* v_x_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_881_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2));
v___x_882_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1));
lean_inc(v_x_871_);
v___x_883_ = l_Lean_Syntax_isOfKind(v_x_871_, v___x_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; 
lean_dec(v_x_871_);
v___x_884_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_884_;
}
else
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v_ty_x3f_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_885_ = lean_unsigned_to_nat(1u);
v___x_886_ = l_Lean_Syntax_getArg(v_x_871_, v___x_885_);
v___x_933_ = lean_unsigned_to_nat(2u);
v___x_934_ = l_Lean_Syntax_getArg(v_x_871_, v___x_933_);
v___x_935_ = l_Lean_Syntax_isNone(v___x_934_);
if (v___x_935_ == 0)
{
uint8_t v___x_936_; 
lean_inc(v___x_934_);
v___x_936_ = l_Lean_Syntax_matchesNull(v___x_934_, v___x_933_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; 
lean_dec(v___x_934_);
lean_dec(v___x_886_);
lean_dec(v_x_871_);
v___x_937_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_937_;
}
else
{
lean_object* v_ty_x3f_938_; lean_object* v___x_939_; 
v_ty_x3f_938_ = l_Lean_Syntax_getArg(v___x_934_, v___x_885_);
lean_dec(v___x_934_);
v___x_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_939_, 0, v_ty_x3f_938_);
v_ty_x3f_888_ = v___x_939_;
v___y_889_ = v_a_872_;
v___y_890_ = v_a_873_;
v___y_891_ = v_a_874_;
v___y_892_ = v_a_875_;
v___y_893_ = v_a_876_;
v___y_894_ = v_a_877_;
v___y_895_ = v_a_878_;
v___y_896_ = v_a_879_;
goto v___jp_887_;
}
}
else
{
lean_object* v___x_940_; 
lean_dec(v___x_934_);
v___x_940_ = lean_box(0);
v_ty_x3f_888_ = v___x_940_;
v___y_889_ = v_a_872_;
v___y_890_ = v_a_873_;
v___y_891_ = v_a_874_;
v___y_892_ = v_a_875_;
v___y_893_ = v_a_876_;
v___y_894_ = v_a_877_;
v___y_895_ = v_a_878_;
v___y_896_ = v_a_879_;
goto v___jp_887_;
}
v___jp_887_:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v_snd_899_; lean_object* v_fst_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_924_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v_snd_899_ = lean_ctor_get(v_a_898_, 1);
v_fst_900_ = lean_ctor_get(v_a_898_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v_a_898_);
if (v_isSharedCheck_924_ == 0)
{
v___x_902_ = v_a_898_;
v_isShared_903_ = v_isSharedCheck_924_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_snd_899_);
lean_inc(v_fst_900_);
lean_dec(v_a_898_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_924_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v_u_904_; lean_object* v_00_u03c3s_905_; lean_object* v_hyps_906_; lean_object* v_target_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_916_; 
v_u_904_ = lean_ctor_get(v_snd_899_, 0);
lean_inc_n(v_u_904_, 2);
v_00_u03c3s_905_ = lean_ctor_get(v_snd_899_, 1);
lean_inc_ref(v_00_u03c3s_905_);
v_hyps_906_ = lean_ctor_get(v_snd_899_, 2);
lean_inc_ref(v_hyps_906_);
v_target_907_ = lean_ctor_get(v_snd_899_, 3);
lean_inc_ref(v_target_907_);
lean_dec(v_snd_899_);
v___x_908_ = lean_unsigned_to_nat(4u);
v___x_909_ = l_Lean_Syntax_getArg(v_x_871_, v___x_908_);
lean_dec(v_x_871_);
v___x_910_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0));
v___x_911_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1));
v___x_912_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2));
v___x_913_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2));
v___x_914_ = lean_box(0);
if (v_isShared_903_ == 0)
{
lean_ctor_set_tag(v___x_902_, 1);
lean_ctor_set(v___x_902_, 1, v___x_914_);
lean_ctor_set(v___x_902_, 0, v_u_904_);
v___x_916_ = v___x_902_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_u_904_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v___x_914_);
v___x_916_ = v_reuseFailAlloc_923_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_917_; lean_object* v___f_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___y_921_; lean_object* v___x_922_; 
v___x_917_ = lean_box(v___x_883_);
lean_inc(v_fst_900_);
lean_inc_ref(v___x_916_);
lean_inc_ref(v_00_u03c3s_905_);
v___f_918_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___boxed), 23, 13);
lean_closure_set(v___f_918_, 0, v___x_886_);
lean_closure_set(v___f_918_, 1, v_00_u03c3s_905_);
lean_closure_set(v___f_918_, 2, v___x_917_);
lean_closure_set(v___f_918_, 3, v_u_904_);
lean_closure_set(v___f_918_, 4, v_hyps_906_);
lean_closure_set(v___f_918_, 5, v___x_909_);
lean_closure_set(v___f_918_, 6, v_target_907_);
lean_closure_set(v___f_918_, 7, v___x_910_);
lean_closure_set(v___f_918_, 8, v___x_911_);
lean_closure_set(v___f_918_, 9, v___x_912_);
lean_closure_set(v___f_918_, 10, v___x_881_);
lean_closure_set(v___f_918_, 11, v___x_916_);
lean_closure_set(v___f_918_, 12, v_fst_900_);
v___x_919_ = l_Lean_mkConst(v___x_913_, v___x_916_);
v___x_920_ = l_Lean_Expr_app___override(v___x_919_, v_00_u03c3s_905_);
v___y_921_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1___boxed), 12, 3);
lean_closure_set(v___y_921_, 0, v_ty_x3f_888_);
lean_closure_set(v___y_921_, 1, v___x_920_);
lean_closure_set(v___y_921_, 2, v___f_918_);
v___x_922_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_900_, v___y_921_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
return v___x_922_;
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v_ty_x3f_888_);
lean_dec(v___x_886_);
lean_dec(v_x_871_);
v_a_925_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_897_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_897_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___boxed(lean_object* v_x_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave(v_x_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1(){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_961_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_962_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1));
v___x_963_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1));
v___x_964_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___boxed), 10, 0);
v___x_965_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_961_, v___x_962_, v___x_963_, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___boxed(lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1();
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0(lean_object* v___x_969_, lean_object* v_u_970_, lean_object* v___x_971_, lean_object* v___x_972_, lean_object* v_00_u03c3s_973_, uint8_t v___x_974_, lean_object* v_hyps_975_, lean_object* v___x_976_, lean_object* v_target_977_, lean_object* v___x_978_, lean_object* v_fst_979_, lean_object* v_ty_x3f_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
if (lean_obj_tag(v___x_969_) == 1)
{
lean_object* v_val_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1106_; 
v_val_990_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_992_ = v___x_969_;
v_isShared_993_ = v_isSharedCheck_1106_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_val_990_);
lean_dec(v___x_969_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1106_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v_focusHyp_994_; lean_object* v_restHyps_995_; lean_object* v_proof_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1105_; 
v_focusHyp_994_ = lean_ctor_get(v_val_990_, 0);
v_restHyps_995_ = lean_ctor_get(v_val_990_, 1);
v_proof_996_ = lean_ctor_get(v_val_990_, 2);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_val_990_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_998_ = v_val_990_;
v_isShared_999_ = v_isSharedCheck_1105_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_proof_996_);
lean_inc(v_restHyps_995_);
lean_inc(v_focusHyp_994_);
lean_dec(v_val_990_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1105_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v_H_x27_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0));
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1));
v___x_1002_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2));
v___x_1003_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2));
v___x_1004_ = lean_box(0);
lean_inc(v_u_970_);
v___x_1005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1005_, 0, v_u_970_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
lean_inc_ref(v___x_1005_);
v___x_1071_ = l_Lean_mkConst(v___x_1003_, v___x_1005_);
lean_inc_ref(v_00_u03c3s_973_);
v___x_1072_ = l_Lean_Expr_app___override(v___x_1071_, v_00_u03c3s_973_);
if (lean_obj_tag(v_ty_x3f_980_) == 1)
{
lean_object* v_val_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1091_; 
v_val_1073_ = lean_ctor_get(v_ty_x3f_980_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_ty_x3f_980_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1075_ = v_ty_x3f_980_;
v_isShared_1076_ = v_isSharedCheck_1091_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_val_1073_);
lean_dec(v_ty_x3f_980_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1091_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1072_);
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1072_);
v___x_1078_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
uint8_t v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = 0;
v___x_1080_ = l_Lean_Elab_Tactic_elabTerm(v_val_1073_, v___x_1078_, v___x_1079_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v_H_x27_1007_ = v_a_1081_;
v___y_1008_ = v___y_981_;
v___y_1009_ = v___y_982_;
v___y_1010_ = v___y_983_;
v___y_1011_ = v___y_984_;
v___y_1012_ = v___y_985_;
v___y_1013_ = v___y_986_;
v___y_1014_ = v___y_987_;
v___y_1015_ = v___y_988_;
goto v___jp_1006_;
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec_ref_known(v___x_1005_, 2);
lean_del_object(v___x_998_);
lean_dec_ref(v_proof_996_);
lean_dec_ref(v_restHyps_995_);
lean_dec_ref(v_focusHyp_994_);
lean_del_object(v___x_992_);
lean_dec(v_fst_979_);
lean_dec_ref(v___x_978_);
lean_dec_ref(v_target_977_);
lean_dec(v___x_976_);
lean_dec_ref(v_hyps_975_);
lean_dec_ref(v_00_u03c3s_973_);
lean_dec(v___x_972_);
lean_dec(v___x_971_);
lean_dec(v_u_970_);
v_a_1082_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1080_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1080_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
}
else
{
lean_object* v___x_1092_; uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_dec(v_ty_x3f_980_);
v___x_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1072_);
v___x_1093_ = 0;
v___x_1094_ = lean_box(0);
v___x_1095_ = l_Lean_Meta_mkFreshExprMVar(v___x_1092_, v___x_1093_, v___x_1094_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v_H_x27_1007_ = v_a_1096_;
v___y_1008_ = v___y_981_;
v___y_1009_ = v___y_982_;
v___y_1010_ = v___y_983_;
v___y_1011_ = v___y_984_;
v___y_1012_ = v___y_985_;
v___y_1013_ = v___y_986_;
v___y_1014_ = v___y_987_;
v___y_1015_ = v___y_988_;
goto v___jp_1006_;
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref_known(v___x_1005_, 2);
lean_del_object(v___x_998_);
lean_dec_ref(v_proof_996_);
lean_dec_ref(v_restHyps_995_);
lean_dec_ref(v_focusHyp_994_);
lean_del_object(v___x_992_);
lean_dec(v_fst_979_);
lean_dec_ref(v___x_978_);
lean_dec_ref(v_target_977_);
lean_dec(v___x_976_);
lean_dec_ref(v_hyps_975_);
lean_dec_ref(v_00_u03c3s_973_);
lean_dec(v___x_972_);
lean_dec(v___x_971_);
lean_dec(v_u_970_);
v_a_1097_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1095_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1095_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
v___jp_1006_:
{
lean_object* v___x_1016_; lean_object* v_a_1017_; lean_object* v___x_1019_; 
v___x_1016_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_1015_);
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref(v___x_1016_);
lean_inc_ref(v_H_x27_1007_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 2, v_H_x27_1007_);
lean_ctor_set(v___x_998_, 1, v_a_1017_);
lean_ctor_set(v___x_998_, 0, v___x_971_);
v___x_1019_ = v___x_998_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_a_1017_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_H_x27_1007_);
v___x_1019_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; 
lean_inc_ref(v___x_1019_);
lean_inc_ref(v_00_u03c3s_973_);
v___x_1020_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v___x_972_, v_00_u03c3s_973_, v___x_1019_, v___x_974_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
lean_dec_ref_known(v___x_1020_, 1);
lean_inc_ref(v_hyps_975_);
lean_inc_ref(v_00_u03c3s_973_);
lean_inc(v_u_970_);
v___x_1021_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1021_, 0, v_u_970_);
lean_ctor_set(v___x_1021_, 1, v_00_u03c3s_973_);
lean_ctor_set(v___x_1021_, 2, v_hyps_975_);
lean_ctor_set(v___x_1021_, 3, v_H_x27_1007_);
v___x_1022_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1021_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_1022_);
v___x_1024_ = v___x_992_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
uint8_t v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = 0;
v___x_1026_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v___x_976_, v___x_1024_, v___x_1025_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v_fst_1030_; lean_object* v_snd_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1060_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1028_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1019_);
lean_inc_ref(v___x_1028_);
lean_inc_ref(v_restHyps_995_);
lean_inc_ref(v_00_u03c3s_973_);
lean_inc(v_u_970_);
v___x_1029_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_970_, v_00_u03c3s_973_, v_restHyps_995_, v___x_1028_);
v_fst_1030_ = lean_ctor_get(v___x_1029_, 0);
v_snd_1031_ = lean_ctor_get(v___x_1029_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1033_ = v___x_1029_;
v_isShared_1034_ = v_isSharedCheck_1060_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_snd_1031_);
lean_inc(v_fst_1030_);
lean_dec(v___x_1029_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1060_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_inc_ref(v_target_977_);
lean_inc(v_fst_1030_);
lean_inc_ref(v_00_u03c3s_973_);
v___x_1035_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1035_, 0, v_u_970_);
lean_ctor_set(v___x_1035_, 1, v_00_u03c3s_973_);
lean_ctor_set(v___x_1035_, 2, v_fst_1030_);
lean_ctor_set(v___x_1035_, 3, v_target_977_);
v___x_1036_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1035_);
v___x_1037_ = lean_box(0);
v___x_1038_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1036_, v___x_1037_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc_n(v_a_1039_, 2);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1040_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3));
v___x_1041_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___closed__0));
v___x_1042_ = l_Lean_Name_mkStr6(v___x_1000_, v___x_1001_, v___x_1002_, v___x_978_, v___x_1040_, v___x_1041_);
v___x_1043_ = l_Lean_mkConst(v___x_1042_, v___x_1005_);
v___x_1044_ = l_Lean_mkApp10(v___x_1043_, v_00_u03c3s_973_, v_restHyps_995_, v_focusHyp_994_, v___x_1028_, v_hyps_975_, v_fst_1030_, v_target_977_, v_proof_996_, v_snd_1031_, v_a_1027_);
v___x_1045_ = l_Lean_Expr_app___override(v___x_1044_, v_a_1039_);
v___x_1046_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_979_, v___x_1045_, v___y_1013_);
lean_dec_ref(v___x_1046_);
v___x_1047_ = l_Lean_Expr_mvarId_x21(v_a_1039_);
lean_dec(v_a_1039_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set_tag(v___x_1033_, 1);
lean_ctor_set(v___x_1033_, 1, v___x_1004_);
lean_ctor_set(v___x_1033_, 0, v___x_1047_);
v___x_1049_ = v___x_1033_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1004_);
v___x_1049_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1049_, v___y_1009_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
return v___x_1050_;
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_del_object(v___x_1033_);
lean_dec(v_snd_1031_);
lean_dec(v_fst_1030_);
lean_dec_ref(v___x_1028_);
lean_dec(v_a_1027_);
lean_dec_ref_known(v___x_1005_, 2);
lean_dec_ref(v_proof_996_);
lean_dec_ref(v_restHyps_995_);
lean_dec_ref(v_focusHyp_994_);
lean_dec(v_fst_979_);
lean_dec_ref(v___x_978_);
lean_dec_ref(v_target_977_);
lean_dec_ref(v_hyps_975_);
lean_dec_ref(v_00_u03c3s_973_);
v_a_1052_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1038_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1038_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec_ref(v___x_1019_);
lean_dec_ref_known(v___x_1005_, 2);
lean_dec_ref(v_proof_996_);
lean_dec_ref(v_restHyps_995_);
lean_dec_ref(v_focusHyp_994_);
lean_dec(v_fst_979_);
lean_dec_ref(v___x_978_);
lean_dec_ref(v_target_977_);
lean_dec_ref(v_hyps_975_);
lean_dec_ref(v_00_u03c3s_973_);
lean_dec(v_u_970_);
v_a_1061_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1026_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1026_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1019_);
lean_dec_ref(v_H_x27_1007_);
lean_dec_ref_known(v___x_1005_, 2);
lean_dec_ref(v_proof_996_);
lean_dec_ref(v_restHyps_995_);
lean_dec_ref(v_focusHyp_994_);
lean_del_object(v___x_992_);
lean_dec(v_fst_979_);
lean_dec_ref(v___x_978_);
lean_dec_ref(v_target_977_);
lean_dec(v___x_976_);
lean_dec_ref(v_hyps_975_);
lean_dec_ref(v_00_u03c3s_973_);
lean_dec(v_u_970_);
return v___x_1020_;
}
}
}
}
}
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec(v_ty_x3f_980_);
lean_dec(v_fst_979_);
lean_dec_ref(v___x_978_);
lean_dec_ref(v_target_977_);
lean_dec(v___x_976_);
lean_dec_ref(v_hyps_975_);
lean_dec_ref(v_00_u03c3s_973_);
lean_dec(v___x_971_);
lean_dec(v_u_970_);
lean_dec(v___x_969_);
v___x_1107_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6);
v___x_1108_ = l_Lean_MessageData_ofSyntax(v___x_972_);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v___x_1111_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___boxed(lean_object** _args){
lean_object* v___x_1113_ = _args[0];
lean_object* v_u_1114_ = _args[1];
lean_object* v___x_1115_ = _args[2];
lean_object* v___x_1116_ = _args[3];
lean_object* v_00_u03c3s_1117_ = _args[4];
lean_object* v___x_1118_ = _args[5];
lean_object* v_hyps_1119_ = _args[6];
lean_object* v___x_1120_ = _args[7];
lean_object* v_target_1121_ = _args[8];
lean_object* v___x_1122_ = _args[9];
lean_object* v_fst_1123_ = _args[10];
lean_object* v_ty_x3f_1124_ = _args[11];
lean_object* v___y_1125_ = _args[12];
lean_object* v___y_1126_ = _args[13];
lean_object* v___y_1127_ = _args[14];
lean_object* v___y_1128_ = _args[15];
lean_object* v___y_1129_ = _args[16];
lean_object* v___y_1130_ = _args[17];
lean_object* v___y_1131_ = _args[18];
lean_object* v___y_1132_ = _args[19];
lean_object* v___y_1133_ = _args[20];
_start:
{
uint8_t v___x_3617__boxed_1134_; lean_object* v_res_1135_; 
v___x_3617__boxed_1134_ = lean_unbox(v___x_1118_);
v_res_1135_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0(v___x_1113_, v_u_1114_, v___x_1115_, v___x_1116_, v_00_u03c3s_1117_, v___x_3617__boxed_1134_, v_hyps_1119_, v___x_1120_, v_target_1121_, v___x_1122_, v_fst_1123_, v_ty_x3f_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace(lean_object* v_x_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1152_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2));
v___x_1153_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1));
lean_inc(v_x_1142_);
v___x_1154_ = l_Lean_Syntax_isOfKind(v_x_1142_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; 
lean_dec(v_x_1142_);
v___x_1155_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_1155_;
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v_ty_x3f_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1156_ = lean_unsigned_to_nat(1u);
v___x_1157_ = l_Lean_Syntax_getArg(v_x_1142_, v___x_1156_);
v___x_1191_ = lean_unsigned_to_nat(2u);
v___x_1192_ = l_Lean_Syntax_getArg(v_x_1142_, v___x_1191_);
v___x_1193_ = l_Lean_Syntax_isNone(v___x_1192_);
if (v___x_1193_ == 0)
{
uint8_t v___x_1194_; 
lean_inc(v___x_1192_);
v___x_1194_ = l_Lean_Syntax_matchesNull(v___x_1192_, v___x_1191_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
lean_dec(v___x_1192_);
lean_dec(v___x_1157_);
lean_dec(v_x_1142_);
v___x_1195_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
return v___x_1195_;
}
else
{
lean_object* v_ty_x3f_1196_; lean_object* v___x_1197_; 
v_ty_x3f_1196_ = l_Lean_Syntax_getArg(v___x_1192_, v___x_1156_);
lean_dec(v___x_1192_);
v___x_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1197_, 0, v_ty_x3f_1196_);
v_ty_x3f_1159_ = v___x_1197_;
v___y_1160_ = v_a_1143_;
v___y_1161_ = v_a_1144_;
v___y_1162_ = v_a_1145_;
v___y_1163_ = v_a_1146_;
v___y_1164_ = v_a_1147_;
v___y_1165_ = v_a_1148_;
v___y_1166_ = v_a_1149_;
v___y_1167_ = v_a_1150_;
goto v___jp_1158_;
}
}
else
{
lean_object* v___x_1198_; 
lean_dec(v___x_1192_);
v___x_1198_ = lean_box(0);
v_ty_x3f_1159_ = v___x_1198_;
v___y_1160_ = v_a_1143_;
v___y_1161_ = v_a_1144_;
v___y_1162_ = v_a_1145_;
v___y_1163_ = v_a_1146_;
v___y_1164_ = v_a_1147_;
v___y_1165_ = v_a_1148_;
v___y_1166_ = v_a_1149_;
v___y_1167_ = v_a_1150_;
goto v___jp_1158_;
}
v___jp_1158_:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v_snd_1170_; lean_object* v_fst_1171_; lean_object* v_u_1172_; lean_object* v_00_u03c3s_1173_; lean_object* v_hyps_1174_; lean_object* v_target_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___y_1181_; lean_object* v___x_1182_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1168_, 1);
v_snd_1170_ = lean_ctor_get(v_a_1169_, 1);
lean_inc(v_snd_1170_);
v_fst_1171_ = lean_ctor_get(v_a_1169_, 0);
lean_inc_n(v_fst_1171_, 2);
lean_dec(v_a_1169_);
v_u_1172_ = lean_ctor_get(v_snd_1170_, 0);
lean_inc(v_u_1172_);
v_00_u03c3s_1173_ = lean_ctor_get(v_snd_1170_, 1);
lean_inc_ref(v_00_u03c3s_1173_);
v_hyps_1174_ = lean_ctor_get(v_snd_1170_, 2);
lean_inc_ref(v_hyps_1174_);
v_target_1175_ = lean_ctor_get(v_snd_1170_, 3);
lean_inc_ref(v_target_1175_);
v___x_1176_ = lean_unsigned_to_nat(4u);
v___x_1177_ = l_Lean_Syntax_getArg(v_x_1142_, v___x_1176_);
lean_dec(v_x_1142_);
v___x_1178_ = l_Lean_Syntax_getId(v___x_1157_);
v___x_1179_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_1170_, v___x_1178_);
v___x_1180_ = lean_box(v___x_1154_);
v___y_1181_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___boxed), 21, 12);
lean_closure_set(v___y_1181_, 0, v___x_1179_);
lean_closure_set(v___y_1181_, 1, v_u_1172_);
lean_closure_set(v___y_1181_, 2, v___x_1178_);
lean_closure_set(v___y_1181_, 3, v___x_1157_);
lean_closure_set(v___y_1181_, 4, v_00_u03c3s_1173_);
lean_closure_set(v___y_1181_, 5, v___x_1180_);
lean_closure_set(v___y_1181_, 6, v_hyps_1174_);
lean_closure_set(v___y_1181_, 7, v___x_1177_);
lean_closure_set(v___y_1181_, 8, v_target_1175_);
lean_closure_set(v___y_1181_, 9, v___x_1152_);
lean_closure_set(v___y_1181_, 10, v_fst_1171_);
lean_closure_set(v___y_1181_, 11, v_ty_x3f_1159_);
v___x_1182_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_1171_, v___y_1181_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
return v___x_1182_;
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec(v_ty_x3f_1159_);
lean_dec(v___x_1157_);
lean_dec(v_x_1142_);
v_a_1183_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1168_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1168_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___boxed(lean_object* v_x_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace(v_x_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1(){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1219_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1220_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1));
v___x_1221_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1));
v___x_1222_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___boxed), 10, 0);
v___x_1223_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1219_, v___x_1220_, v___x_1221_, v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___boxed(lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1();
return v_res_1225_;
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
