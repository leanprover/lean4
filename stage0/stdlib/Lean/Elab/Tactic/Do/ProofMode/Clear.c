// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Clear
// Imports: public import Std.Tactic.Do.Syntax public import Lean.Elab.Tactic.Do.ProofMode.Focus
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Clear"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clear"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "not in proof mode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mclear"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__3_value),LEAN_SCALAR_PTR_LITERAL(107, 161, 32, 25, 224, 212, 229, 174)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabMClear"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(92, 83, 226, 112, 28, 79, 201, 237)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0(void){
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___boxed(lean_object* v_00_u03b1_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0(v_00_u03b1_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg(lean_object* v_e_31_, lean_object* v___y_32_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = l_Lean_Expr_hasMVar(v_e_31_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; 
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v_e_31_);
return v___x_35_;
}
else
{
lean_object* v___x_36_; lean_object* v_mctx_37_; lean_object* v___x_38_; lean_object* v_fst_39_; lean_object* v_snd_40_; lean_object* v___x_41_; lean_object* v_cache_42_; lean_object* v_zetaDeltaFVarIds_43_; lean_object* v_postponed_44_; lean_object* v_diag_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_54_; 
v___x_36_ = lean_st_ref_get(v___y_32_);
v_mctx_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc_ref(v_mctx_37_);
lean_dec(v___x_36_);
v___x_38_ = l_Lean_instantiateMVarsCore(v_mctx_37_, v_e_31_);
v_fst_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_fst_39_);
v_snd_40_ = lean_ctor_get(v___x_38_, 1);
lean_inc(v_snd_40_);
lean_dec_ref(v___x_38_);
v___x_41_ = lean_st_ref_take(v___y_32_);
v_cache_42_ = lean_ctor_get(v___x_41_, 1);
v_zetaDeltaFVarIds_43_ = lean_ctor_get(v___x_41_, 2);
v_postponed_44_ = lean_ctor_get(v___x_41_, 3);
v_diag_45_ = lean_ctor_get(v___x_41_, 4);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_54_ == 0)
{
lean_object* v_unused_55_; 
v_unused_55_ = lean_ctor_get(v___x_41_, 0);
lean_dec(v_unused_55_);
v___x_47_ = v___x_41_;
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_diag_45_);
lean_inc(v_postponed_44_);
lean_inc(v_zetaDeltaFVarIds_43_);
lean_inc(v_cache_42_);
lean_dec(v___x_41_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 0, v_snd_40_);
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_snd_40_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_cache_42_);
lean_ctor_set(v_reuseFailAlloc_53_, 2, v_zetaDeltaFVarIds_43_);
lean_ctor_set(v_reuseFailAlloc_53_, 3, v_postponed_44_);
lean_ctor_set(v_reuseFailAlloc_53_, 4, v_diag_45_);
v___x_50_ = v_reuseFailAlloc_53_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_st_ref_set(v___y_32_, v___x_50_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v_fst_39_);
return v___x_52_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg___boxed(lean_object* v_e_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg(v_e_56_, v___y_57_);
lean_dec(v___y_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1(lean_object* v_e_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg(v_e_60_, v___y_66_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___boxed(lean_object* v_e_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1(v_e_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___lam__0(lean_object* v_x_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_92_; 
lean_inc(v___y_86_);
lean_inc_ref(v___y_85_);
lean_inc(v___y_84_);
lean_inc_ref(v___y_83_);
v___x_92_ = lean_apply_9(v_x_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, lean_box(0));
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___lam__0___boxed(lean_object* v_x_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___lam__0(v_x_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg(lean_object* v_mvarId_104_, lean_object* v_x_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___f_115_; lean_object* v___x_116_; 
lean_inc(v___y_109_);
lean_inc_ref(v___y_108_);
lean_inc(v___y_107_);
lean_inc_ref(v___y_106_);
v___f_115_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_115_, 0, v_x_105_);
lean_closure_set(v___f_115_, 1, v___y_106_);
lean_closure_set(v___f_115_, 2, v___y_107_);
lean_closure_set(v___f_115_, 3, v___y_108_);
lean_closure_set(v___f_115_, 4, v___y_109_);
v___x_116_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_104_, v___f_115_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
if (lean_obj_tag(v___x_116_) == 0)
{
return v___x_116_;
}
else
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_124_ == 0)
{
v___x_119_ = v___x_116_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_117_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___boxed(lean_object* v_mvarId_125_, lean_object* v_x_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg(v_mvarId_125_, v_x_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4(lean_object* v_00_u03b1_137_, lean_object* v_mvarId_138_, lean_object* v_x_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg(v_mvarId_138_, v_x_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___boxed(lean_object* v_00_u03b1_150_, lean_object* v_mvarId_151_, lean_object* v_x_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4(v_00_u03b1_150_, v_mvarId_151_, v_x_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v_x_166_){
_start:
{
lean_object* v_ks_167_; lean_object* v_vs_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_192_; 
v_ks_167_ = lean_ctor_get(v_x_163_, 0);
v_vs_168_ = lean_ctor_get(v_x_163_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_x_163_);
if (v_isSharedCheck_192_ == 0)
{
v___x_170_ = v_x_163_;
v_isShared_171_ = v_isSharedCheck_192_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_vs_168_);
lean_inc(v_ks_167_);
lean_dec(v_x_163_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_192_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_array_get_size(v_ks_167_);
v___x_173_ = lean_nat_dec_lt(v_x_164_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
lean_dec(v_x_164_);
v___x_174_ = lean_array_push(v_ks_167_, v_x_165_);
v___x_175_ = lean_array_push(v_vs_168_, v_x_166_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v___x_175_);
lean_ctor_set(v___x_170_, 0, v___x_174_);
v___x_177_ = v___x_170_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
else
{
lean_object* v_k_x27_179_; uint8_t v___x_180_; 
v_k_x27_179_ = lean_array_fget_borrowed(v_ks_167_, v_x_164_);
v___x_180_ = l_Lean_instBEqMVarId_beq(v_x_165_, v_k_x27_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_182_; 
if (v_isShared_171_ == 0)
{
v___x_182_ = v___x_170_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_ks_167_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_vs_168_);
v___x_182_ = v_reuseFailAlloc_186_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_add(v_x_164_, v___x_183_);
lean_dec(v_x_164_);
v_x_163_ = v___x_182_;
v_x_164_ = v___x_184_;
goto _start;
}
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_187_ = lean_array_fset(v_ks_167_, v_x_164_, v_x_165_);
v___x_188_ = lean_array_fset(v_vs_168_, v_x_164_, v_x_166_);
lean_dec(v_x_164_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v___x_188_);
lean_ctor_set(v___x_170_, 0, v___x_187_);
v___x_190_ = v___x_170_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7___redArg(lean_object* v_n_193_, lean_object* v_k_194_, lean_object* v_v_195_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_n_193_, v___x_196_, v_k_194_, v_v_195_);
return v___x_197_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; 
v___x_198_ = ((size_t)5ULL);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_shift_left(v___x_199_, v___x_198_);
return v___x_200_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_201_; size_t v___x_202_; size_t v___x_203_; 
v___x_201_ = ((size_t)1ULL);
v___x_202_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_203_ = lean_usize_sub(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(lean_object* v_x_205_, size_t v_x_206_, size_t v_x_207_, lean_object* v_x_208_, lean_object* v_x_209_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
lean_object* v_es_210_; size_t v___x_211_; size_t v___x_212_; size_t v___x_213_; size_t v___x_214_; lean_object* v_j_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_es_210_ = lean_ctor_get(v_x_205_, 0);
v___x_211_ = ((size_t)5ULL);
v___x_212_ = ((size_t)1ULL);
v___x_213_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1);
v___x_214_ = lean_usize_land(v_x_206_, v___x_213_);
v_j_215_ = lean_usize_to_nat(v___x_214_);
v___x_216_ = lean_array_get_size(v_es_210_);
v___x_217_ = lean_nat_dec_lt(v_j_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_dec(v_j_215_);
lean_dec(v_x_209_);
lean_dec(v_x_208_);
return v_x_205_;
}
else
{
lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_254_; 
lean_inc_ref(v_es_210_);
v_isSharedCheck_254_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_254_ == 0)
{
lean_object* v_unused_255_; 
v_unused_255_ = lean_ctor_get(v_x_205_, 0);
lean_dec(v_unused_255_);
v___x_219_ = v_x_205_;
v_isShared_220_ = v_isSharedCheck_254_;
goto v_resetjp_218_;
}
else
{
lean_dec(v_x_205_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_254_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_v_221_; lean_object* v___x_222_; lean_object* v_xs_x27_223_; lean_object* v___y_225_; 
v_v_221_ = lean_array_fget(v_es_210_, v_j_215_);
v___x_222_ = lean_box(0);
v_xs_x27_223_ = lean_array_fset(v_es_210_, v_j_215_, v___x_222_);
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
v___x_235_ = l_Lean_instBEqMVarId_beq(v_x_208_, v_key_230_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_del_object(v___x_233_);
v___x_236_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_230_, v_val_231_, v_x_208_, v_x_209_);
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
lean_ctor_set(v___x_233_, 1, v_x_209_);
lean_ctor_set(v___x_233_, 0, v_x_208_);
v___x_239_ = v___x_233_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_x_208_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_x_209_);
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
lean_object* v_node_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_252_; 
v_node_242_ = lean_ctor_get(v_v_221_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v_v_221_);
if (v_isSharedCheck_252_ == 0)
{
v___x_244_ = v_v_221_;
v_isShared_245_ = v_isSharedCheck_252_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_node_242_);
lean_dec(v_v_221_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_252_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
size_t v___x_246_; size_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_246_ = lean_usize_shift_right(v_x_206_, v___x_211_);
v___x_247_ = lean_usize_add(v_x_207_, v___x_212_);
v___x_248_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_node_242_, v___x_246_, v___x_247_, v_x_208_, v_x_209_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_248_);
v___x_250_ = v___x_244_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
v___y_225_ = v___x_250_;
goto v___jp_224_;
}
}
}
default: 
{
lean_object* v___x_253_; 
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v_x_208_);
lean_ctor_set(v___x_253_, 1, v_x_209_);
v___y_225_ = v___x_253_;
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
lean_object* v_ks_256_; lean_object* v_vs_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_277_; 
v_ks_256_ = lean_ctor_get(v_x_205_, 0);
v_vs_257_ = lean_ctor_get(v_x_205_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_277_ == 0)
{
v___x_259_ = v_x_205_;
v_isShared_260_ = v_isSharedCheck_277_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_vs_257_);
lean_inc(v_ks_256_);
lean_dec(v_x_205_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_277_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_ks_256_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_vs_257_);
v___x_262_ = v_reuseFailAlloc_276_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v_newNode_263_; uint8_t v___y_265_; size_t v___x_271_; uint8_t v___x_272_; 
v_newNode_263_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7___redArg(v___x_262_, v_x_208_, v_x_209_);
v___x_271_ = ((size_t)7ULL);
v___x_272_ = lean_usize_dec_le(v___x_271_, v_x_207_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_273_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_263_);
v___x_274_ = lean_unsigned_to_nat(4u);
v___x_275_ = lean_nat_dec_lt(v___x_273_, v___x_274_);
lean_dec(v___x_273_);
v___y_265_ = v___x_275_;
goto v___jp_264_;
}
else
{
v___y_265_ = v___x_272_;
goto v___jp_264_;
}
v___jp_264_:
{
if (v___y_265_ == 0)
{
lean_object* v_ks_266_; lean_object* v_vs_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_ks_266_ = lean_ctor_get(v_newNode_263_, 0);
lean_inc_ref(v_ks_266_);
v_vs_267_ = lean_ctor_get(v_newNode_263_, 1);
lean_inc_ref(v_vs_267_);
lean_dec_ref(v_newNode_263_);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2);
v___x_270_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(v_x_207_, v_ks_266_, v_vs_267_, v___x_268_, v___x_269_);
lean_dec_ref(v_vs_267_);
lean_dec_ref(v_ks_266_);
return v___x_270_;
}
else
{
return v_newNode_263_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(size_t v_depth_278_, lean_object* v_keys_279_, lean_object* v_vals_280_, lean_object* v_i_281_, lean_object* v_entries_282_){
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
v___x_296_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_entries_282_, v_h_294_, v_depth_278_, v_k_285_, v_v_286_);
v_i_281_ = v___x_295_;
v_entries_282_ = v___x_296_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_298_, lean_object* v_keys_299_, lean_object* v_vals_300_, lean_object* v_i_301_, lean_object* v_entries_302_){
_start:
{
size_t v_depth_boxed_303_; lean_object* v_res_304_; 
v_depth_boxed_303_ = lean_unbox_usize(v_depth_298_);
lean_dec(v_depth_298_);
v_res_304_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_boxed_303_, v_keys_299_, v_vals_300_, v_i_301_, v_entries_302_);
lean_dec_ref(v_vals_300_);
lean_dec_ref(v_keys_299_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
size_t v_x_7042__boxed_310_; size_t v_x_7043__boxed_311_; lean_object* v_res_312_; 
v_x_7042__boxed_310_ = lean_unbox_usize(v_x_306_);
lean_dec(v_x_306_);
v_x_7043__boxed_311_ = lean_unbox_usize(v_x_307_);
lean_dec(v_x_307_);
v_res_312_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_x_305_, v_x_7042__boxed_310_, v_x_7043__boxed_311_, v_x_308_, v_x_309_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2___redArg(lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
uint64_t v___x_316_; size_t v___x_317_; size_t v___x_318_; lean_object* v___x_319_; 
v___x_316_ = l_Lean_instHashableMVarId_hash(v_x_314_);
v___x_317_ = lean_uint64_to_usize(v___x_316_);
v___x_318_ = ((size_t)1ULL);
v___x_319_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_x_313_, v___x_317_, v___x_318_, v_x_314_, v_x_315_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(lean_object* v_mvarId_320_, lean_object* v_val_321_, lean_object* v___y_322_){
_start:
{
lean_object* v___x_324_; lean_object* v_mctx_325_; lean_object* v_cache_326_; lean_object* v_zetaDeltaFVarIds_327_; lean_object* v_postponed_328_; lean_object* v_diag_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_356_; 
v___x_324_ = lean_st_ref_take(v___y_322_);
v_mctx_325_ = lean_ctor_get(v___x_324_, 0);
v_cache_326_ = lean_ctor_get(v___x_324_, 1);
v_zetaDeltaFVarIds_327_ = lean_ctor_get(v___x_324_, 2);
v_postponed_328_ = lean_ctor_get(v___x_324_, 3);
v_diag_329_ = lean_ctor_get(v___x_324_, 4);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_356_ == 0)
{
v___x_331_ = v___x_324_;
v_isShared_332_ = v_isSharedCheck_356_;
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
v_isShared_332_ = v_isSharedCheck_356_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v_depth_333_; lean_object* v_levelAssignDepth_334_; lean_object* v_mvarCounter_335_; lean_object* v_lDepth_336_; lean_object* v_decls_337_; lean_object* v_userNames_338_; lean_object* v_lAssignment_339_; lean_object* v_eAssignment_340_; lean_object* v_dAssignment_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_355_; 
v_depth_333_ = lean_ctor_get(v_mctx_325_, 0);
v_levelAssignDepth_334_ = lean_ctor_get(v_mctx_325_, 1);
v_mvarCounter_335_ = lean_ctor_get(v_mctx_325_, 2);
v_lDepth_336_ = lean_ctor_get(v_mctx_325_, 3);
v_decls_337_ = lean_ctor_get(v_mctx_325_, 4);
v_userNames_338_ = lean_ctor_get(v_mctx_325_, 5);
v_lAssignment_339_ = lean_ctor_get(v_mctx_325_, 6);
v_eAssignment_340_ = lean_ctor_get(v_mctx_325_, 7);
v_dAssignment_341_ = lean_ctor_get(v_mctx_325_, 8);
v_isSharedCheck_355_ = !lean_is_exclusive(v_mctx_325_);
if (v_isSharedCheck_355_ == 0)
{
v___x_343_ = v_mctx_325_;
v_isShared_344_ = v_isSharedCheck_355_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_dAssignment_341_);
lean_inc(v_eAssignment_340_);
lean_inc(v_lAssignment_339_);
lean_inc(v_userNames_338_);
lean_inc(v_decls_337_);
lean_inc(v_lDepth_336_);
lean_inc(v_mvarCounter_335_);
lean_inc(v_levelAssignDepth_334_);
lean_inc(v_depth_333_);
lean_dec(v_mctx_325_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_355_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_345_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2___redArg(v_eAssignment_340_, v_mvarId_320_, v_val_321_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 7, v___x_345_);
v___x_347_ = v___x_343_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_depth_333_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_levelAssignDepth_334_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_mvarCounter_335_);
lean_ctor_set(v_reuseFailAlloc_354_, 3, v_lDepth_336_);
lean_ctor_set(v_reuseFailAlloc_354_, 4, v_decls_337_);
lean_ctor_set(v_reuseFailAlloc_354_, 5, v_userNames_338_);
lean_ctor_set(v_reuseFailAlloc_354_, 6, v_lAssignment_339_);
lean_ctor_set(v_reuseFailAlloc_354_, 7, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_354_, 8, v_dAssignment_341_);
v___x_347_ = v_reuseFailAlloc_354_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_349_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_347_);
v___x_349_ = v___x_331_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_cache_326_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v_zetaDeltaFVarIds_327_);
lean_ctor_set(v_reuseFailAlloc_353_, 3, v_postponed_328_);
lean_ctor_set(v_reuseFailAlloc_353_, 4, v_diag_329_);
v___x_349_ = v_reuseFailAlloc_353_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_st_ref_set(v___y_322_, v___x_349_);
v___x_351_ = lean_box(0);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg___boxed(lean_object* v_mvarId_357_, lean_object* v_val_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(v_mvarId_357_, v_val_358_, v___y_359_);
lean_dec(v___y_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4(lean_object* v_msgData_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v___x_368_; lean_object* v_env_369_; lean_object* v___x_370_; lean_object* v_mctx_371_; lean_object* v_lctx_372_; lean_object* v_options_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_368_ = lean_st_ref_get(v___y_366_);
v_env_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc_ref(v_env_369_);
lean_dec(v___x_368_);
v___x_370_ = lean_st_ref_get(v___y_364_);
v_mctx_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc_ref(v_mctx_371_);
lean_dec(v___x_370_);
v_lctx_372_ = lean_ctor_get(v___y_363_, 2);
v_options_373_ = lean_ctor_get(v___y_365_, 2);
lean_inc_ref(v_options_373_);
lean_inc_ref(v_lctx_372_);
v___x_374_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_374_, 0, v_env_369_);
lean_ctor_set(v___x_374_, 1, v_mctx_371_);
lean_ctor_set(v___x_374_, 2, v_lctx_372_);
lean_ctor_set(v___x_374_, 3, v_options_373_);
v___x_375_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v_msgData_362_);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4___boxed(lean_object* v_msgData_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4(v_msgData_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(lean_object* v_msg_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_ref_390_; lean_object* v___x_391_; lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_400_; 
v_ref_390_ = lean_ctor_get(v___y_387_, 5);
v___x_391_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4(v_msg_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_400_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
lean_inc(v_ref_390_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v_ref_390_);
lean_ctor_set(v___x_396_, 1, v_a_392_);
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 1);
lean_ctor_set(v___x_394_, 0, v___x_396_);
v___x_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg___boxed(lean_object* v_msg_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(v_msg_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_407_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__5));
v___x_415_ = l_Lean_stringToMessageData(v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0(lean_object* v_a_416_, lean_object* v_hyp_417_, lean_object* v___x_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_428_; 
lean_inc(v_a_416_);
v___x_428_ = l_Lean_MVarId_getType(v_a_416_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_430_; lean_object* v_a_431_; lean_object* v___x_432_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref(v___x_428_);
v___x_430_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg(v_a_429_, v___y_424_);
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref(v___x_430_);
v___x_432_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_431_);
lean_dec(v_a_431_);
if (lean_obj_tag(v___x_432_) == 1)
{
lean_object* v_val_433_; lean_object* v___x_434_; 
v_val_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc_n(v_val_433_, 2);
lean_dec_ref(v___x_432_);
v___x_434_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_val_433_, v_hyp_417_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref(v___x_434_);
lean_inc(v_val_433_);
v___x_436_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal(v_a_435_, v_val_433_);
v___x_437_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_436_);
v___x_438_ = lean_box(0);
v___x_439_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_437_, v___x_438_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v_u_441_; lean_object* v_00_u03c3s_442_; lean_object* v_hyps_443_; lean_object* v_target_444_; lean_object* v_focusHyp_445_; lean_object* v_restHyps_446_; lean_object* v_proof_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc_n(v_a_440_, 2);
lean_dec_ref(v___x_439_);
v_u_441_ = lean_ctor_get(v_val_433_, 0);
lean_inc(v_u_441_);
v_00_u03c3s_442_ = lean_ctor_get(v_val_433_, 1);
lean_inc_ref(v_00_u03c3s_442_);
v_hyps_443_ = lean_ctor_get(v_val_433_, 2);
lean_inc_ref(v_hyps_443_);
v_target_444_ = lean_ctor_get(v_val_433_, 3);
lean_inc_ref(v_target_444_);
lean_dec(v_val_433_);
v_focusHyp_445_ = lean_ctor_get(v_a_435_, 0);
lean_inc_ref(v_focusHyp_445_);
v_restHyps_446_ = lean_ctor_get(v_a_435_, 1);
lean_inc_ref(v_restHyps_446_);
v_proof_447_ = lean_ctor_get(v_a_435_, 2);
lean_inc_ref(v_proof_447_);
lean_dec(v_a_435_);
v___x_448_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__0));
v___x_449_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1));
v___x_450_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__2));
v___x_451_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__3));
v___x_452_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__4));
v___x_453_ = l_Lean_Name_mkStr6(v___x_448_, v___x_449_, v___x_450_, v___x_418_, v___x_451_, v___x_452_);
v___x_454_ = lean_box(0);
v___x_455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_455_, 0, v_u_441_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = l_Lean_mkConst(v___x_453_, v___x_455_);
v___x_457_ = l_Lean_mkApp7(v___x_456_, v_00_u03c3s_442_, v_hyps_443_, v_restHyps_446_, v_focusHyp_445_, v_target_444_, v_proof_447_, v_a_440_);
v___x_458_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(v_a_416_, v___x_457_, v___y_424_);
lean_dec_ref(v___x_458_);
v___x_459_ = l_Lean_Expr_mvarId_x21(v_a_440_);
lean_dec(v_a_440_);
v___x_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___x_454_);
v___x_461_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_460_, v___y_420_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
return v___x_461_;
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec(v_a_435_);
lean_dec(v_val_433_);
lean_dec_ref(v___x_418_);
lean_dec(v_a_416_);
v_a_462_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_439_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_439_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_dec(v_val_433_);
lean_dec_ref(v___x_418_);
lean_dec(v_a_416_);
v_a_470_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_434_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_434_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v___x_432_);
lean_dec_ref(v___x_418_);
lean_dec(v_hyp_417_);
lean_dec(v_a_416_);
v___x_478_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6);
v___x_479_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(v___x_478_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
return v___x_479_;
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec_ref(v___x_418_);
lean_dec(v_hyp_417_);
lean_dec(v_a_416_);
v_a_480_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_428_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_428_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___boxed(lean_object* v_a_488_, lean_object* v_hyp_489_, lean_object* v___x_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0(v_a_488_, v_hyp_489_, v___x_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear(lean_object* v_x_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_523_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2));
v___x_524_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4));
lean_inc(v_x_513_);
v___x_525_ = l_Lean_Syntax_isOfKind(v_x_513_, v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; 
lean_dec(v_x_513_);
v___x_526_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg();
return v___x_526_;
}
else
{
lean_object* v___x_527_; lean_object* v_hyp_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_527_ = lean_unsigned_to_nat(1u);
v_hyp_528_ = l_Lean_Syntax_getArg(v_x_513_, v___x_527_);
lean_dec(v_x_513_);
v___x_529_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__6));
lean_inc(v_hyp_528_);
v___x_530_ = l_Lean_Syntax_isOfKind(v_hyp_528_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; 
lean_dec(v_hyp_528_);
v___x_531_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg();
return v___x_531_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_515_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___f_534_; lean_object* v___x_535_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc_n(v_a_533_, 2);
lean_dec_ref(v___x_532_);
v___f_534_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___boxed), 12, 3);
lean_closure_set(v___f_534_, 0, v_a_533_);
lean_closure_set(v___f_534_, 1, v_hyp_528_);
lean_closure_set(v___f_534_, 2, v___x_523_);
v___x_535_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg(v_a_533_, v___f_534_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
return v___x_535_;
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec(v_hyp_528_);
v_a_536_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_532_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_532_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___boxed(lean_object* v_x_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear(v_x_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2(lean_object* v_mvarId_555_, lean_object* v_val_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(v_mvarId_555_, v_val_556_, v___y_562_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___boxed(lean_object* v_mvarId_567_, lean_object* v_val_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2(v_mvarId_567_, v_val_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3(lean_object* v_00_u03b1_579_, lean_object* v_msg_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(v_msg_580_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___boxed(lean_object* v_00_u03b1_591_, lean_object* v_msg_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3(v_00_u03b1_591_, v_msg_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2(lean_object* v_00_u03b2_603_, lean_object* v_x_604_, lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2___redArg(v_x_604_, v_x_605_, v_x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_608_, lean_object* v_x_609_, size_t v_x_610_, size_t v_x_611_, lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_x_609_, v_x_610_, v_x_611_, v_x_612_, v_x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_615_, lean_object* v_x_616_, lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v_x_619_, lean_object* v_x_620_){
_start:
{
size_t v_x_7637__boxed_621_; size_t v_x_7638__boxed_622_; lean_object* v_res_623_; 
v_x_7637__boxed_621_ = lean_unbox_usize(v_x_617_);
lean_dec(v_x_617_);
v_x_7638__boxed_622_ = lean_unbox_usize(v_x_618_);
lean_dec(v_x_618_);
v_res_623_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4(v_00_u03b2_615_, v_x_616_, v_x_7637__boxed_621_, v_x_7638__boxed_622_, v_x_619_, v_x_620_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_624_, lean_object* v_n_625_, lean_object* v_k_626_, lean_object* v_v_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7___redArg(v_n_625_, v_k_626_, v_v_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_629_, size_t v_depth_630_, lean_object* v_keys_631_, lean_object* v_vals_632_, lean_object* v_heq_633_, lean_object* v_i_634_, lean_object* v_entries_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_630_, v_keys_631_, v_vals_632_, v_i_634_, v_entries_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_637_, lean_object* v_depth_638_, lean_object* v_keys_639_, lean_object* v_vals_640_, lean_object* v_heq_641_, lean_object* v_i_642_, lean_object* v_entries_643_){
_start:
{
size_t v_depth_boxed_644_; lean_object* v_res_645_; 
v_depth_boxed_644_ = lean_unbox_usize(v_depth_638_);
lean_dec(v_depth_638_);
v_res_645_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_637_, v_depth_boxed_644_, v_keys_639_, v_vals_640_, v_heq_641_, v_i_642_, v_entries_643_);
lean_dec_ref(v_vals_640_);
lean_dec_ref(v_keys_639_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_646_, lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_647_, v_x_648_, v_x_649_, v_x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1(){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_663_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_664_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4));
v___x_665_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3));
v___x_666_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___boxed), 10, 0);
v___x_667_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_663_, v___x_664_, v___x_665_, v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___boxed(lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1();
return v_res_669_;
}
}
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(builtin);
}
#ifdef __cplusplus
}
#endif
