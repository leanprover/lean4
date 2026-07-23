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
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0;
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
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabMClear"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(92, 83, 226, 112, 28, 79, 201, 237)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___boxed(lean_object*);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(lean_object* v_x_199_, size_t v_x_200_, size_t v_x_201_, lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
if (lean_obj_tag(v_x_199_) == 0)
{
lean_object* v_es_204_; size_t v___x_205_; size_t v___x_206_; lean_object* v_j_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_es_204_ = lean_ctor_get(v_x_199_, 0);
v___x_205_ = ((size_t)31ULL);
v___x_206_ = lean_usize_land(v_x_200_, v___x_205_);
v_j_207_ = lean_usize_to_nat(v___x_206_);
v___x_208_ = lean_array_get_size(v_es_204_);
v___x_209_ = lean_nat_dec_lt(v_j_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_dec(v_j_207_);
lean_dec(v_x_203_);
lean_dec(v_x_202_);
return v_x_199_;
}
else
{
lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_248_; 
lean_inc_ref(v_es_204_);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; 
v_unused_249_ = lean_ctor_get(v_x_199_, 0);
lean_dec(v_unused_249_);
v___x_211_ = v_x_199_;
v_isShared_212_ = v_isSharedCheck_248_;
goto v_resetjp_210_;
}
else
{
lean_dec(v_x_199_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_248_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v_v_213_; lean_object* v___x_214_; lean_object* v_xs_x27_215_; lean_object* v___y_217_; 
v_v_213_ = lean_array_fget(v_es_204_, v_j_207_);
v___x_214_ = lean_box(0);
v_xs_x27_215_ = lean_array_fset(v_es_204_, v_j_207_, v___x_214_);
switch(lean_obj_tag(v_v_213_))
{
case 0:
{
lean_object* v_key_222_; lean_object* v_val_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_233_; 
v_key_222_ = lean_ctor_get(v_v_213_, 0);
v_val_223_ = lean_ctor_get(v_v_213_, 1);
v_isSharedCheck_233_ = !lean_is_exclusive(v_v_213_);
if (v_isSharedCheck_233_ == 0)
{
v___x_225_ = v_v_213_;
v_isShared_226_ = v_isSharedCheck_233_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_val_223_);
lean_inc(v_key_222_);
lean_dec(v_v_213_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_233_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
uint8_t v___x_227_; 
v___x_227_ = l_Lean_instBEqMVarId_beq(v_x_202_, v_key_222_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_del_object(v___x_225_);
v___x_228_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_222_, v_val_223_, v_x_202_, v_x_203_);
v___x_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
v___y_217_ = v___x_229_;
goto v___jp_216_;
}
else
{
lean_object* v___x_231_; 
lean_dec(v_val_223_);
lean_dec(v_key_222_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v_x_203_);
lean_ctor_set(v___x_225_, 0, v_x_202_);
v___x_231_ = v___x_225_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_x_202_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_x_203_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
v___y_217_ = v___x_231_;
goto v___jp_216_;
}
}
}
}
case 1:
{
lean_object* v_node_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_246_; 
v_node_234_ = lean_ctor_get(v_v_213_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v_v_213_);
if (v_isSharedCheck_246_ == 0)
{
v___x_236_ = v_v_213_;
v_isShared_237_ = v_isSharedCheck_246_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_node_234_);
lean_dec(v_v_213_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_246_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
size_t v___x_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_238_ = ((size_t)5ULL);
v___x_239_ = lean_usize_shift_right(v_x_200_, v___x_238_);
v___x_240_ = ((size_t)1ULL);
v___x_241_ = lean_usize_add(v_x_201_, v___x_240_);
v___x_242_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_node_234_, v___x_239_, v___x_241_, v_x_202_, v_x_203_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_242_);
v___x_244_ = v___x_236_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
v___y_217_ = v___x_244_;
goto v___jp_216_;
}
}
}
default: 
{
lean_object* v___x_247_; 
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v_x_202_);
lean_ctor_set(v___x_247_, 1, v_x_203_);
v___y_217_ = v___x_247_;
goto v___jp_216_;
}
}
v___jp_216_:
{
lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_218_ = lean_array_fset(v_xs_x27_215_, v_j_207_, v___y_217_);
lean_dec(v_j_207_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_218_);
v___x_220_ = v___x_211_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
else
{
lean_object* v_ks_250_; lean_object* v_vs_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_271_; 
v_ks_250_ = lean_ctor_get(v_x_199_, 0);
v_vs_251_ = lean_ctor_get(v_x_199_, 1);
v_isSharedCheck_271_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_271_ == 0)
{
v___x_253_ = v_x_199_;
v_isShared_254_ = v_isSharedCheck_271_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_vs_251_);
lean_inc(v_ks_250_);
lean_dec(v_x_199_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_271_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_ks_250_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_vs_251_);
v___x_256_ = v_reuseFailAlloc_270_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v_newNode_257_; uint8_t v___y_259_; size_t v___x_265_; uint8_t v___x_266_; 
v_newNode_257_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7___redArg(v___x_256_, v_x_202_, v_x_203_);
v___x_265_ = ((size_t)7ULL);
v___x_266_ = lean_usize_dec_le(v___x_265_, v_x_201_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_267_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_257_);
v___x_268_ = lean_unsigned_to_nat(4u);
v___x_269_ = lean_nat_dec_lt(v___x_267_, v___x_268_);
lean_dec(v___x_267_);
v___y_259_ = v___x_269_;
goto v___jp_258_;
}
else
{
v___y_259_ = v___x_266_;
goto v___jp_258_;
}
v___jp_258_:
{
if (v___y_259_ == 0)
{
lean_object* v_ks_260_; lean_object* v_vs_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_ks_260_ = lean_ctor_get(v_newNode_257_, 0);
lean_inc_ref(v_ks_260_);
v_vs_261_ = lean_ctor_get(v_newNode_257_, 1);
lean_inc_ref(v_vs_261_);
lean_dec_ref(v_newNode_257_);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_264_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(v_x_201_, v_ks_260_, v_vs_261_, v___x_262_, v___x_263_);
lean_dec_ref(v_vs_261_);
lean_dec_ref(v_ks_260_);
return v___x_264_;
}
else
{
return v_newNode_257_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(size_t v_depth_272_, lean_object* v_keys_273_, lean_object* v_vals_274_, lean_object* v_i_275_, lean_object* v_entries_276_){
_start:
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = lean_array_get_size(v_keys_273_);
v___x_278_ = lean_nat_dec_lt(v_i_275_, v___x_277_);
if (v___x_278_ == 0)
{
lean_dec(v_i_275_);
return v_entries_276_;
}
else
{
lean_object* v_k_279_; lean_object* v_v_280_; uint64_t v___x_281_; size_t v_h_282_; size_t v___x_283_; lean_object* v___x_284_; size_t v___x_285_; size_t v___x_286_; size_t v___x_287_; size_t v_h_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_k_279_ = lean_array_fget_borrowed(v_keys_273_, v_i_275_);
v_v_280_ = lean_array_fget_borrowed(v_vals_274_, v_i_275_);
v___x_281_ = l_Lean_instHashableMVarId_hash(v_k_279_);
v_h_282_ = lean_uint64_to_usize(v___x_281_);
v___x_283_ = ((size_t)5ULL);
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = ((size_t)1ULL);
v___x_286_ = lean_usize_sub(v_depth_272_, v___x_285_);
v___x_287_ = lean_usize_mul(v___x_283_, v___x_286_);
v_h_288_ = lean_usize_shift_right(v_h_282_, v___x_287_);
v___x_289_ = lean_nat_add(v_i_275_, v___x_284_);
lean_dec(v_i_275_);
lean_inc(v_v_280_);
lean_inc(v_k_279_);
v___x_290_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_entries_276_, v_h_288_, v_depth_272_, v_k_279_, v_v_280_);
v_i_275_ = v___x_289_;
v_entries_276_ = v___x_290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_292_, lean_object* v_keys_293_, lean_object* v_vals_294_, lean_object* v_i_295_, lean_object* v_entries_296_){
_start:
{
size_t v_depth_boxed_297_; lean_object* v_res_298_; 
v_depth_boxed_297_ = lean_unbox_usize(v_depth_292_);
lean_dec(v_depth_292_);
v_res_298_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_boxed_297_, v_keys_293_, v_vals_294_, v_i_295_, v_entries_296_);
lean_dec_ref(v_vals_294_);
lean_dec_ref(v_keys_293_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_299_, lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
size_t v_x_7033__boxed_304_; size_t v_x_7034__boxed_305_; lean_object* v_res_306_; 
v_x_7033__boxed_304_ = lean_unbox_usize(v_x_300_);
lean_dec(v_x_300_);
v_x_7034__boxed_305_ = lean_unbox_usize(v_x_301_);
lean_dec(v_x_301_);
v_res_306_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_x_299_, v_x_7033__boxed_304_, v_x_7034__boxed_305_, v_x_302_, v_x_303_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2___redArg(lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
uint64_t v___x_310_; size_t v___x_311_; size_t v___x_312_; lean_object* v___x_313_; 
v___x_310_ = l_Lean_instHashableMVarId_hash(v_x_308_);
v___x_311_ = lean_uint64_to_usize(v___x_310_);
v___x_312_ = ((size_t)1ULL);
v___x_313_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_x_307_, v___x_311_, v___x_312_, v_x_308_, v_x_309_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(lean_object* v_mvarId_314_, lean_object* v_val_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___x_318_; lean_object* v_mctx_319_; lean_object* v_cache_320_; lean_object* v_zetaDeltaFVarIds_321_; lean_object* v_postponed_322_; lean_object* v_diag_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_351_; 
v___x_318_ = lean_st_ref_take(v___y_316_);
v_mctx_319_ = lean_ctor_get(v___x_318_, 0);
v_cache_320_ = lean_ctor_get(v___x_318_, 1);
v_zetaDeltaFVarIds_321_ = lean_ctor_get(v___x_318_, 2);
v_postponed_322_ = lean_ctor_get(v___x_318_, 3);
v_diag_323_ = lean_ctor_get(v___x_318_, 4);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_351_ == 0)
{
v___x_325_ = v___x_318_;
v_isShared_326_ = v_isSharedCheck_351_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_diag_323_);
lean_inc(v_postponed_322_);
lean_inc(v_zetaDeltaFVarIds_321_);
lean_inc(v_cache_320_);
lean_inc(v_mctx_319_);
lean_dec(v___x_318_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_351_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v_depth_327_; lean_object* v_levelAssignDepth_328_; lean_object* v_lmvarCounter_329_; lean_object* v_mvarCounter_330_; lean_object* v_lDecls_331_; lean_object* v_decls_332_; lean_object* v_userNames_333_; lean_object* v_lAssignment_334_; lean_object* v_eAssignment_335_; lean_object* v_dAssignment_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_350_; 
v_depth_327_ = lean_ctor_get(v_mctx_319_, 0);
v_levelAssignDepth_328_ = lean_ctor_get(v_mctx_319_, 1);
v_lmvarCounter_329_ = lean_ctor_get(v_mctx_319_, 2);
v_mvarCounter_330_ = lean_ctor_get(v_mctx_319_, 3);
v_lDecls_331_ = lean_ctor_get(v_mctx_319_, 4);
v_decls_332_ = lean_ctor_get(v_mctx_319_, 5);
v_userNames_333_ = lean_ctor_get(v_mctx_319_, 6);
v_lAssignment_334_ = lean_ctor_get(v_mctx_319_, 7);
v_eAssignment_335_ = lean_ctor_get(v_mctx_319_, 8);
v_dAssignment_336_ = lean_ctor_get(v_mctx_319_, 9);
v_isSharedCheck_350_ = !lean_is_exclusive(v_mctx_319_);
if (v_isSharedCheck_350_ == 0)
{
v___x_338_ = v_mctx_319_;
v_isShared_339_ = v_isSharedCheck_350_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_dAssignment_336_);
lean_inc(v_eAssignment_335_);
lean_inc(v_lAssignment_334_);
lean_inc(v_userNames_333_);
lean_inc(v_decls_332_);
lean_inc(v_lDecls_331_);
lean_inc(v_mvarCounter_330_);
lean_inc(v_lmvarCounter_329_);
lean_inc(v_levelAssignDepth_328_);
lean_inc(v_depth_327_);
lean_dec(v_mctx_319_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_350_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2___redArg(v_eAssignment_335_, v_mvarId_314_, v_val_315_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 8, v___x_340_);
v___x_342_ = v___x_338_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_depth_327_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_levelAssignDepth_328_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v_lmvarCounter_329_);
lean_ctor_set(v_reuseFailAlloc_349_, 3, v_mvarCounter_330_);
lean_ctor_set(v_reuseFailAlloc_349_, 4, v_lDecls_331_);
lean_ctor_set(v_reuseFailAlloc_349_, 5, v_decls_332_);
lean_ctor_set(v_reuseFailAlloc_349_, 6, v_userNames_333_);
lean_ctor_set(v_reuseFailAlloc_349_, 7, v_lAssignment_334_);
lean_ctor_set(v_reuseFailAlloc_349_, 8, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_349_, 9, v_dAssignment_336_);
v___x_342_ = v_reuseFailAlloc_349_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_344_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v___x_342_);
v___x_344_ = v___x_325_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_cache_320_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v_zetaDeltaFVarIds_321_);
lean_ctor_set(v_reuseFailAlloc_348_, 3, v_postponed_322_);
lean_ctor_set(v_reuseFailAlloc_348_, 4, v_diag_323_);
v___x_344_ = v_reuseFailAlloc_348_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_st_ref_set(v___y_316_, v___x_344_);
v___x_346_ = lean_box(0);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg___boxed(lean_object* v_mvarId_352_, lean_object* v_val_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(v_mvarId_352_, v_val_353_, v___y_354_);
lean_dec(v___y_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4(lean_object* v_msgData_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; lean_object* v_env_364_; lean_object* v___x_365_; lean_object* v_mctx_366_; lean_object* v_lctx_367_; lean_object* v_options_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_363_ = lean_st_ref_get(v___y_361_);
v_env_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc_ref(v_env_364_);
lean_dec(v___x_363_);
v___x_365_ = lean_st_ref_get(v___y_359_);
v_mctx_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc_ref(v_mctx_366_);
lean_dec(v___x_365_);
v_lctx_367_ = lean_ctor_get(v___y_358_, 2);
v_options_368_ = lean_ctor_get(v___y_360_, 2);
lean_inc_ref(v_options_368_);
lean_inc_ref(v_lctx_367_);
v___x_369_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_369_, 0, v_env_364_);
lean_ctor_set(v___x_369_, 1, v_mctx_366_);
lean_ctor_set(v___x_369_, 2, v_lctx_367_);
lean_ctor_set(v___x_369_, 3, v_options_368_);
v___x_370_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v_msgData_357_);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4___boxed(lean_object* v_msgData_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4(v_msgData_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(lean_object* v_msg_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_ref_385_; lean_object* v___x_386_; lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_395_; 
v_ref_385_ = lean_ctor_get(v___y_382_, 5);
v___x_386_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4(v_msg_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_395_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_395_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_395_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_393_; 
lean_inc(v_ref_385_);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v_ref_385_);
lean_ctor_set(v___x_391_, 1, v_a_387_);
if (v_isShared_390_ == 0)
{
lean_ctor_set_tag(v___x_389_, 1);
lean_ctor_set(v___x_389_, 0, v___x_391_);
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg___boxed(lean_object* v_msg_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(v_msg_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
return v_res_402_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__5));
v___x_410_ = l_Lean_stringToMessageData(v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0(lean_object* v_a_411_, lean_object* v_hyp_412_, lean_object* v___x_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___x_423_; 
lean_inc(v_a_411_);
v___x_423_ = l_Lean_MVarId_getType(v_a_411_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_425_; lean_object* v_a_426_; lean_object* v___x_427_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_423_, 1);
v___x_425_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg(v_a_424_, v___y_419_);
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref(v___x_425_);
v___x_427_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_426_);
lean_dec(v_a_426_);
if (lean_obj_tag(v___x_427_) == 1)
{
lean_object* v_val_428_; lean_object* v___x_429_; 
v_val_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc_n(v_val_428_, 2);
lean_dec_ref_known(v___x_427_, 1);
v___x_429_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_val_428_, v_hyp_412_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref_known(v___x_429_, 1);
lean_inc(v_val_428_);
v___x_431_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal(v_a_430_, v_val_428_);
v___x_432_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_431_);
v___x_433_ = lean_box(0);
v___x_434_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_432_, v___x_433_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v_u_436_; lean_object* v_00_u03c3s_437_; lean_object* v_hyps_438_; lean_object* v_target_439_; lean_object* v_focusHyp_440_; lean_object* v_restHyps_441_; lean_object* v_proof_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc_n(v_a_435_, 2);
lean_dec_ref_known(v___x_434_, 1);
v_u_436_ = lean_ctor_get(v_val_428_, 0);
lean_inc(v_u_436_);
v_00_u03c3s_437_ = lean_ctor_get(v_val_428_, 1);
lean_inc_ref(v_00_u03c3s_437_);
v_hyps_438_ = lean_ctor_get(v_val_428_, 2);
lean_inc_ref(v_hyps_438_);
v_target_439_ = lean_ctor_get(v_val_428_, 3);
lean_inc_ref(v_target_439_);
lean_dec(v_val_428_);
v_focusHyp_440_ = lean_ctor_get(v_a_430_, 0);
lean_inc_ref(v_focusHyp_440_);
v_restHyps_441_ = lean_ctor_get(v_a_430_, 1);
lean_inc_ref(v_restHyps_441_);
v_proof_442_ = lean_ctor_get(v_a_430_, 2);
lean_inc_ref(v_proof_442_);
lean_dec(v_a_430_);
v___x_443_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__0));
v___x_444_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1));
v___x_445_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__2));
v___x_446_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__3));
v___x_447_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__4));
v___x_448_ = l_Lean_Name_mkStr6(v___x_443_, v___x_444_, v___x_445_, v___x_413_, v___x_446_, v___x_447_);
v___x_449_ = lean_box(0);
v___x_450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_450_, 0, v_u_436_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = l_Lean_mkConst(v___x_448_, v___x_450_);
v___x_452_ = l_Lean_mkApp7(v___x_451_, v_00_u03c3s_437_, v_hyps_438_, v_restHyps_441_, v_focusHyp_440_, v_target_439_, v_proof_442_, v_a_435_);
v___x_453_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(v_a_411_, v___x_452_, v___y_419_);
lean_dec_ref(v___x_453_);
v___x_454_ = l_Lean_Expr_mvarId_x21(v_a_435_);
lean_dec(v_a_435_);
v___x_455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___x_449_);
v___x_456_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_455_, v___y_415_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
return v___x_456_;
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec(v_a_430_);
lean_dec(v_val_428_);
lean_dec_ref(v___x_413_);
lean_dec(v_a_411_);
v_a_457_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_434_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_434_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec(v_val_428_);
lean_dec_ref(v___x_413_);
lean_dec(v_a_411_);
v_a_465_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_429_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_429_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec(v___x_427_);
lean_dec_ref(v___x_413_);
lean_dec(v_hyp_412_);
lean_dec(v_a_411_);
v___x_473_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6);
v___x_474_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(v___x_473_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
return v___x_474_;
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec_ref(v___x_413_);
lean_dec(v_hyp_412_);
lean_dec(v_a_411_);
v_a_475_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_423_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_423_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___boxed(lean_object* v_a_483_, lean_object* v_hyp_484_, lean_object* v___x_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0(v_a_483_, v_hyp_484_, v___x_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear(lean_object* v_x_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_518_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2));
v___x_519_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4));
lean_inc(v_x_508_);
v___x_520_ = l_Lean_Syntax_isOfKind(v_x_508_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
lean_dec(v_x_508_);
v___x_521_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg();
return v___x_521_;
}
else
{
lean_object* v___x_522_; lean_object* v_hyp_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v_hyp_523_ = l_Lean_Syntax_getArg(v_x_508_, v___x_522_);
lean_dec(v_x_508_);
v___x_524_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__6));
lean_inc(v_hyp_523_);
v___x_525_ = l_Lean_Syntax_isOfKind(v_hyp_523_, v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; 
lean_dec(v_hyp_523_);
v___x_526_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg();
return v___x_526_;
}
else
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_510_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___f_529_; lean_object* v___x_530_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc_n(v_a_528_, 2);
lean_dec_ref_known(v___x_527_, 1);
v___f_529_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___boxed), 12, 3);
lean_closure_set(v___f_529_, 0, v_a_528_);
lean_closure_set(v___f_529_, 1, v_hyp_523_);
lean_closure_set(v___f_529_, 2, v___x_518_);
v___x_530_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg(v_a_528_, v___f_529_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
return v___x_530_;
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_hyp_523_);
v_a_531_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_527_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_527_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___boxed(lean_object* v_x_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear(v_x_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2(lean_object* v_mvarId_550_, lean_object* v_val_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(v_mvarId_550_, v_val_551_, v___y_557_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___boxed(lean_object* v_mvarId_562_, lean_object* v_val_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2(v_mvarId_562_, v_val_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3(lean_object* v_00_u03b1_574_, lean_object* v_msg_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(v_msg_575_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___boxed(lean_object* v_00_u03b1_586_, lean_object* v_msg_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3(v_00_u03b1_586_, v_msg_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2(lean_object* v_00_u03b2_598_, lean_object* v_x_599_, lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2___redArg(v_x_599_, v_x_600_, v_x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_603_, lean_object* v_x_604_, size_t v_x_605_, size_t v_x_606_, lean_object* v_x_607_, lean_object* v_x_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_x_604_, v_x_605_, v_x_606_, v_x_607_, v_x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_610_, lean_object* v_x_611_, lean_object* v_x_612_, lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
size_t v_x_7622__boxed_616_; size_t v_x_7623__boxed_617_; lean_object* v_res_618_; 
v_x_7622__boxed_616_ = lean_unbox_usize(v_x_612_);
lean_dec(v_x_612_);
v_x_7623__boxed_617_ = lean_unbox_usize(v_x_613_);
lean_dec(v_x_613_);
v_res_618_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4(v_00_u03b2_610_, v_x_611_, v_x_7622__boxed_616_, v_x_7623__boxed_617_, v_x_614_, v_x_615_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_619_, lean_object* v_n_620_, lean_object* v_k_621_, lean_object* v_v_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7___redArg(v_n_620_, v_k_621_, v_v_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_624_, size_t v_depth_625_, lean_object* v_keys_626_, lean_object* v_vals_627_, lean_object* v_heq_628_, lean_object* v_i_629_, lean_object* v_entries_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_625_, v_keys_626_, v_vals_627_, v_i_629_, v_entries_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_632_, lean_object* v_depth_633_, lean_object* v_keys_634_, lean_object* v_vals_635_, lean_object* v_heq_636_, lean_object* v_i_637_, lean_object* v_entries_638_){
_start:
{
size_t v_depth_boxed_639_; lean_object* v_res_640_; 
v_depth_boxed_639_ = lean_unbox_usize(v_depth_633_);
lean_dec(v_depth_633_);
v_res_640_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_632_, v_depth_boxed_639_, v_keys_634_, v_vals_635_, v_heq_636_, v_i_637_, v_entries_638_);
lean_dec_ref(v_vals_635_);
lean_dec_ref(v_keys_634_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_641_, lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_642_, v_x_643_, v_x_644_, v_x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1(){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_658_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_659_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4));
v___x_660_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3));
v___x_661_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___boxed), 10, 0);
v___x_662_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_658_, v___x_659_, v___x_660_, v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___boxed(lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1();
return v_res_664_;
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
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1();
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
