// Lean compiler output
// Module: Lean.Elab.Tactic.AsAuxLemma
// Imports: public import Lean.Elab.Tactic.Meta
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_elabAsAuxLemma___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "Cannot abstract term into auxiliary lemma because there are open goals."};
static const lean_object* l_elabAsAuxLemma___lam__0___closed__0 = (const lean_object*)&l_elabAsAuxLemma___lam__0___closed__0_value;
static lean_once_cell_t l_elabAsAuxLemma___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_elabAsAuxLemma___lam__0___closed__1;
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_elabAsAuxLemma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_elabAsAuxLemma___closed__0 = (const lean_object*)&l_elabAsAuxLemma___closed__0_value;
static const lean_string_object l_elabAsAuxLemma___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_elabAsAuxLemma___closed__1 = (const lean_object*)&l_elabAsAuxLemma___closed__1_value;
static const lean_string_object l_elabAsAuxLemma___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_elabAsAuxLemma___closed__2 = (const lean_object*)&l_elabAsAuxLemma___closed__2_value;
static const lean_string_object l_elabAsAuxLemma___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "as_aux_lemma"};
static const lean_object* l_elabAsAuxLemma___closed__3 = (const lean_object*)&l_elabAsAuxLemma___closed__3_value;
static const lean_ctor_object l_elabAsAuxLemma___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_elabAsAuxLemma___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_elabAsAuxLemma___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_elabAsAuxLemma___closed__4_value_aux_0),((lean_object*)&l_elabAsAuxLemma___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_elabAsAuxLemma___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_elabAsAuxLemma___closed__4_value_aux_1),((lean_object*)&l_elabAsAuxLemma___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_elabAsAuxLemma___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_elabAsAuxLemma___closed__4_value_aux_2),((lean_object*)&l_elabAsAuxLemma___closed__3_value),LEAN_SCALAR_PTR_LITERAL(248, 107, 244, 71, 211, 100, 179, 147)}};
static const lean_object* l_elabAsAuxLemma___closed__4 = (const lean_object*)&l_elabAsAuxLemma___closed__4_value;
static const lean_string_object l_elabAsAuxLemma___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Invalid as_aux_lemma syntax"};
static const lean_object* l_elabAsAuxLemma___closed__5 = (const lean_object*)&l_elabAsAuxLemma___closed__5_value;
static lean_once_cell_t l_elabAsAuxLemma___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_elabAsAuxLemma___closed__6;
LEAN_EXPORT lean_object* l_elabAsAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_elabAsAuxLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabAsAuxLemma_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabAsAuxLemma_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabAsAuxLemma"};
static const lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 189, 57, 147, 172, 30, 246, 215)}};
static const lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(v_e_30_, v___y_36_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___boxed(lean_object* v_e_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1(v_e_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_x_52_, lean_object* v_x_53_, lean_object* v_x_54_, lean_object* v_x_55_){
_start:
{
lean_object* v_ks_56_; lean_object* v_vs_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_81_; 
v_ks_56_ = lean_ctor_get(v_x_52_, 0);
v_vs_57_ = lean_ctor_get(v_x_52_, 1);
v_isSharedCheck_81_ = !lean_is_exclusive(v_x_52_);
if (v_isSharedCheck_81_ == 0)
{
v___x_59_ = v_x_52_;
v_isShared_60_ = v_isSharedCheck_81_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_vs_57_);
lean_inc(v_ks_56_);
lean_dec(v_x_52_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_81_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_61_ = lean_array_get_size(v_ks_56_);
v___x_62_ = lean_nat_dec_lt(v_x_53_, v___x_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
lean_dec(v_x_53_);
v___x_63_ = lean_array_push(v_ks_56_, v_x_54_);
v___x_64_ = lean_array_push(v_vs_57_, v_x_55_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 1, v___x_64_);
lean_ctor_set(v___x_59_, 0, v___x_63_);
v___x_66_ = v___x_59_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_63_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v___x_64_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
else
{
lean_object* v_k_x27_68_; uint8_t v___x_69_; 
v_k_x27_68_ = lean_array_fget_borrowed(v_ks_56_, v_x_53_);
v___x_69_ = l_Lean_instBEqMVarId_beq(v_x_54_, v_k_x27_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_71_; 
if (v_isShared_60_ == 0)
{
v___x_71_ = v___x_59_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_ks_56_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_vs_57_);
v___x_71_ = v_reuseFailAlloc_75_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_add(v_x_53_, v___x_72_);
lean_dec(v_x_53_);
v_x_52_ = v___x_71_;
v_x_53_ = v___x_73_;
goto _start;
}
}
else
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_76_ = lean_array_fset(v_ks_56_, v_x_53_, v_x_54_);
v___x_77_ = lean_array_fset(v_vs_57_, v_x_53_, v_x_55_);
lean_dec(v_x_53_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 1, v___x_77_);
lean_ctor_set(v___x_59_, 0, v___x_76_);
v___x_79_ = v___x_59_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_76_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v___x_77_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_n_82_, lean_object* v_k_83_, lean_object* v_v_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_n_82_, v___x_85_, v_k_83_, v_v_84_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(lean_object* v_x_88_, size_t v_x_89_, size_t v_x_90_, lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
if (lean_obj_tag(v_x_88_) == 0)
{
lean_object* v_es_93_; size_t v___x_94_; size_t v___x_95_; lean_object* v_j_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v_es_93_ = lean_ctor_get(v_x_88_, 0);
v___x_94_ = ((size_t)31ULL);
v___x_95_ = lean_usize_land(v_x_89_, v___x_94_);
v_j_96_ = lean_usize_to_nat(v___x_95_);
v___x_97_ = lean_array_get_size(v_es_93_);
v___x_98_ = lean_nat_dec_lt(v_j_96_, v___x_97_);
if (v___x_98_ == 0)
{
lean_dec(v_j_96_);
lean_dec(v_x_92_);
lean_dec(v_x_91_);
return v_x_88_;
}
else
{
lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_137_; 
lean_inc_ref(v_es_93_);
v_isSharedCheck_137_ = !lean_is_exclusive(v_x_88_);
if (v_isSharedCheck_137_ == 0)
{
lean_object* v_unused_138_; 
v_unused_138_ = lean_ctor_get(v_x_88_, 0);
lean_dec(v_unused_138_);
v___x_100_ = v_x_88_;
v_isShared_101_ = v_isSharedCheck_137_;
goto v_resetjp_99_;
}
else
{
lean_dec(v_x_88_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_137_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v_v_102_; lean_object* v___x_103_; lean_object* v_xs_x27_104_; lean_object* v___y_106_; 
v_v_102_ = lean_array_fget(v_es_93_, v_j_96_);
v___x_103_ = lean_box(0);
v_xs_x27_104_ = lean_array_fset(v_es_93_, v_j_96_, v___x_103_);
switch(lean_obj_tag(v_v_102_))
{
case 0:
{
lean_object* v_key_111_; lean_object* v_val_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_122_; 
v_key_111_ = lean_ctor_get(v_v_102_, 0);
v_val_112_ = lean_ctor_get(v_v_102_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v_v_102_);
if (v_isSharedCheck_122_ == 0)
{
v___x_114_ = v_v_102_;
v_isShared_115_ = v_isSharedCheck_122_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_val_112_);
lean_inc(v_key_111_);
lean_dec(v_v_102_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_122_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
uint8_t v___x_116_; 
v___x_116_ = l_Lean_instBEqMVarId_beq(v_x_91_, v_key_111_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_del_object(v___x_114_);
v___x_117_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_111_, v_val_112_, v_x_91_, v_x_92_);
v___x_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
v___y_106_ = v___x_118_;
goto v___jp_105_;
}
else
{
lean_object* v___x_120_; 
lean_dec(v_val_112_);
lean_dec(v_key_111_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 1, v_x_92_);
lean_ctor_set(v___x_114_, 0, v_x_91_);
v___x_120_ = v___x_114_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_x_91_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_x_92_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
v___y_106_ = v___x_120_;
goto v___jp_105_;
}
}
}
}
case 1:
{
lean_object* v_node_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_135_; 
v_node_123_ = lean_ctor_get(v_v_102_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v_v_102_);
if (v_isSharedCheck_135_ == 0)
{
v___x_125_ = v_v_102_;
v_isShared_126_ = v_isSharedCheck_135_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_node_123_);
lean_dec(v_v_102_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_135_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_127_ = ((size_t)5ULL);
v___x_128_ = lean_usize_shift_right(v_x_89_, v___x_127_);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_add(v_x_90_, v___x_129_);
v___x_131_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_node_123_, v___x_128_, v___x_130_, v_x_91_, v_x_92_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_131_);
v___x_133_ = v___x_125_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
v___y_106_ = v___x_133_;
goto v___jp_105_;
}
}
}
default: 
{
lean_object* v___x_136_; 
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v_x_91_);
lean_ctor_set(v___x_136_, 1, v_x_92_);
v___y_106_ = v___x_136_;
goto v___jp_105_;
}
}
v___jp_105_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = lean_array_fset(v_xs_x27_104_, v_j_96_, v___y_106_);
lean_dec(v_j_96_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_107_);
v___x_109_ = v___x_100_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
else
{
lean_object* v_ks_139_; lean_object* v_vs_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_160_; 
v_ks_139_ = lean_ctor_get(v_x_88_, 0);
v_vs_140_ = lean_ctor_get(v_x_88_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_x_88_);
if (v_isSharedCheck_160_ == 0)
{
v___x_142_ = v_x_88_;
v_isShared_143_ = v_isSharedCheck_160_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_vs_140_);
lean_inc(v_ks_139_);
lean_dec(v_x_88_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_160_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_ks_139_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_vs_140_);
v___x_145_ = v_reuseFailAlloc_159_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v_newNode_146_; uint8_t v___y_148_; size_t v___x_154_; uint8_t v___x_155_; 
v_newNode_146_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(v___x_145_, v_x_91_, v_x_92_);
v___x_154_ = ((size_t)7ULL);
v___x_155_ = lean_usize_dec_le(v___x_154_, v_x_90_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_156_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_146_);
v___x_157_ = lean_unsigned_to_nat(4u);
v___x_158_ = lean_nat_dec_lt(v___x_156_, v___x_157_);
lean_dec(v___x_156_);
v___y_148_ = v___x_158_;
goto v___jp_147_;
}
else
{
v___y_148_ = v___x_155_;
goto v___jp_147_;
}
v___jp_147_:
{
if (v___y_148_ == 0)
{
lean_object* v_ks_149_; lean_object* v_vs_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_ks_149_ = lean_ctor_get(v_newNode_146_, 0);
lean_inc_ref(v_ks_149_);
v_vs_150_ = lean_ctor_get(v_newNode_146_, 1);
lean_inc_ref(v_vs_150_);
lean_dec_ref(v_newNode_146_);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_153_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_x_90_, v_ks_149_, v_vs_150_, v___x_151_, v___x_152_);
lean_dec_ref(v_vs_150_);
lean_dec_ref(v_ks_149_);
return v___x_153_;
}
else
{
return v_newNode_146_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(size_t v_depth_161_, lean_object* v_keys_162_, lean_object* v_vals_163_, lean_object* v_i_164_, lean_object* v_entries_165_){
_start:
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = lean_array_get_size(v_keys_162_);
v___x_167_ = lean_nat_dec_lt(v_i_164_, v___x_166_);
if (v___x_167_ == 0)
{
lean_dec(v_i_164_);
return v_entries_165_;
}
else
{
lean_object* v_k_168_; lean_object* v_v_169_; uint64_t v___x_170_; size_t v_h_171_; size_t v___x_172_; lean_object* v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v_h_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_k_168_ = lean_array_fget_borrowed(v_keys_162_, v_i_164_);
v_v_169_ = lean_array_fget_borrowed(v_vals_163_, v_i_164_);
v___x_170_ = l_Lean_instHashableMVarId_hash(v_k_168_);
v_h_171_ = lean_uint64_to_usize(v___x_170_);
v___x_172_ = ((size_t)5ULL);
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = ((size_t)1ULL);
v___x_175_ = lean_usize_sub(v_depth_161_, v___x_174_);
v___x_176_ = lean_usize_mul(v___x_172_, v___x_175_);
v_h_177_ = lean_usize_shift_right(v_h_171_, v___x_176_);
v___x_178_ = lean_nat_add(v_i_164_, v___x_173_);
lean_dec(v_i_164_);
lean_inc(v_v_169_);
lean_inc(v_k_168_);
v___x_179_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_entries_165_, v_h_177_, v_depth_161_, v_k_168_, v_v_169_);
v_i_164_ = v___x_178_;
v_entries_165_ = v___x_179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_depth_181_, lean_object* v_keys_182_, lean_object* v_vals_183_, lean_object* v_i_184_, lean_object* v_entries_185_){
_start:
{
size_t v_depth_boxed_186_; lean_object* v_res_187_; 
v_depth_boxed_186_ = lean_unbox_usize(v_depth_181_);
lean_dec(v_depth_181_);
v_res_187_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_boxed_186_, v_keys_182_, v_vals_183_, v_i_184_, v_entries_185_);
lean_dec_ref(v_vals_183_);
lean_dec_ref(v_keys_182_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
size_t v_x_4578__boxed_193_; size_t v_x_4579__boxed_194_; lean_object* v_res_195_; 
v_x_4578__boxed_193_ = lean_unbox_usize(v_x_189_);
lean_dec(v_x_189_);
v_x_4579__boxed_194_ = lean_unbox_usize(v_x_190_);
lean_dec(v_x_190_);
v_res_195_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_188_, v_x_4578__boxed_193_, v_x_4579__boxed_194_, v_x_191_, v_x_192_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3___redArg(lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
uint64_t v___x_199_; size_t v___x_200_; size_t v___x_201_; lean_object* v___x_202_; 
v___x_199_ = l_Lean_instHashableMVarId_hash(v_x_197_);
v___x_200_ = lean_uint64_to_usize(v___x_199_);
v___x_201_ = ((size_t)1ULL);
v___x_202_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_196_, v___x_200_, v___x_201_, v_x_197_, v_x_198_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(lean_object* v_mvarId_203_, lean_object* v_val_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; lean_object* v_mctx_208_; lean_object* v_cache_209_; lean_object* v_zetaDeltaFVarIds_210_; lean_object* v_postponed_211_; lean_object* v_diag_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_240_; 
v___x_207_ = lean_st_ref_take(v___y_205_);
v_mctx_208_ = lean_ctor_get(v___x_207_, 0);
v_cache_209_ = lean_ctor_get(v___x_207_, 1);
v_zetaDeltaFVarIds_210_ = lean_ctor_get(v___x_207_, 2);
v_postponed_211_ = lean_ctor_get(v___x_207_, 3);
v_diag_212_ = lean_ctor_get(v___x_207_, 4);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_240_ == 0)
{
v___x_214_ = v___x_207_;
v_isShared_215_ = v_isSharedCheck_240_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_diag_212_);
lean_inc(v_postponed_211_);
lean_inc(v_zetaDeltaFVarIds_210_);
lean_inc(v_cache_209_);
lean_inc(v_mctx_208_);
lean_dec(v___x_207_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_240_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v_depth_216_; lean_object* v_levelAssignDepth_217_; lean_object* v_lmvarCounter_218_; lean_object* v_mvarCounter_219_; lean_object* v_lDecls_220_; lean_object* v_decls_221_; lean_object* v_userNames_222_; lean_object* v_lAssignment_223_; lean_object* v_eAssignment_224_; lean_object* v_dAssignment_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_239_; 
v_depth_216_ = lean_ctor_get(v_mctx_208_, 0);
v_levelAssignDepth_217_ = lean_ctor_get(v_mctx_208_, 1);
v_lmvarCounter_218_ = lean_ctor_get(v_mctx_208_, 2);
v_mvarCounter_219_ = lean_ctor_get(v_mctx_208_, 3);
v_lDecls_220_ = lean_ctor_get(v_mctx_208_, 4);
v_decls_221_ = lean_ctor_get(v_mctx_208_, 5);
v_userNames_222_ = lean_ctor_get(v_mctx_208_, 6);
v_lAssignment_223_ = lean_ctor_get(v_mctx_208_, 7);
v_eAssignment_224_ = lean_ctor_get(v_mctx_208_, 8);
v_dAssignment_225_ = lean_ctor_get(v_mctx_208_, 9);
v_isSharedCheck_239_ = !lean_is_exclusive(v_mctx_208_);
if (v_isSharedCheck_239_ == 0)
{
v___x_227_ = v_mctx_208_;
v_isShared_228_ = v_isSharedCheck_239_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_dAssignment_225_);
lean_inc(v_eAssignment_224_);
lean_inc(v_lAssignment_223_);
lean_inc(v_userNames_222_);
lean_inc(v_decls_221_);
lean_inc(v_lDecls_220_);
lean_inc(v_mvarCounter_219_);
lean_inc(v_lmvarCounter_218_);
lean_inc(v_levelAssignDepth_217_);
lean_inc(v_depth_216_);
lean_dec(v_mctx_208_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_239_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3___redArg(v_eAssignment_224_, v_mvarId_203_, v_val_204_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 8, v___x_229_);
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_depth_216_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_levelAssignDepth_217_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_lmvarCounter_218_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_mvarCounter_219_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v_lDecls_220_);
lean_ctor_set(v_reuseFailAlloc_238_, 5, v_decls_221_);
lean_ctor_set(v_reuseFailAlloc_238_, 6, v_userNames_222_);
lean_ctor_set(v_reuseFailAlloc_238_, 7, v_lAssignment_223_);
lean_ctor_set(v_reuseFailAlloc_238_, 8, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_238_, 9, v_dAssignment_225_);
v___x_231_ = v_reuseFailAlloc_238_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_233_; 
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_231_);
v___x_233_ = v___x_214_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_cache_209_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_zetaDeltaFVarIds_210_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v_postponed_211_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v_diag_212_);
v___x_233_ = v_reuseFailAlloc_237_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_st_ref_set(v___y_205_, v___x_233_);
v___x_235_ = lean_box(0);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg___boxed(lean_object* v_mvarId_241_, lean_object* v_val_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(v_mvarId_241_, v_val_242_, v___y_243_);
lean_dec(v___y_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0(lean_object* v_msgData_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___x_252_; lean_object* v_env_253_; lean_object* v___x_254_; lean_object* v_mctx_255_; lean_object* v_lctx_256_; lean_object* v_options_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_252_ = lean_st_ref_get(v___y_250_);
v_env_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc_ref(v_env_253_);
lean_dec(v___x_252_);
v___x_254_ = lean_st_ref_get(v___y_248_);
v_mctx_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc_ref(v_mctx_255_);
lean_dec(v___x_254_);
v_lctx_256_ = lean_ctor_get(v___y_247_, 2);
v_options_257_ = lean_ctor_get(v___y_249_, 2);
lean_inc_ref(v_options_257_);
lean_inc_ref(v_lctx_256_);
v___x_258_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_258_, 0, v_env_253_);
lean_ctor_set(v___x_258_, 1, v_mctx_255_);
lean_ctor_set(v___x_258_, 2, v_lctx_256_);
lean_ctor_set(v___x_258_, 3, v_options_257_);
v___x_259_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v_msgData_246_);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0___boxed(lean_object* v_msgData_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0(v_msgData_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(lean_object* v_msg_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_ref_274_; lean_object* v___x_275_; lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_284_; 
v_ref_274_ = lean_ctor_get(v___y_271_, 5);
v___x_275_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0(v_msg_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_284_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_284_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_284_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
lean_inc(v_ref_274_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v_ref_274_);
lean_ctor_set(v___x_280_, 1, v_a_276_);
if (v_isShared_279_ == 0)
{
lean_ctor_set_tag(v___x_278_, 1);
lean_ctor_set(v___x_278_, 0, v___x_280_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg___boxed(lean_object* v_msg_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(v_msg_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
return v_res_291_;
}
}
static lean_object* _init_l_elabAsAuxLemma___lam__0___closed__1(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l_elabAsAuxLemma___lam__0___closed__0));
v___x_294_ = l_Lean_stringToMessageData(v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lam__0(lean_object* v___x_295_, uint8_t v___x_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_298_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_n(v_a_307_, 2);
lean_dec_ref_known(v___x_306_, 1);
v___x_343_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_343_, 0, v___x_295_);
v___x_344_ = l_Lean_Elab_Tactic_run(v_a_307_, v___x_343_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; uint8_t v___x_346_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_344_, 1);
v___x_346_ = l_List_isEmpty___redArg(v_a_345_);
lean_dec(v_a_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec(v_a_307_);
v___x_347_ = lean_obj_once(&l_elabAsAuxLemma___lam__0___closed__1, &l_elabAsAuxLemma___lam__0___closed__1_once, _init_l_elabAsAuxLemma___lam__0___closed__1);
v___x_348_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(v___x_347_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
return v___x_348_;
}
else
{
v___y_309_ = v___y_297_;
v___y_310_ = v___y_298_;
v___y_311_ = v___y_299_;
v___y_312_ = v___y_300_;
v___y_313_ = v___y_301_;
v___y_314_ = v___y_302_;
v___y_315_ = v___y_303_;
v___y_316_ = v___y_304_;
goto v___jp_308_;
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec(v_a_307_);
v_a_349_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_344_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_344_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
v___jp_308_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_a_319_; lean_object* v___x_320_; 
lean_inc_n(v_a_307_, 2);
v___x_317_ = l_Lean_mkMVar(v_a_307_);
v___x_318_ = l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(v___x_317_, v___y_314_);
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref(v___x_318_);
v___x_320_ = l_Lean_MVarId_getType(v_a_307_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; uint8_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_320_, 1);
v___x_322_ = 0;
v___x_323_ = lean_box(0);
v___x_324_ = l_Lean_Meta_mkAuxTheorem(v_a_321_, v_a_319_, v___x_322_, v___x_323_, v___x_296_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
v___x_326_ = l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(v_a_307_, v_a_325_, v___y_314_);
return v___x_326_;
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec(v_a_307_);
v_a_327_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_324_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_324_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec(v_a_319_);
lean_dec(v_a_307_);
v_a_335_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_320_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_320_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec(v___x_295_);
v_a_357_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_306_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_306_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lam__0___boxed(lean_object* v___x_365_, lean_object* v___x_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
uint8_t v___x_4859__boxed_376_; lean_object* v_res_377_; 
v___x_4859__boxed_376_ = lean_unbox(v___x_366_);
v_res_377_ = l_elabAsAuxLemma___lam__0(v___x_365_, v___x_4859__boxed_376_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_377_;
}
}
static lean_object* _init_l_elabAsAuxLemma___closed__6(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l_elabAsAuxLemma___closed__5));
v___x_389_ = l_Lean_stringToMessageData(v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_elabAsAuxLemma(lean_object* v_x_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = ((lean_object*)(l_elabAsAuxLemma___closed__4));
lean_inc(v_x_390_);
v___x_401_ = l_Lean_Syntax_isOfKind(v_x_390_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec(v_x_390_);
v___x_402_ = lean_obj_once(&l_elabAsAuxLemma___closed__6, &l_elabAsAuxLemma___closed__6_once, _init_l_elabAsAuxLemma___closed__6);
v___x_403_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(v___x_402_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
return v___x_403_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___f_407_; lean_object* v___x_408_; 
v___x_404_ = lean_unsigned_to_nat(2u);
v___x_405_ = l_Lean_Syntax_getArg(v_x_390_, v___x_404_);
lean_dec(v_x_390_);
v___x_406_ = lean_box(v___x_401_);
v___f_407_ = lean_alloc_closure((void*)(l_elabAsAuxLemma___lam__0___boxed), 11, 2);
lean_closure_set(v___f_407_, 0, v___x_405_);
lean_closure_set(v___f_407_, 1, v___x_406_);
v___x_408_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_407_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_elabAsAuxLemma___boxed(lean_object* v_x_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_elabAsAuxLemma(v_x_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabAsAuxLemma_spec__0(lean_object* v_00_u03b1_420_, lean_object* v_msg_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(v_msg_421_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabAsAuxLemma_spec__0___boxed(lean_object* v_00_u03b1_432_, lean_object* v_msg_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0(v_00_u03b1_432_, v_msg_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2(lean_object* v_mvarId_444_, lean_object* v_val_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(v_mvarId_444_, v_val_445_, v___y_451_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___boxed(lean_object* v_mvarId_456_, lean_object* v_val_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2(v_mvarId_456_, v_val_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3(lean_object* v_00_u03b2_468_, lean_object* v_x_469_, lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3___redArg(v_x_469_, v_x_470_, v_x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_473_, lean_object* v_x_474_, size_t v_x_475_, size_t v_x_476_, lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_474_, v_x_475_, v_x_476_, v_x_477_, v_x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
size_t v_x_5142__boxed_486_; size_t v_x_5143__boxed_487_; lean_object* v_res_488_; 
v_x_5142__boxed_486_ = lean_unbox_usize(v_x_482_);
lean_dec(v_x_482_);
v_x_5143__boxed_487_ = lean_unbox_usize(v_x_483_);
lean_dec(v_x_483_);
v_res_488_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4(v_00_u03b2_480_, v_x_481_, v_x_5142__boxed_486_, v_x_5143__boxed_487_, v_x_484_, v_x_485_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_489_, lean_object* v_n_490_, lean_object* v_k_491_, lean_object* v_v_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(v_n_490_, v_k_491_, v_v_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_494_, size_t v_depth_495_, lean_object* v_keys_496_, lean_object* v_vals_497_, lean_object* v_heq_498_, lean_object* v_i_499_, lean_object* v_entries_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_495_, v_keys_496_, v_vals_497_, v_i_499_, v_entries_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_502_, lean_object* v_depth_503_, lean_object* v_keys_504_, lean_object* v_vals_505_, lean_object* v_heq_506_, lean_object* v_i_507_, lean_object* v_entries_508_){
_start:
{
size_t v_depth_boxed_509_; lean_object* v_res_510_; 
v_depth_boxed_509_ = lean_unbox_usize(v_depth_503_);
lean_dec(v_depth_503_);
v_res_510_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_502_, v_depth_boxed_509_, v_keys_504_, v_vals_505_, v_heq_506_, v_i_507_, v_entries_508_);
lean_dec_ref(v_vals_505_);
lean_dec_ref(v_keys_504_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_511_, lean_object* v_x_512_, lean_object* v_x_513_, lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_x_512_, v_x_513_, v_x_514_, v_x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1(){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_521_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_522_ = ((lean_object*)(l_elabAsAuxLemma___closed__4));
v___x_523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__1));
v___x_524_ = lean_alloc_closure((void*)(l_elabAsAuxLemma___boxed), 10, 0);
v___x_525_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_521_, v___x_522_, v___x_523_, v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___boxed(lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1();
return v_res_527_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_AsAuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_AsAuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_AsAuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
}
#ifdef __cplusplus
}
#endif
